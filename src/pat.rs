use std::collections::VecDeque;

use crate::syntax::{Expr, Ident};

#[derive(Debug, Clone)]
pub struct Branches(pub VecDeque<Branch>);

#[derive(Debug, Clone)]
pub struct Branch(pub VecDeque<Pattern>, pub Expr);

#[derive(Debug, Clone)]
pub enum Pattern {
    Var(Ident),
    Pair(Box<Pattern>, Box<Pattern>),
    Inj1(Box<Pattern>),
    Inj2(Box<Pattern>),
    Nil,
    Cons(Box<Pattern>, Box<Pattern>),
    Wildcard,
    Unit,
}

impl Branches {
    fn new() -> Self {
        Self(VecDeque::new())
    }

    pub fn from_iter(branches: impl IntoIterator<Item = Branch>) -> Self {
        Self(VecDeque::from_iter(branches))
    }

    /// Π guarded, `self` contains a list pattern constructor in head position.
    pub fn guarded(&self) -> bool {
        self.0
            .iter()
            .any(|Branch(ps, _)| matches!(ps.front(), Some(Pattern::Nil | Pattern::Cons(_, _))))
    }

    /// Π ~>Vec Π[] || Π::, expand vector patterns in `self`.
    pub fn expand_vec_pats(self) -> Result<(Self, Self), String> {
        self.0.into_iter().try_fold(
            (Self::new(), Self::new()),
            |(mut nils, mut conses), Branch(mut ps, e)| match ps.pop_front() {
                Some(Pattern::Nil) => {
                    nils.0.push_front(Branch(ps, e));

                    Ok((nils, conses))
                }
                Some(Pattern::Cons(hd, tl)) => {
                    ps.push_front(*tl);
                    ps.push_front(*hd);
                    conses.0.push_front(Branch(ps, e));

                    Ok((nils, conses))
                }
                None => Ok((nils, conses)),
                Some(Pattern::Var(_) | Pattern::Wildcard) => {
                    nils.0.push_front(Branch(ps.clone(), e.clone()));
                    ps.push_front(Pattern::Wildcard);
                    ps.push_front(Pattern::Wildcard);
                    conses.0.push_front(Branch(ps, e));

                    Ok((nils, conses))
                }
                Some(pat) => Err(format!(
                    "Invalid pattern:\nExpected patterns that match vec type but got {pat:?}."
                )),
            },
        )
    }

    /// Π ~>× Π', expand head pair patterns in `self`.
    pub fn expand_pair_pats(mut self) -> Result<Self, String> {
        for Branch(ps, _) in &mut self.0 {
            match ps.pop_front() {
                Some(Pattern::Pair(p1, p2)) => {
                    ps.push_front(*p2);
                    ps.push_front(*p1);
                }
                Some(Pattern::Var(_) | Pattern::Wildcard) => {
                    ps.push_front(Pattern::Wildcard);
                    ps.push_front(Pattern::Wildcard);
                }
                None => {}
                Some(pat) => {
                    return Err(format!(
                        "Invalid pattern:\nExpected patterns that match product type but got {pat:?}."
                    ));
                }
            }
        }

        Ok(self)
    }

    /// Π ~>+ Πₗ || Πᵣ, expand head sum patterns in `self` into L and R sets.
    pub fn expand_sum_pats(self) -> Result<(Self, Self), String> {
        self.0.into_iter().try_fold(
            (Self::new(), Self::new()),
            |(mut l, mut r), Branch(mut ps, e)| match ps.pop_front() {
                Some(Pattern::Inj1(p)) => {
                    ps.push_front(*p);
                    l.0.push_front(Branch(ps, e));

                    Ok((l, r))
                }
                Some(Pattern::Inj2(p)) => {
                    ps.push_front(*p);
                    r.0.push_front(Branch(ps, e));

                    Ok((l, r))
                }
                Some(Pattern::Var(_) | Pattern::Wildcard) => {
                    ps.push_front(Pattern::Wildcard);
                    l.0.push_front(Branch(ps.clone(), e.clone()));
                    r.0.push_front(Branch(ps, e));

                    Ok((l, r))
                }
                None => Ok((l, r)),
                Some(pat) => Err(format!(
                    "Invalid pattern:\nExpected patterns that match sum type but got {pat:?}."
                )),
            },
        )
    }

    /// Π ~>1 Π', remove head variable, wildcard, and unit patterns patterns from `self`.
    pub fn expand_unit_pats(mut self) -> Result<Self, String> {
        for Branch(ps, _) in &mut self.0 {
            match ps.pop_front() {
                Some(Pattern::Var(_) | Pattern::Wildcard | Pattern::Unit) => {}
                None => {}
                Some(pat) => {
                    return Err(format!(
                        "Invalid pattern:\nExpected patterns that match unit type but got {pat:?}."
                    ));
                }
            }
        }

        Ok(self)
    }

    /// Π ~>var Π', remove head variable and wildcard patterns from `self`.
    pub fn expand_var_pats(mut self) -> Self {
        for Branch(ps, _) in &mut self.0 {
            match ps.pop_front() {
                Some(Pattern::Var(_) | Pattern::Wildcard) => {}
                None => {}
                _ => panic!("all other patterns should be checked before this one"),
            }
        }

        self
    }
}

impl Branch {
    pub fn from_iter(patterns: impl IntoIterator<Item = Pattern>, expr: Expr) -> Self {
        Self(VecDeque::from_iter(patterns), expr)
    }
}

impl Pattern {
    pub fn pair(e1: Self, e2: Self) -> Self {
        Self::Pair(Box::new(e1), Box::new(e2))
    }

    pub fn inj1(expr: Self) -> Self {
        Self::Inj1(Box::new(expr))
    }

    pub fn inj2(expr: Self) -> Self {
        Self::Inj2(Box::new(expr))
    }

    pub fn cons(hd: Self, tl: Self) -> Self {
        Self::Cons(Box::new(hd), Box::new(tl))
    }
}
