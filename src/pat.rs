use std::collections::VecDeque;

use crate::syntax::{Expr, Ident};

#[derive(Debug, Clone)]
pub struct Branches(VecDeque<Branch>);

#[derive(Debug, Clone)]
struct Branch(VecDeque<Pattern>, Expr);

#[derive(Debug, Clone)]
enum Pattern {
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

    /// Π ~>Vec Π[] || Π::, expand vector patterns in `self`
    fn expand_vec_pats(self) -> (Self, Self) {
        self.0.into_iter().fold(
            (Self::new(), Self::new()),
            |(mut nils, mut conses), Branch(mut ps, e)| {
                match ps.pop_front() {
                    Some(Pattern::Nil) => nils.0.push_front(Branch(ps, e)),
                    Some(Pattern::Cons(hd, tl)) => {
                        ps.push_front(*tl);
                        ps.push_front(*hd);
                        conses.0.push_front(Branch(ps, e));
                    }
                    None => {}
                    _ => panic!("unexpected pattern when expanding vec patterns"),
                }

                (nils, conses)
            },
        )
    }

    /// Π ~>× Π', expand head pair patterns in `self`
    fn expand_pair_pats(mut self) -> Self {
        for Branch(ps, _) in self.0.iter_mut() {
            match ps.pop_front() {
                Some(Pattern::Pair(p1, p2)) => {
                    ps.push_front(*p2);
                    ps.push_front(*p1);
                }
                Some(Pattern::Var(_)) | Some(Pattern::Wildcard) => {
                    ps.push_front(Pattern::Wildcard);
                    ps.push_front(Pattern::Wildcard);
                }
                None => {}
                _ => panic!("unexpected pattern when expanding pair patterns"),
            }
        }

        self
    }

    /// Π ~>+ Πₗ || Πᵣ, expand head sum patterns in `self` into L and R sets
    fn expand_sum_pats(self) -> (Self, Self) {
        self.0.into_iter().fold(
            (Self::new(), Self::new()),
            |(mut l, mut r), Branch(mut ps, e)| {
                match ps.pop_front() {
                    Some(Pattern::Inj1(p)) => {
                        ps.push_front(*p);
                        l.0.push_front(Branch(ps, e));
                    }
                    Some(Pattern::Inj2(p)) => {
                        ps.push_front(*p);
                        r.0.push_front(Branch(ps, e));
                    }
                    Some(Pattern::Var(_)) | Some(Pattern::Wildcard) => {
                        ps.push_front(Pattern::Wildcard);
                        l.0.push_front(Branch(ps.clone(), e.clone()));
                        r.0.push_front(Branch(ps, e));
                    }
                    None => {}
                    _ => panic!("unexpected pattern when expanding sum patterns"),
                }
                (l, r)
            },
        )
    }

    /// Π ~>var Π', remove head variable and wildcard patterns from `self`
    fn expand_var_pats(mut self) -> Self {
        for Branch(ps, _) in self.0.iter_mut() {
            match ps.pop_front() {
                Some(Pattern::Var(_)) | Some(Pattern::Wildcard) => {}
                None => {}
                _ => panic!("unexpected pattern when expanding var patterns"),
            }
        }

        self
    }

    /// Π ~>1 Π', remove head variable, wildcard, and unit patterns patterns from `self`
    fn expand_unit_pats(mut self) -> Self {
        for Branch(ps, _) in self.0.iter_mut() {
            match ps.pop_front() {
                Some(Pattern::Var(_)) | Some(Pattern::Wildcard) | Some(Pattern::Unit) => {}
                None => {}
                _ => panic!("unexpected pattern when expanding unit patterns"),
            }
        }

        self
    }
}
