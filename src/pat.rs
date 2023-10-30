use std::collections::VecDeque;

use crate::{
    context::{Item, TyCtx},
    syntax::{Expr, Ident},
    ty::{ExistsVar, ForallVar, Principality, Proposition, Sort, Term, TyVar, Type},
};

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

    /// Γ ⊢ Π covers A⃗ q, under the context `tcx`, check if `self` cover the types `tys`.
    fn covers(self, mut tys: VecDeque<Type>, principality: Principality, tcx: TyCtx) -> bool {
        match tys.pop_front() {
            // CoversEmpty
            None => self.0.front().is_some_and(|Branch(ps, _)| ps.is_empty()),
            // Covers1
            Some(Type::Unit) => {
                let expanded = self.expand_unit_pats();
                expanded.covers(tys, principality, tcx)
            }
            // Covers×
            Some(Type::Product(a1, a2)) => {
                let expanded = self.expand_pair_pats();
                tys.push_front(*a2);
                tys.push_front(*a1);
                expanded.covers(tys, principality, tcx)
            }
            // Covers+
            Some(Type::Sum(a1, a2)) => {
                let (l, r) = self.expand_sum_pats();

                let mut l_tys = tys.clone();
                l_tys.push_front(*a1);
                let covers_l = l.covers(l_tys, principality, tcx.clone());

                let mut r_tys = tys;
                r_tys.push_front(*a2);
                let covers_r = r.covers(r_tys, principality, tcx);

                covers_l && covers_r
            }
            // Covers∃
            Some(Type::Exists(ident, sort, _)) => {
                let new_tcx = tcx.extend(Item::Decl(TyVar::Exists(ExistsVar(ident.0)), sort));
                self.covers(tys, principality, new_tcx)
            }
            Some(Type::With(ty, prop)) => {
                tys.push_front(*ty);

                match principality {
                    // Covers∧
                    Principality::Principal => self.covers_assuming(tys, tcx, prop),
                    // Covers∧!̸
                    Principality::NotPrincipal => self.covers(tys, Principality::NotPrincipal, tcx),
                }
            }
            Some(Type::Vec(term, ty)) => {
                let guarded = self.guarded();
                let (nils, conses) = self.expand_vec_pats();

                let nil_tys = tys.clone();

                let mut cons_tys = tys;
                let n = ForallVar::fresh("n");
                cons_tys.push_front(Type::Vec(Term::ForallVar(n.clone()), ty.clone()));
                cons_tys.push_front(*ty);
                let new_tcx = tcx.extend(Item::Decl(TyVar::Forall(n.clone()), Sort::Natural));

                let preconds = match principality {
                    // CoversVec
                    Principality::Principal => {
                        let covers_nil = nils.covers_assuming(
                            nil_tys,
                            tcx.clone(),
                            Proposition(term.clone(), Term::Zero),
                        );
                        let covers_cons = conses.covers_assuming(
                            cons_tys,
                            new_tcx,
                            Proposition(term, Term::Succ(Box::new(Term::ForallVar(n)))),
                        );

                        covers_nil && covers_cons
                    }
                    // CoversVec!̸
                    Principality::NotPrincipal => {
                        let covers_nil =
                            nils.covers(nil_tys, Principality::NotPrincipal, tcx.clone());
                        let covers_cons =
                            conses.covers(cons_tys, Principality::NotPrincipal, new_tcx);

                        covers_nil && covers_cons
                    }
                };

                guarded && preconds
            }
            // CoversVar
            Some(_) => {
                let expanded = self.expand_var_pats();
                expanded.covers(tys, principality, tcx)
            }
        }
    }

    /// Γ / P ⊢ Π covers A⃗ !, under the context `tcx`, check if `self` cover the types `tys`, assuming P.
    fn covers_assuming(&self, tys: VecDeque<Type>, tcx: TyCtx, prop: Proposition) -> bool {
        todo!()
    }

    /// Π guarded, `self` contains a list pattern constructor in head position.
    fn guarded(&self) -> bool {
        self.0.iter().any(|Branch(ps, _)| match ps.front() {
            Some(Pattern::Nil | Pattern::Cons(_, _)) => true,
            Some(Pattern::Var(_) | Pattern::Wildcard) | None => false,
            _ => panic!("unexpected pattern when checking if branches are guarded"),
        })
    }

    /// Π ~>Vec Π[] || Π::, expand vector patterns in `self`.
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

    /// Π ~>× Π', expand head pair patterns in `self`.
    fn expand_pair_pats(mut self) -> Self {
        for Branch(ps, _) in self.0.iter_mut() {
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
                _ => panic!("unexpected pattern when expanding pair patterns"),
            }
        }

        self
    }

    /// Π ~>+ Πₗ || Πᵣ, expand head sum patterns in `self` into L and R sets.
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
                    Some(Pattern::Var(_) | Pattern::Wildcard) => {
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

    /// Π ~>var Π', remove head variable and wildcard patterns from `self`.
    fn expand_var_pats(mut self) -> Self {
        for Branch(ps, _) in self.0.iter_mut() {
            match ps.pop_front() {
                Some(Pattern::Var(_) | Pattern::Wildcard) => {}
                None => {}
                _ => panic!("unexpected pattern when expanding var patterns"),
            }
        }

        self
    }

    /// Π ~>1 Π', remove head variable, wildcard, and unit patterns patterns from `self`.
    fn expand_unit_pats(mut self) -> Self {
        for Branch(ps, _) in self.0.iter_mut() {
            match ps.pop_front() {
                Some(Pattern::Var(_) | Pattern::Wildcard | Pattern::Unit) => {}
                None => {}
                _ => panic!("unexpected pattern when expanding unit patterns"),
            }
        }

        self
    }
}
