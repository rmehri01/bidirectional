use std::collections::VecDeque;

use crate::{
    pat::{Branch, Branches},
    syntax::Ident,
    ty::{ExistsVar, ForallVar, Principality, Proposition, Sort, Term, TyVar, Type},
};

#[derive(Debug, Clone)]
struct TyCtx(Vec<Item>);

#[derive(Debug, Clone)]
enum Item {
    Decl(TyVar, Sort),
    ExprTyping(Ident, Type, Principality),
    SolvedExists(ExistsVar, Sort, Term),
    SolvedForall(ForallVar, Term),
    Marker(TyVar),
}

impl TyCtx {
    /// Extend `self` with the given `item`.
    fn extend(&self, item: Item) -> Self {
        let mut res = self.clone();
        res.0.push(item);
        res
    }

    /// Substitute for solved existential variables in `ty`.
    fn apply_to_ty(&self, ty: Type) -> Type {
        match ty {
            Type::ForallVar(ref alpha) => self
                .find_forall_solution(alpha)
                .map(|term| self.apply_to_term(term).to_ty())
                .unwrap_or(ty),
            Type::Implies(prop, ty) => {
                Type::Implies(self.apply_to_prop(prop), Box::new(self.apply_to_ty(*ty)))
            }
            Type::With(ty, prop) => {
                Type::With(Box::new(self.apply_to_ty(*ty)), self.apply_to_prop(prop))
            }
            Type::Function(a, b) => Type::Function(
                Box::new(self.apply_to_ty(*a)),
                Box::new(self.apply_to_ty(*b)),
            ),
            Type::Sum(a, b) => Type::Sum(
                Box::new(self.apply_to_ty(*a)),
                Box::new(self.apply_to_ty(*b)),
            ),
            Type::Product(a, b) => Type::Product(
                Box::new(self.apply_to_ty(*a)),
                Box::new(self.apply_to_ty(*b)),
            ),
            Type::Vec(idx, ty) => {
                Type::Vec(self.apply_to_term(idx), Box::new(self.apply_to_ty(*ty)))
            }
            Type::ExistsVar(ref alpha_hat) => self
                .find_exists_solution(alpha_hat)
                .map(|term| self.apply_to_term(term).to_ty())
                .unwrap_or(ty),
            Type::Forall(ident, sort, ty) => {
                Type::Forall(ident, sort, Box::new(self.apply_to_ty(*ty)))
            }
            Type::Exists(ident, sort, ty) => {
                Type::Exists(ident, sort, Box::new(self.apply_to_ty(*ty)))
            }
            Type::Unit => Type::Unit,
        }
    }

    /// Substitute for solved existential variables in `term`.
    fn apply_to_term(&self, term: Term) -> Term {
        match term {
            Term::Zero | Term::Succ(_) | Term::Unit => term,
            Term::ForallVar(ref alpha) => self
                .find_forall_solution(alpha)
                .map(|term| self.apply_to_term(term))
                .unwrap_or(term),
            Term::ExistsVar(ref alpha_hat) => self
                .find_exists_solution(alpha_hat)
                .map(|term| self.apply_to_term(term))
                .unwrap_or(term),
            Term::Function(a, b) => Term::Function(
                Box::new(self.apply_to_term(*a)),
                Box::new(self.apply_to_term(*b)),
            ),
            Term::Sum(a, b) => Term::Sum(
                Box::new(self.apply_to_term(*a)),
                Box::new(self.apply_to_term(*b)),
            ),
            Term::Product(a, b) => Term::Product(
                Box::new(self.apply_to_term(*a)),
                Box::new(self.apply_to_term(*b)),
            ),
        }
    }

    /// Substitute for solved existential variables in `prop`.
    fn apply_to_prop(&self, prop: Proposition) -> Proposition {
        Proposition(self.apply_to_term(prop.0), self.apply_to_term(prop.1))
    }

    fn find_forall_solution(&self, for_var: &ForallVar) -> Option<Term> {
        self.0.iter().find_map(|item| match item {
            Item::SolvedForall(alpha, monotype) if for_var == alpha => Some(monotype.clone()),
            _ => None,
        })
    }

    fn find_exists_solution(&self, for_var: &ExistsVar) -> Option<Term> {
        self.0.iter().find_map(|item| match item {
            Item::SolvedExists(alpha_hat, _, monotype) if for_var == alpha_hat => {
                Some(monotype.clone())
            }
            _ => None,
        })
    }

    /// Γ ⊢ A <:ᴾ B ⊣ ∆, under `self`, check if type `a` is a subtype of `b` with output ctx ∆,
    /// decomposing head connectives of polarity P.
    fn check_subtype(self, a: Type, b: Type) -> TyCtx {
        todo!()
    }

    /// Γ ⊢ Π covers A⃗ q, under the context `self`, check if `branches` cover the types `tys`.
    fn branches_cover(
        self,
        branches: Branches,
        mut tys: VecDeque<Type>,
        principality: Principality,
    ) -> bool {
        match tys.pop_front() {
            // CoversEmpty
            None => branches
                .0
                .front()
                .is_some_and(|Branch(ps, _)| ps.is_empty()),
            // Covers1
            Some(Type::Unit) => {
                let expanded = branches.expand_unit_pats();
                self.branches_cover(expanded, tys, principality)
            }
            // Covers×
            Some(Type::Product(a1, a2)) => {
                let expanded = branches.expand_pair_pats();
                tys.push_front(*a2);
                tys.push_front(*a1);
                self.branches_cover(expanded, tys, principality)
            }
            // Covers+
            Some(Type::Sum(a1, a2)) => {
                let (l, r) = branches.expand_sum_pats();

                let mut l_tys = tys.clone();
                l_tys.push_front(*a1);
                let covers_l = self.clone().branches_cover(l, l_tys, principality);

                let mut r_tys = tys;
                r_tys.push_front(*a2);
                let covers_r = self.branches_cover(r, r_tys, principality);

                covers_l && covers_r
            }
            // Covers∃
            Some(Type::Exists(ident, sort, _)) => {
                let new_tcx = self.extend(Item::Decl(TyVar::Exists(ExistsVar(ident.0)), sort));
                new_tcx.branches_cover(branches, tys, principality)
            }
            Some(Type::With(ty, prop)) => {
                tys.push_front(*ty);

                match principality {
                    // Covers∧
                    Principality::Principal => self.branches_cover_assuming(prop, branches, tys),
                    // Covers∧!̸
                    Principality::NotPrincipal => {
                        self.branches_cover(branches, tys, Principality::NotPrincipal)
                    }
                }
            }
            Some(Type::Vec(term, ty)) => {
                let guarded = branches.guarded();
                let (nils, conses) = branches.expand_vec_pats();

                let nil_tys = tys.clone();

                let mut cons_tys = tys;
                let n = ForallVar::fresh("n");
                cons_tys.push_front(Type::Vec(Term::ForallVar(n.clone()), ty.clone()));
                cons_tys.push_front(*ty);
                let new_tcx = self.extend(Item::Decl(TyVar::Forall(n.clone()), Sort::Natural));

                let preconds = match principality {
                    // CoversVec
                    Principality::Principal => {
                        let covers_nil = self.branches_cover_assuming(
                            Proposition(term.clone(), Term::Zero),
                            nils,
                            nil_tys,
                        );
                        let covers_cons = new_tcx.branches_cover_assuming(
                            Proposition(term, Term::Succ(Box::new(Term::ForallVar(n)))),
                            conses,
                            cons_tys,
                        );

                        covers_nil && covers_cons
                    }
                    // CoversVec!̸
                    Principality::NotPrincipal => {
                        let covers_nil =
                            self.branches_cover(nils, nil_tys, Principality::NotPrincipal);
                        let covers_cons =
                            new_tcx.branches_cover(conses, cons_tys, Principality::NotPrincipal);

                        covers_nil && covers_cons
                    }
                };

                guarded && preconds
            }
            // CoversVar
            Some(_) => {
                let expanded = branches.expand_var_pats();
                self.branches_cover(expanded, tys, principality)
            }
        }
    }

    /// Γ / P ⊢ Π covers A⃗ !, under the context `self`, check if `branches` cover the types `tys`, assuming `prop`.
    fn branches_cover_assuming(
        self,
        prop: Proposition,
        branches: Branches,
        tys: VecDeque<Type>,
    ) -> bool {
        let Proposition(term1, term2) = prop;
        let maybe_tcx = self.unify(term1, term2, Sort::Natural);
        match maybe_tcx {
            MaybeTcx::Valid(new_tcx) => {
                let new_tys = tys.into_iter().map(|ty| new_tcx.apply_to_ty(ty)).collect();
                new_tcx.branches_cover(branches, new_tys, Principality::Principal)
            }
            MaybeTcx::Bottom => true,
        }
    }

    /// Γ / σ ≐ τ : κ ⊣ ∆⊥, unify `term1` and `term2`, taking `self` to ∆ or ⊥
    fn unify(self, term1: Term, term2: Term, sort: Sort) -> MaybeTcx {
        todo!()
    }
}

/// An equality can yield inconsistency, so the resulting [TyCtx] can be valid or ⊥.
enum MaybeTcx {
    Valid(TyCtx),
    Bottom,
}
