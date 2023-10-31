use std::{collections::VecDeque, iter};

use crate::{
    pat::{Branch, Branches},
    syntax::Ident,
    ty::{Connective, ExistsVar, ForallVar, Principality, Proposition, Sort, Term, TyVar, Type},
};

#[derive(Debug, Clone)]
struct TyCtx(Vec<Entry>);

#[derive(Debug, Clone, PartialEq)]
enum Entry {
    Decl(TyVar, Sort),
    ExprTyping(Ident, Type, Principality),
    SolvedExists(ExistsVar, Sort, Term),
    SolvedForall(ForallVar, Term),
    Marker(TyVar),
}

impl TyCtx {
    /// Extend `self` with the given `entry`.
    fn extend(&self, entry: Entry) -> Self {
        let mut res = self.clone();
        res.0.push(entry);
        res
    }

    /// Drops all entries in the context from `entry` and onward.
    fn drop_from(mut self, entry: Entry) -> Self {
        let idx = self
            .0
            .iter()
            .position(|it| *it == entry)
            .expect("entry should be found in this context");
        self.0.truncate(idx);
        self
    }

    /// Replaces `this` with `that`.
    fn replace(self, this: Entry, that: Entry) -> Self {
        self.replace_many(this, iter::once(that))
    }

    /// Replaces `entry` with `entries`.
    fn replace_many(mut self, entry: Entry, entries: impl Iterator<Item = Entry>) -> Self {
        let idx = self
            .0
            .iter()
            .position(|it| *it == entry)
            .expect("entry should be found in this context");
        Self(self.0.splice(idx..=idx, entries).collect())
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
            Type::Binary(a, op, b) => Type::Binary(
                Box::new(self.apply_to_ty(*a)),
                op,
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
            Term::Binary(a, op, b) => Term::Binary(
                Box::new(self.apply_to_term(*a)),
                op,
                Box::new(self.apply_to_term(*b)),
            ),
        }
    }

    /// Substitute for solved existential variables in `prop`.
    fn apply_to_prop(&self, prop: Proposition) -> Proposition {
        Proposition(self.apply_to_term(prop.0), self.apply_to_term(prop.1))
    }

    fn find_forall_solution(&self, for_var: &ForallVar) -> Option<Term> {
        self.0.iter().find_map(|entry| match entry {
            Entry::SolvedForall(alpha, monotype) if for_var == alpha => Some(monotype.clone()),
            _ => None,
        })
    }

    fn find_exists_solution(&self, for_var: &ExistsVar) -> Option<Term> {
        self.0.iter().find_map(|entry| match entry {
            Entry::SolvedExists(alpha_hat, _, monotype) if for_var == alpha_hat => {
                Some(monotype.clone())
            }
            _ => None,
        })
    }

    /// Γ ⊢ A <:ᴾ B ⊣ ∆, under `self`, check if type `a` is a subtype of `b` with output ctx ∆,
    /// decomposing head connectives of polarity P.
    fn check_subtype(self, a: Type, b: Type) -> Self {
        todo!()
    }

    /// Γ ⊢ P ≡ Q ⊣ ∆, under `self`, check that `p` is equivalent to `q` with output ctx ∆.
    fn check_props_equal(self, p: Proposition, q: Proposition) -> Self {
        // ≡PropEq
        let Proposition(p1, p2) = p;
        let Proposition(q1, q2) = q;
        let new_tcx = self.check_equation(p1, q1, Sort::Natural);

        let new_p2 = new_tcx.apply_to_term(p2);
        let new_q2 = new_tcx.apply_to_term(q2);
        new_tcx.check_equation(new_p2, new_q2, Sort::Natural)
    }

    /// Γ ⊢ t1 ≐ t2 : κ ⊣ ∆, check that `term1` equals `term2`, taking `self` to ∆.
    fn check_equation(self, term1: Term, term2: Term, sort: Sort) -> Self {
        todo!()
    }

    /// Γ ⊢ A ≡ B ⊣ ∆, under `self`, check that `a` is equivalent to `b` with output ctx ∆.
    fn check_tys_equal(self, a: Type, b: Type) -> Self {
        match (a, b) {
            // ≡Var
            (Type::ForallVar(alpha1), Type::ForallVar(alpha2)) if alpha1 == alpha2 => self,
            // ≡Exvar
            (Type::ExistsVar(alpha_hat1), Type::ExistsVar(alpha_hat2))
                if alpha_hat1 == alpha_hat2 =>
            {
                self
            }
            // ≡Unit
            (Type::Unit, Type::Unit) => self,
            // ≡⊕
            (Type::Binary(a1, op1, a2), Type::Binary(b1, op2, b2)) if op1 == op2 => {
                let new_tcx = self.check_tys_equal(*a1, *b1);

                let new_a2 = new_tcx.apply_to_ty(*a2);
                let new_b2 = new_tcx.apply_to_ty(*b2);
                new_tcx.check_tys_equal(new_a2, new_b2)
            }
            // ≡Vec
            (Type::Vec(t1, a1), Type::Vec(t2, a2)) => {
                let new_tcx = self.check_terms_equal(t1, t2);

                let new_a1 = new_tcx.apply_to_ty(*a1);
                let new_a2 = new_tcx.apply_to_ty(*a2);
                new_tcx.check_tys_equal(new_a1, new_a2)
            }
            // ≡∀
            (Type::Forall(alpha1, sort1, a), Type::Forall(alpha2, sort2, b))
                if alpha1 == alpha2 && sort1 == sort2 =>
            {
                let entry = Entry::Decl(TyVar::Forall(ForallVar(alpha1.0)), sort1);
                let new_tcx = self.extend(entry.clone());
                new_tcx.check_tys_equal(*a, *b).drop_from(entry)
            }
            // ≡∃
            (Type::Exists(alpha1, sort1, a), Type::Exists(alpha2, sort2, b))
                if alpha1 == alpha2 && sort1 == sort2 =>
            {
                let entry = Entry::Decl(TyVar::Exists(ExistsVar(alpha1.0)), sort1);
                let new_tcx = self.extend(entry.clone());
                new_tcx.check_tys_equal(*a, *b).drop_from(entry)
            }
            // ≡⊃
            // ≡∧
            (Type::Implies(p, a), Type::Implies(q, b)) | (Type::With(a, p), Type::With(b, q)) => {
                let new_tcx = self.check_props_equal(p, q);
                let new_a = new_tcx.apply_to_ty(*a);
                let new_b = new_tcx.apply_to_ty(*b);
                new_tcx.check_tys_equal(new_a, new_b)
            }
            // ≡InstantiateL
            // ≡InstantiateR
            (Type::ExistsVar(alpha_hat), tau) | (tau, Type::ExistsVar(alpha_hat))
                if !tau
                    .clone()
                    .to_term()
                    .free_exists_vars()
                    .contains(&alpha_hat)
                    && self.find_exists_solution(&alpha_hat).is_none() =>
            {
                self.instantiate(alpha_hat, tau.to_term(), Sort::Monotype)
            }
            _ => panic!("unexpected pattern for checking that types are equal"),
        }
    }

    /// Γ ⊢ A ≡ B ⊣ ∆, under `self`, check that `a` is equivalent to `b` with output ctx ∆.
    fn check_terms_equal(self, a: Term, b: Term) -> Self {
        // TODO: not sure if this is just normal equality
        todo!()
    }

    /// Γ ⊢ α̂ := t : κ ⊣ ∆, under `self`, instantiate `var` such that `var` = `t` with output ctx ∆.
    fn instantiate(self, var: ExistsVar, term: Term, sort: Sort) -> Self {
        match (term, sort) {
            // InstZero
            (Term::Zero, Sort::Natural) => self.replace(
                Entry::Decl(TyVar::Exists(var), Sort::Natural),
                Entry::SolvedExists(var, Sort::Natural, Term::Zero),
            ),
            // InstSucc
            (Term::Succ(t1), Sort::Natural) => {
                let alpha_hat1 = ExistsVar::fresh("α̂");
                let new_tcx = self.replace(
                    Entry::Decl(TyVar::Exists(var), Sort::Natural),
                    Entry::SolvedExists(
                        var,
                        Sort::Natural,
                        Term::Succ(Box::new(Term::ExistsVar(alpha_hat1))),
                    ),
                );
                new_tcx.instantiate(alpha_hat1, *t1, Sort::Natural)
            }
            _ => todo!(),
        }
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
            Some(Type::Binary(a1, Connective::Product, a2)) => {
                let expanded = branches.expand_pair_pats();
                tys.push_front(*a2);
                tys.push_front(*a1);
                self.branches_cover(expanded, tys, principality)
            }
            // Covers+
            Some(Type::Binary(a1, Connective::Sum, a2)) => {
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
                let new_tcx = self.extend(Entry::Decl(TyVar::Exists(ExistsVar(ident.0)), sort));
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
                cons_tys.push_front(Type::Vec(Term::ForallVar(n), ty.clone()));
                cons_tys.push_front(*ty);
                let new_tcx = self.extend(Entry::Decl(TyVar::Forall(n), Sort::Natural));

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

    /// Γ / σ ≐ τ : κ ⊣ ∆⊥, unify `term1` and `term2`, taking `self` to ∆ or ⊥.
    fn unify(self, term1: Term, term2: Term, sort: Sort) -> MaybeTcx {
        match (term1, term2, sort) {
            // ElimeqUvarRefl
            (Term::ForallVar(ForallVar(alpha1)), Term::ForallVar(ForallVar(alpha2)), _)
                if alpha1 == alpha2 =>
            {
                MaybeTcx::Valid(self)
            }
            // ElimeqZero
            (Term::Zero, Term::Zero, Sort::Natural) => MaybeTcx::Valid(self),
            // ElimeqSucc
            (Term::Succ(s1), Term::Succ(s2), Sort::Natural) => self.unify(*s1, *s2, Sort::Natural),
            // ElimeqUvarL
            // ElimeqUvarR
            (Term::ForallVar(alpha), term, _) | (term, Term::ForallVar(alpha), _)
                if !term.free_forall_vars().contains(&alpha)
                    && self.find_forall_solution(&alpha).is_none() =>
            {
                MaybeTcx::Valid(self.extend(Entry::SolvedForall(alpha, term)))
            }
            // ElimeqUvarL⊥
            // ElimeqUvarR⊥
            (Term::ForallVar(alpha), term, _) | (term, Term::ForallVar(alpha), _)
                if term.free_forall_vars().contains(&alpha) =>
            {
                MaybeTcx::Bottom
            }
            // ElimeqUnit
            (Term::Unit, Term::Unit, Sort::Monotype) => MaybeTcx::Valid(self),
            (Term::Binary(a1, op1, a2), Term::Binary(b1, op2, b2), Sort::Monotype)
                if op1 == op2 =>
            {
                let maybe_tcx = self.unify(*a1, *b1, Sort::Monotype);
                match maybe_tcx {
                    // ElimeqBin
                    MaybeTcx::Valid(new_tcx) => {
                        let new_b1 = new_tcx.apply_to_term(*a2);
                        let new_b2 = new_tcx.apply_to_term(*b2);
                        new_tcx.unify(new_b1, new_b2, Sort::Monotype)
                    }
                    // ElimeqBinBot
                    MaybeTcx::Bottom => MaybeTcx::Bottom,
                }
            }
            // ElimeqClash
            (term1, term2, _) if term1.clashes_with(&term2) => MaybeTcx::Bottom,
            _ => panic!("unexpected unification pattern for two terms"),
        }
    }
}

/// An equality can yield inconsistency, so the resulting [TyCtx] can be valid or ⊥.
enum MaybeTcx {
    Valid(TyCtx),
    Bottom,
}
