use std::collections::{HashSet, VecDeque};

use crate::{
    pat::{Branch, Branches, Pattern},
    syntax::{Expr, Ident, Spine},
    ty::{
        Connective, ExistsVar, ForallVar, Polarity, Principality, Proposition, Sort, Term, TyVar,
        Type,
    },
};

#[derive(Debug, Clone, Default)]
pub struct TyCtx(Vec<Entry>);

#[derive(Debug, Clone, PartialEq)]
pub enum Entry {
    Unsolved(TyVar, Sort),
    ExprTyping(Ident, Type, Principality),
    SolvedExists(ExistsVar, Sort, Term),
    SolvedForall(ForallVar, Term),
    Marker(TyVar),
}

impl TyCtx {
    pub fn new() -> Self {
        Self::default()
    }

    /// Extend `self` with the given `entry`.
    fn extend(&self, entry: Entry) -> Self {
        self.extend_many([entry])
    }

    /// Extend `self` with the given `entries`.
    fn extend_many(&self, entries: impl IntoIterator<Item = Entry>) -> Self {
        let mut res = self.clone();
        res.0.extend(entries);
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
        self.replace_with_many(this, [that])
    }

    /// Replaces `entry` with `entries`.
    fn replace_with_many(mut self, entry: Entry, entries: impl IntoIterator<Item = Entry>) -> Self {
        let idx = self
            .0
            .iter()
            .position(|it| *it == entry)
            .expect("entry should be found in this context");
        self.0.splice(idx..=idx, entries);
        Self(self.0)
    }

    /// Substitute for solved existential variables in `ty`.
    fn apply_to_ty(&self, ty: Type) -> Type {
        match ty {
            Type::ForallVar(ref alpha) => self
                .find_forall_solution(alpha)
                .map(|term| self.apply_to_term(term).into_ty())
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
                .map(|term| self.apply_to_term(term).into_ty())
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
            // TODO: should this be defined on zero and succ?
            Term::Zero | Term::Unit => term,
            Term::Succ(t) => Term::Succ(Box::new(self.apply_to_term(*t))),
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
        self.0.iter().rev().find_map(|entry| match entry {
            Entry::SolvedForall(alpha, monotype) if for_var == alpha => Some(monotype.clone()),
            _ => None,
        })
    }

    fn find_exists_solution(&self, for_var: &ExistsVar) -> Option<Term> {
        self.0.iter().rev().find_map(|entry| match entry {
            Entry::SolvedExists(alpha_hat, _, monotype) if for_var == alpha_hat => {
                Some(monotype.clone())
            }
            _ => None,
        })
    }

    fn find_expr_solution(&self, for_var: &Ident) -> Option<(Type, Principality)> {
        self.0.iter().rev().find_map(|entry| match entry {
            Entry::ExprTyping(x, ty, p) if for_var == x => Some((ty.clone(), *p)),
            _ => None,
        })
    }

    // TODO: not sure how necessary this is, seems like overlaps with find_solution?
    fn find_unsolved(&self, var: &TyVar) -> Option<Sort> {
        self.0.iter().rev().find_map(|entry| match entry {
            Entry::Unsolved(found_var, sort) if found_var == var => Some(*sort),
            _ => None,
        })
    }

    // TODO: not sure how necessary this is, seems like overlaps with find_solution?
    fn is_unsolved(&self, var: &TyVar) -> bool {
        self.find_unsolved(var).is_some()
    }

    /// Γ ⊢ e <== A p ⊣ ∆, under `self`, expression `expr` checks against type `ty` with output context ∆.
    fn check_expr_ty(self, expr: Expr, ty: Type, p: Principality) -> Self {
        match (expr, ty, p) {
            // Rec
            (Expr::Fix(x, v), a, p) => {
                let entry = Entry::ExprTyping(x, a.clone(), p);
                // TODO: not sure if we need a separate check_value
                self.extend(entry.clone())
                    .check_expr_ty(v.into_expr(), a, p)
                    .drop_from(entry)
            }
            // 1I
            (Expr::Unit, Type::Unit, _) => self,
            // 1Iα̂
            (Expr::Unit, Type::ExistsVar(alpha_hat), Principality::NonPrincipal)
                if self
                    .0
                    .contains(&Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Monotype)) =>
            {
                self.replace(
                    Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Monotype),
                    Entry::SolvedExists(alpha_hat, Sort::Monotype, Term::Unit),
                )
            }
            // TODO: why are these v in the paper, are they always values?
            // ∀I
            (v, Type::Forall(alpha, sort, a), p) if v.is_intro_form() => {
                let entry = Entry::Unsolved(TyVar::Forall(ForallVar(alpha.0)), sort);
                self.extend(entry.clone())
                    .check_expr_ty(v, *a, p)
                    .drop_from(entry)
            }
            // ∃I
            (e, Type::Exists(alpha, sort, mut a), _) if e.is_intro_form() => {
                let alpha = ExistsVar(alpha.0);
                let alpha_hat = ExistsVar::fresh("α^");
                a.substitute_exists(alpha, alpha_hat);
                self.extend(Entry::Unsolved(TyVar::Exists(alpha_hat), sort))
                    .check_expr_ty(e, *a, Principality::NonPrincipal)
            }
            (v, Type::Implies(prop, a), Principality::Principal) if v.is_intro_form() => {
                let mark = ForallVar::fresh("P");
                let marker = Entry::Marker(TyVar::Forall(mark));
                let maybe_tcx = self.extend(marker.clone()).assume_prop(prop);

                match maybe_tcx {
                    // ⊃I
                    MaybeTcx::Valid(new_tcx) => {
                        let new_a = new_tcx.apply_to_ty(*a);
                        new_tcx
                            .check_expr_ty(v, new_a, Principality::Principal)
                            .drop_from(marker)
                    }
                    // ⊃I⊥
                    MaybeTcx::Bottom => self,
                }
            }
            // ∧I
            (e, Type::With(a, prop), p) if !e.is_case() => {
                let new_tcx = self.check_prop(prop);

                let new_a = new_tcx.apply_to_ty(*a);
                new_tcx.check_expr_ty(e, new_a, p)
            }
            // ->I
            (Expr::Function(x, e), Type::Binary(a, Connective::Function, b), p) => {
                let entry = Entry::ExprTyping(x, *a, p);
                self.extend(entry.clone())
                    .check_expr_ty(*e, *b, p)
                    .drop_from(entry)
            }
            // ->Iα̂
            (Expr::Function(x, e), Type::ExistsVar(alpha_hat), Principality::NonPrincipal)
                if self
                    .0
                    .contains(&Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Monotype)) =>
            {
                let alpha_hat1 = ExistsVar::fresh("α^");
                let alpha_hat2 = ExistsVar::fresh("α^");

                let x_entry =
                    Entry::ExprTyping(x, Type::ExistsVar(alpha_hat1), Principality::NonPrincipal);
                let new_tcx = self
                    .replace_with_many(
                        Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Monotype),
                        [
                            Entry::Unsolved(TyVar::Exists(alpha_hat1), Sort::Monotype),
                            Entry::Unsolved(TyVar::Exists(alpha_hat2), Sort::Monotype),
                            Entry::SolvedExists(
                                alpha_hat,
                                Sort::Monotype,
                                Term::Binary(
                                    Box::new(Term::ExistsVar(alpha_hat1)),
                                    Connective::Function,
                                    Box::new(Term::ExistsVar(alpha_hat2)),
                                ),
                            ),
                        ],
                    )
                    .extend(x_entry.clone());

                new_tcx
                    .check_expr_ty(*e, Type::ExistsVar(alpha_hat2), Principality::NonPrincipal)
                    .drop_from(x_entry)
            }
            // Case
            (Expr::Case(e, branches), c, p) => {
                let (a, q, new_tcx) = self.synth_expr_ty(*e);

                let new_a = new_tcx.apply_to_ty(a.clone());
                let new_c = new_tcx.apply_to_ty(c);
                let new_tcx =
                    new_tcx.check_branches(branches.clone(), VecDeque::from([new_a]), q, new_c, p);

                let new_a = new_tcx.apply_to_ty(a);
                if !new_tcx
                    .clone()
                    .branches_cover(branches, VecDeque::from([new_a]), q)
                {
                    panic!("branches do not cover all cases")
                }

                new_tcx
            }
            // +Iₖ
            (Expr::Inj1(e), Type::Binary(ty, Connective::Sum, _), p)
            | (Expr::Inj2(e), Type::Binary(_, Connective::Sum, ty), p) => {
                self.check_expr_ty(*e, *ty, p)
            }
            // +Iα̂ₖ
            (Expr::Inj1(e), Type::ExistsVar(alpha_hat), Principality::NonPrincipal)
                if self
                    .0
                    .contains(&Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Monotype)) =>
            {
                let alpha_hat1 = ExistsVar::fresh("α^");
                let alpha_hat2 = ExistsVar::fresh("α^");

                let new_tcx = self.replace_with_many(
                    Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Monotype),
                    [
                        Entry::Unsolved(TyVar::Exists(alpha_hat1), Sort::Monotype),
                        Entry::Unsolved(TyVar::Exists(alpha_hat2), Sort::Monotype),
                        Entry::SolvedExists(
                            alpha_hat,
                            Sort::Monotype,
                            Term::Binary(
                                Box::new(Term::ExistsVar(alpha_hat1)),
                                Connective::Sum,
                                Box::new(Term::ExistsVar(alpha_hat2)),
                            ),
                        ),
                    ],
                );

                new_tcx.check_expr_ty(*e, Type::ExistsVar(alpha_hat1), Principality::NonPrincipal)
            }
            (Expr::Inj2(e), Type::ExistsVar(alpha_hat), Principality::NonPrincipal)
                if self
                    .0
                    .contains(&Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Monotype)) =>
            {
                let alpha_hat1 = ExistsVar::fresh("α^");
                let alpha_hat2 = ExistsVar::fresh("α^");

                let new_tcx = self.replace_with_many(
                    Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Monotype),
                    [
                        Entry::Unsolved(TyVar::Exists(alpha_hat1), Sort::Monotype),
                        Entry::Unsolved(TyVar::Exists(alpha_hat2), Sort::Monotype),
                        Entry::SolvedExists(
                            alpha_hat,
                            Sort::Monotype,
                            Term::Binary(
                                Box::new(Term::ExistsVar(alpha_hat1)),
                                Connective::Sum,
                                Box::new(Term::ExistsVar(alpha_hat2)),
                            ),
                        ),
                    ],
                );

                new_tcx.check_expr_ty(*e, Type::ExistsVar(alpha_hat2), Principality::NonPrincipal)
            }
            // ×I
            (Expr::Pair(e1, e2), Type::Binary(a1, Connective::Product, a2), p) => {
                let new_tcx = self.check_expr_ty(*e1, *a1, p);

                let new_a2 = new_tcx.apply_to_ty(*a2);
                new_tcx.check_expr_ty(*e2, new_a2, p)
            }
            // ×Iα̂
            (Expr::Pair(e1, e2), Type::ExistsVar(alpha_hat), Principality::NonPrincipal)
                if self
                    .0
                    .contains(&Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Monotype)) =>
            {
                let alpha_hat1 = ExistsVar::fresh("α^");
                let alpha_hat2 = ExistsVar::fresh("α^");

                let new_tcx = self.replace_with_many(
                    Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Monotype),
                    [
                        Entry::Unsolved(TyVar::Exists(alpha_hat2), Sort::Monotype),
                        Entry::Unsolved(TyVar::Exists(alpha_hat1), Sort::Monotype),
                        Entry::SolvedExists(
                            alpha_hat,
                            Sort::Monotype,
                            Term::Binary(
                                Box::new(Term::ExistsVar(alpha_hat1)),
                                Connective::Product,
                                Box::new(Term::ExistsVar(alpha_hat2)),
                            ),
                        ),
                    ],
                );

                let new_tcx = new_tcx.check_expr_ty(
                    *e1,
                    Type::ExistsVar(alpha_hat1),
                    Principality::NonPrincipal,
                );

                let new_alpha_hat_2 = new_tcx.apply_to_ty(Type::ExistsVar(alpha_hat2));
                new_tcx.check_expr_ty(*e2, new_alpha_hat_2, Principality::NonPrincipal)
            }
            // Nil
            (Expr::Nil, Type::Vec(t, _), _) => self.check_prop(Proposition(t, Term::Zero)),
            // Cons
            (Expr::Cons(e1, e2), Type::Vec(t, a), p) => {
                let alpha_hat = ExistsVar::fresh("α^");
                let marker = Entry::Marker(TyVar::Exists(alpha_hat));

                let new_tcx = self
                    .extend_many([
                        marker.clone(),
                        Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Natural),
                    ])
                    .check_prop(Proposition(
                        t,
                        Term::Succ(Box::new(Term::ExistsVar(alpha_hat))),
                    ));

                let new_a = new_tcx.apply_to_ty(*a.clone());
                let new_tcx = new_tcx.check_expr_ty(*e1, new_a, p);

                let new_ty = new_tcx.apply_to_ty(Type::Vec(Term::ExistsVar(alpha_hat), a));
                new_tcx
                    .check_expr_ty(*e2, new_ty, Principality::NonPrincipal)
                    .drop_from(marker)
            }
            // TODO: do other cases need to fall through into this?
            // Sub
            (e, b, _) => {
                let (a, _, new_tcx) = self.synth_expr_ty(e);

                let polarity = b.polarity().join(a.polarity());
                new_tcx.check_subtype(a, b, polarity)
            }
        }
    }

    /// Γ ⊢ Π :: A⃗ q <== C p ⊣ ∆, under `self`, check `branches` with patterns of type `pattern_tys` and
    /// bodies of `body_ty` with output context ∆.
    fn check_branches(
        self,
        mut branches: Branches,
        pattern_tys: VecDeque<Type>,
        q: Principality,
        body_ty: Type,
        p: Principality,
    ) -> Self {
        match branches.0.pop_front() {
            // MatchEmpty
            None => self,
            // MatchSeq
            Some(branch) => {
                let new_tcx = self.check_branch(branch, pattern_tys.clone(), q, body_ty.clone(), p);
                let new_tys = pattern_tys
                    .into_iter()
                    .map(|ty| new_tcx.apply_to_ty(ty))
                    .collect();
                new_tcx.check_branches(branches, new_tys, q, body_ty, p)
            }
        }
    }

    /// Γ ⊢ π :: A⃗ q <== C p ⊣ ∆, under `self`, check `branch` with patterns of type `pattern_tys` and
    /// bodies of `body_ty` with output context ∆.
    fn check_branch(
        self,
        branch: Branch,
        mut pattern_tys: VecDeque<Type>,
        q: Principality,
        body_ty: Type,
        p: Principality,
    ) -> Self {
        let Branch(mut ps, e) = branch;
        match (ps.pop_front(), pattern_tys.pop_front(), q, body_ty, p) {
            // MatchBase
            (None, None, _, body_ty, p) => self.check_expr_ty(e, body_ty, p),
            // MatchUnit
            (Some(Pattern::Unit), Some(Type::Unit), q, body_ty, p) => {
                self.check_branch(Branch(ps, e), pattern_tys, q, body_ty, p)
            }
            // Match∃
            (Some(pat), Some(Type::Exists(alpha, sort, a)), q, body_ty, p) => {
                ps.push_front(pat);
                pattern_tys.push_front(*a);

                let entry = Entry::Unsolved(TyVar::Exists(ExistsVar(alpha.0)), sort);
                self.extend(entry.clone())
                    .check_branch(Branch(ps, e), pattern_tys, q, body_ty, p)
                    .drop_from(entry)
            }
            (Some(pat), Some(Type::With(a, prop)), q, body_ty, p) => {
                ps.push_front(pat);
                pattern_tys.push_front(*a);

                match q {
                    // Match∧
                    Principality::Principal => {
                        self.check_branch_assuming(prop, Branch(ps, e), pattern_tys, body_ty, p)
                    }
                    // Match∧!̸
                    Principality::NonPrincipal => self.check_branch(
                        Branch(ps, e),
                        pattern_tys,
                        Principality::NonPrincipal,
                        body_ty,
                        p,
                    ),
                }
            }
            // Match×
            (
                Some(Pattern::Pair(p1, p2)),
                Some(Type::Binary(a1, Connective::Product, a2)),
                q,
                body_ty,
                p,
            ) => {
                ps.push_front(*p2);
                ps.push_front(*p1);
                pattern_tys.push_front(*a2);
                pattern_tys.push_front(*a1);
                self.check_branch(Branch(ps, e), pattern_tys, q, body_ty, p)
            }
            // Match+ₖ
            (
                Some(Pattern::Inj1(pat)),
                Some(Type::Binary(ty, Connective::Sum, _)),
                q,
                body_ty,
                p,
            )
            | (
                Some(Pattern::Inj2(pat)),
                Some(Type::Binary(_, Connective::Sum, ty)),
                q,
                body_ty,
                p,
            ) => {
                ps.push_front(*pat);
                pattern_tys.push_front(*ty);
                self.check_branch(Branch(ps, e), pattern_tys, q, body_ty, p)
            }
            // MatchNeg
            (Some(Pattern::Var(z)), Some(a), q, body_ty, p) if !a.is_quantifier() => {
                let entry = Entry::ExprTyping(z, a, Principality::Principal);
                self.extend(entry.clone())
                    .check_branch(Branch(ps, e), pattern_tys, q, body_ty, p)
                    .drop_from(entry)
            }
            // MatchWild
            (Some(Pattern::Wildcard), Some(a), q, body_ty, p) if !a.is_quantifier() => {
                self.check_branch(Branch(ps, e), pattern_tys, q, body_ty, p)
            }
            (Some(Pattern::Nil), Some(Type::Vec(t, _)), q, body_ty, p) => {
                match q {
                    // MatchNil
                    Principality::Principal => self.check_branch_assuming(
                        Proposition(t, Term::Zero),
                        Branch(ps, e),
                        pattern_tys,
                        body_ty,
                        p,
                    ),
                    // MatchNil!̸
                    Principality::NonPrincipal => self.check_branch(
                        Branch(ps, e),
                        pattern_tys,
                        Principality::NonPrincipal,
                        body_ty,
                        p,
                    ),
                }
            }
            (Some(Pattern::Cons(p1, p2)), Some(Type::Vec(t, a)), q, body_ty, p) => {
                let alpha = ForallVar::fresh("α");
                let entry = Entry::Unsolved(TyVar::Forall(alpha), Sort::Natural);
                ps.push_front(*p2);
                ps.push_front(*p1);
                pattern_tys.push_front(Type::Vec(Term::ForallVar(alpha), a.clone()));
                pattern_tys.push_front(*a);

                match q {
                    // MatchCons
                    Principality::Principal => self
                        .extend(entry.clone())
                        .check_branch_assuming(
                            Proposition(t, Term::Succ(Box::new(Term::ForallVar(alpha)))),
                            Branch(ps, e),
                            pattern_tys,
                            body_ty,
                            p,
                        )
                        .drop_from(entry),
                    // MatchCons!̸
                    Principality::NonPrincipal => self
                        .extend(entry.clone())
                        .check_branch(
                            Branch(ps, e),
                            pattern_tys,
                            Principality::NonPrincipal,
                            body_ty,
                            p,
                        )
                        .drop_from(entry),
                }
            }
            (hd_pats, hd_tys, q, body_ty, p) => panic!("unexpected pattern when checking branch: {hd_pats:?} {hd_tys:?} {q:?} {body_ty:?} {p:?}"),
        }
    }

    /// Γ / P ⊢ π :: A⃗ ! <== C p ⊣ ∆, under `self`, incorporate proposition `prop` while checking
    /// `branches` with patterns of type `pattern_tys` and bodies of `body_ty` with output context ∆.
    fn check_branch_assuming(
        self,
        prop: Proposition,
        branch: Branch,
        pattern_tys: VecDeque<Type>,
        body_ty: Type,
        p: Principality,
    ) -> Self {
        let Proposition(t1, t2) = prop;

        let mark = ForallVar::fresh("P");
        let marker = Entry::Marker(TyVar::Forall(mark));

        // TODO: what should this sort be
        let maybe_tcx = self.extend(marker.clone()).unify(t1, t2, Sort::Natural);
        match maybe_tcx {
            // Match⊥
            MaybeTcx::Bottom => self,
            // MatchUnify
            MaybeTcx::Valid(new_tcx) => {
                // TODO: should we sub here? paper doesn't say so but I think it should?
                let new_tys = pattern_tys
                    .into_iter()
                    .map(|ty| new_tcx.apply_to_ty(ty))
                    .collect();
                let new_body_ty = new_tcx.apply_to_ty(body_ty);
                new_tcx
                    .check_branch(branch, new_tys, Principality::Principal, new_body_ty, p)
                    .drop_from(marker)
            }
        }
    }

    /// Γ ⊢ e ==> A p ⊣ ∆, under `self`, expression `expr` synthesizes output type `A` with output context ∆.
    pub fn synth_expr_ty(self, expr: Expr) -> (Type, Principality, Self) {
        match expr {
            // Var
            Expr::Var(var) if self.find_expr_solution(&var).is_some() => {
                let (a, p) = self.find_expr_solution(&var).unwrap();
                // TODO: not sure if needs sub or not, seems to overwrite in recursive case, maybe need to rename quantifier vars or something?
                (a, p, self)
            }
            // Anno
            Expr::Annotation(e, a)
                if self.ty_principality_well_formed(a.clone(), Principality::Principal) =>
            {
                let new_a = self.apply_to_ty(a.clone());
                let new_tcx = self.check_expr_ty(*e, new_a, Principality::Principal);

                let new_a = new_tcx.apply_to_ty(a);
                (new_a, Principality::Principal, new_tcx)
            }
            // ->E
            Expr::App(e, s) => {
                let (a, p, new_tcx) = self.synth_expr_ty(*e);
                new_tcx.apply_spine_recovering(s, a, p)
            }
            // Add straightforward rules, such as for unit
            Expr::Unit => (Type::Unit, Principality::Principal, self),
            _ => panic!("unexpected pattern in synth: {expr:?}"),
        }
    }

    /// Γ ⊢ s : A p >> C q ⊣ ∆, under `self`, passing spine `s` to a function of type `ty` synthesizes type `C`.
    fn apply_spine(self, mut s: Spine, ty: Type, p: Principality) -> (Type, Principality, Self) {
        match (s.0.pop_front(), ty) {
            // EmptySpine
            (None, ty) => (ty, p, self),
            // ∀Spine
            (Some(e), Type::Forall(alpha, sort, mut a)) => {
                s.0.push_front(e);
                let alpha = ForallVar(alpha.0);
                let alpha_hat = ExistsVar::fresh("α^");
                a.substitute_forall(alpha, alpha_hat);
                self.extend(Entry::Unsolved(TyVar::Exists(alpha_hat), sort))
                    .apply_spine(s, *a, Principality::NonPrincipal)
            }
            // ⊃Spine
            (Some(e), Type::Implies(prop, a)) => {
                let new_tcx = self.check_prop(prop);

                s.0.push_front(e);
                let new_a = new_tcx.apply_to_ty(*a);
                new_tcx.apply_spine(s, new_a, p)
            }
            // ->Spine
            (Some(e), Type::Binary(a, Connective::Function, b)) => {
                let new_tcx = self.check_expr_ty(e, *a, p);

                let new_b = new_tcx.apply_to_ty(*b);
                new_tcx.apply_spine(s, new_b, p)
            }
            // α̂Spine
            (Some(e), Type::ExistsVar(alpha_hat))
                if self
                    .0
                    .contains(&Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Monotype)) =>
            {
                let alpha_hat1 = ExistsVar::fresh("α^");
                let alpha_hat2 = ExistsVar::fresh("α^");

                let new_tcx = self.replace_with_many(
                    Entry::Unsolved(TyVar::Exists(alpha_hat), Sort::Monotype),
                    [
                        Entry::Unsolved(TyVar::Exists(alpha_hat2), Sort::Monotype),
                        Entry::Unsolved(TyVar::Exists(alpha_hat1), Sort::Monotype),
                        Entry::SolvedExists(
                            alpha_hat,
                            Sort::Monotype,
                            Term::Binary(
                                Box::new(Term::ExistsVar(alpha_hat1)),
                                Connective::Function,
                                Box::new(Term::ExistsVar(alpha_hat2)),
                            ),
                        ),
                    ],
                );

                s.0.push_front(e);
                new_tcx.apply_spine(
                    s,
                    Type::Binary(
                        Box::new(Type::ExistsVar(alpha_hat1)),
                        Connective::Function,
                        Box::new(Type::ExistsVar(alpha_hat2)),
                    ),
                    Principality::NonPrincipal,
                )
            }
            _ => panic!("unexpected pattern when applying spine"),
        }
    }

    /// Γ ⊢ s : A p >> C ⌈q⌉ ⊣ ∆, under `self`, passing spine `s` to a function of type `ty` synthesizes type `C`;
    /// recovering principality in q if possible.
    fn apply_spine_recovering(
        self,
        s: Spine,
        ty: Type,
        p: Principality,
    ) -> (Type, Principality, Self) {
        let (c, q, new_tcx) = self.apply_spine(s, ty, p);

        if p.is_principal() && q.is_non_principal() && c.free_exists_vars().is_empty() {
            // SpineRecover
            (c, Principality::Principal, new_tcx)
        } else {
            // SpinePass
            (c, q, new_tcx)
        }
    }

    /// Γ ⊢ A <:ᴾ B ⊣ ∆, under `self`, check if type `a` is a subtype of `b` with output ctx ∆,
    /// decomposing head connectives of polarity `p`.
    fn check_subtype(self, a: Type, b: Type, p: Polarity) -> Self {
        match (a, b, p) {
            // <:∀L
            (Type::Forall(alpha, sort, mut a), b, Polarity::Negative) if !b.is_forall() => {
                let alpha_hat = ExistsVar::fresh("α^");
                let marker = Entry::Marker(TyVar::Exists(alpha_hat));
                let new_tcx = self.extend_many([
                    marker.clone(),
                    Entry::Unsolved(TyVar::Exists(alpha_hat), sort),
                ]);
                a.substitute_forall(ForallVar(alpha.0), alpha_hat);
                new_tcx
                    .check_subtype(*a, b, Polarity::Negative)
                    .drop_from(marker)
            }
            // <:∀R
            (a, Type::Forall(beta, sort, b), Polarity::Negative) => {
                let beta = ForallVar(beta.0);
                let beta_entry = Entry::Unsolved(TyVar::Forall(beta), sort);
                self.extend(beta_entry.clone())
                    .check_subtype(a, *b, Polarity::Negative)
                    .drop_from(beta_entry)
            }
            // <:∃L
            (Type::Exists(alpha, sort, a), b, Polarity::Positive) => {
                let alpha = ExistsVar(alpha.0);
                let alpha_entry = Entry::Unsolved(TyVar::Exists(alpha), sort);
                self.extend(alpha_entry.clone())
                    .check_subtype(*a, b, Polarity::Positive)
                    .drop_from(alpha_entry)
            }
            // <:∃R
            (a, Type::Exists(beta, sort, mut b), Polarity::Positive) if !a.is_exists() => {
                let beta_hat = ExistsVar::fresh("β^");
                let marker = Entry::Marker(TyVar::Exists(beta_hat));
                let new_tcx = self.extend_many([
                    marker.clone(),
                    Entry::Unsolved(TyVar::Exists(beta_hat), sort),
                ]);
                b.substitute_exists(ExistsVar(beta.0), beta_hat);
                new_tcx
                    .check_subtype(a, *b, Polarity::Positive)
                    .drop_from(marker)
            }
            // -+L
            (a, b, Polarity::Positive)
                if a.polarity().is_negative() && b.polarity().is_non_positive() =>
            {
                self.check_subtype(a, b, Polarity::Negative)
            }
            // -+R
            (a, b, Polarity::Positive)
                if a.polarity().is_non_positive() && b.polarity().is_negative() =>
            {
                self.check_subtype(a, b, Polarity::Negative)
            }
            // +-L
            (a, b, Polarity::Negative)
                if a.polarity().is_positive() && b.polarity().is_non_negative() =>
            {
                self.check_subtype(a, b, Polarity::Positive)
            }
            // +-R
            (a, b, Polarity::Negative)
                if a.polarity().is_non_negative() && b.polarity().is_positive() =>
            {
                self.check_subtype(a, b, Polarity::Positive)
            }
            // <:Equiv
            (a, b, _) if !a.is_quantifier() && !b.is_quantifier() => self.check_tys_equal(a, b),
            (a, b, p) => panic!("unexpected pattern when checking subtype: {a:?} {b:?} {p:?}"),
        }
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
        match (term1, term2, sort) {
            // CheckeqVar
            (Term::ForallVar(var1), Term::ForallVar(var2), _) if var1 == var2 => self,
            (Term::ExistsVar(var1), Term::ExistsVar(var2), _) if var1 == var2 => self,
            // CheckeqUnit
            (Term::Unit, Term::Unit, Sort::Monotype) => self,
            // CheckeqBin
            (Term::Binary(a1, op1, a2), Term::Binary(b1, op2, b2), Sort::Monotype)
                if op1 == op2 =>
            {
                let new_tcx = self.check_equation(*a1, *b1, Sort::Monotype);

                let new_a2 = new_tcx.apply_to_term(*a2);
                let new_b2 = new_tcx.apply_to_term(*b2);
                new_tcx.check_equation(new_a2, new_b2, Sort::Monotype)
            }
            // CheckeqZero
            (Term::Zero, Term::Zero, Sort::Natural) => self,
            // CheckeqSucc
            (Term::Succ(t1), Term::Succ(t2), Sort::Natural) => {
                self.check_equation(*t1, *t2, Sort::Natural)
            }
            // CheckeqInstL
            // CheckeqInstR
            (Term::ExistsVar(alpha_hat), term, sort) | (term, Term::ExistsVar(alpha_hat), sort)
                if self
                    .0
                    .contains(&Entry::Unsolved(TyVar::Exists(alpha_hat), sort))
                    && !term.free_exists_vars().contains(&alpha_hat) =>
            {
                self.instantiate(alpha_hat, term, sort)
            }
            (term1, term2, sort) => panic!(
                "unexpected pattern for checking term equation: {term1:?} {term2:?} {sort:?}"
            ),
        }
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
                let entry = Entry::Unsolved(TyVar::Forall(ForallVar(alpha1.0)), sort1);
                let new_tcx = self.extend(entry.clone());
                new_tcx.check_tys_equal(*a, *b).drop_from(entry)
            }
            // ≡∃
            (Type::Exists(alpha1, sort1, a), Type::Exists(alpha2, sort2, b))
                if alpha1 == alpha2 && sort1 == sort2 =>
            {
                let entry = Entry::Unsolved(TyVar::Exists(ExistsVar(alpha1.0)), sort1);
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
                    && self.is_unsolved(&TyVar::Exists(alpha_hat)) =>
            {
                self.instantiate(alpha_hat, tau.to_term(), Sort::Monotype)
            }
            (a, b) => panic!("unexpected pattern for checking that types are equal: {a:?} {b:?}"),
        }
    }

    /// Γ ⊢ A ≡ B ⊣ ∆, under `self`, check that `a` is equivalent to `b` with output ctx ∆.
    fn check_terms_equal(self, a: Term, b: Term) -> Self {
        // TODO: duplicated from ty, not sure if this is right
        match (a, b) {
            // ≡Var
            (Term::ForallVar(alpha1), Term::ForallVar(alpha2)) if alpha1 == alpha2 => self,
            // ≡Exvar
            (Term::ExistsVar(alpha_hat1), Term::ExistsVar(alpha_hat2))
                if alpha_hat1 == alpha_hat2 =>
            {
                self
            }
            // ≡Unit
            (Term::Unit, Term::Unit) => self,
            // ≡⊕
            (Term::Binary(a1, op1, a2), Term::Binary(b1, op2, b2)) if op1 == op2 => {
                let new_tcx = self.check_terms_equal(*a1, *b1);

                let new_a2 = new_tcx.apply_to_term(*a2);
                let new_b2 = new_tcx.apply_to_term(*b2);
                new_tcx.check_terms_equal(new_a2, new_b2)
            }
            // ≡InstantiateL
            // ≡InstantiateR
            (Term::ExistsVar(alpha_hat), tau) | (tau, Term::ExistsVar(alpha_hat))
                if !tau.clone().free_exists_vars().contains(&alpha_hat)
                    && self.is_unsolved(&TyVar::Exists(alpha_hat)) =>
            {
                // TODO: what sort
                self.instantiate(alpha_hat, tau, Sort::Natural)
            }
            (a, b) => panic!("unexpected pattern for checking that terms are equal: {a:?} {b:?}"),
        }
        // TODO: not sure if this is just normal equality
        // if a == b {
        //     self
        // } else {
        //     panic!("terms not equal: {self:#?} {a:?} {b:?}")
        // }
    }

    /// Γ ⊢ α̂ := t : κ ⊣ ∆, under `self`, instantiate `var` such that `var` = `t` with output ctx ∆.
    fn instantiate(self, var: ExistsVar, term: Term, sort: Sort) -> Self {
        match (term, sort) {
            // InstZero
            (Term::Zero, Sort::Natural) => self.replace(
                Entry::Unsolved(TyVar::Exists(var), Sort::Natural),
                Entry::SolvedExists(var, Sort::Natural, Term::Zero),
            ),
            // InstSucc
            (Term::Succ(t1), Sort::Natural)
                if self
                    .0
                    .contains(&Entry::Unsolved(TyVar::Exists(var), Sort::Natural)) =>
            {
                let alpha_hat1 = ExistsVar::fresh("α^");
                let new_tcx = self.replace_with_many(
                    Entry::Unsolved(TyVar::Exists(var), Sort::Natural),
                    [
                        Entry::Unsolved(TyVar::Exists(alpha_hat1), Sort::Natural),
                        Entry::SolvedExists(
                            var,
                            Sort::Natural,
                            Term::Succ(Box::new(Term::ExistsVar(alpha_hat1))),
                        ),
                    ],
                );
                new_tcx.instantiate(alpha_hat1, *t1, Sort::Natural)
            }
            // InstBin
            (Term::Binary(t1, op, t2), Sort::Monotype) => {
                let alpha_hat1 = ExistsVar::fresh("α^");
                let alpha_hat2 = ExistsVar::fresh("α^");

                let new_tcx = self
                    .replace_with_many(
                        Entry::Unsolved(TyVar::Exists(var), Sort::Monotype),
                        [
                            Entry::Unsolved(TyVar::Exists(alpha_hat2), Sort::Monotype),
                            Entry::Unsolved(TyVar::Exists(alpha_hat1), Sort::Monotype),
                            Entry::SolvedExists(
                                var,
                                Sort::Monotype,
                                Term::Binary(
                                    Box::new(Term::ExistsVar(alpha_hat1)),
                                    op,
                                    Box::new(Term::ExistsVar(alpha_hat2)),
                                ),
                            ),
                        ],
                    )
                    .instantiate(alpha_hat1, *t1, Sort::Monotype);

                let new_t2 = new_tcx.apply_to_term(*t2);
                new_tcx.instantiate(alpha_hat2, new_t2, Sort::Monotype)
            }
            // InstReach
            (Term::ExistsVar(beta), sort)
                if self.is_unsolved(&TyVar::Exists(var))
                    && self.is_unsolved(&TyVar::Exists(beta)) =>
            {
                self.replace(
                    Entry::Unsolved(TyVar::Exists(beta), sort),
                    Entry::SolvedExists(beta, sort, Term::ExistsVar(var)),
                )
            }
            // InstSolve
            (term, sort)
                if self.is_unsolved(&TyVar::Exists(var))
                    && self
                        .clone()
                        .drop_from(Entry::Unsolved(TyVar::Exists(var), sort))
                        .entails(&term, &sort) =>
            {
                self.replace(
                    Entry::Unsolved(TyVar::Exists(var), sort),
                    Entry::SolvedExists(var, sort, term),
                )
            }
            (term, sort) => {
                panic!("unexpected pattern when instantiating existential var: {var:?} {term:?} {sort:?}")
            }
        }
    }

    /// Γ ⊢ τ : κ, under `self`, `term` has sort `sort`
    fn entails(&self, term: &Term, sort: &Sort) -> bool {
        match (term, sort) {
            // ZeroSort
            (Term::Zero, Sort::Natural) => true,
            // SuccSort
            (Term::Succ(t), Sort::Natural) => self.entails(t, &Sort::Natural),
            // VarSort
            (Term::ForallVar(var), sort) => self
                .0
                .contains(&Entry::Unsolved(TyVar::Forall(*var), *sort)),
            // SolvedVarSort
            (Term::ExistsVar(var), sort) => {
                let unsolved_entails = self
                    .0
                    .contains(&Entry::Unsolved(TyVar::Exists(*var), *sort));
                let solved_entails = self
                    .0
                    .iter()
                    .any(|entry| matches!(
                        entry,
                        Entry::SolvedExists(found_var, found_sort, _) if found_var == var && found_sort == sort
                    ));

                unsolved_entails || solved_entails
            }
            // UnitSort
            (Term::Unit, Sort::Monotype) => true,
            // BinSort
            (Term::Binary(t1, _, t2), Sort::Monotype) => {
                self.entails(t1, &Sort::Monotype) && self.entails(t2, &Sort::Monotype)
            }
            _ => false,
        }
    }

    /// Γ ⊢ P prop, under `self`, `prop` is well-formed.
    fn prop_well_formed(&self, prop: &Proposition) -> bool {
        // EqProp
        let Proposition(t1, t2) = prop;
        self.entails(t1, &Sort::Natural) && self.entails(t2, &Sort::Natural)
    }

    /// Γ ⊢ A type, under `self`, `ty` is well-formed.
    fn ty_well_formed(&self, ty: &Type) -> bool {
        match ty {
            // VarWF
            Type::ForallVar(var) => self
                .0
                .contains(&Entry::Unsolved(TyVar::Forall(*var), Sort::Monotype)),
            // SolvedVarWF
            Type::ExistsVar(var) => {
                let unsolved_entails = self
                    .0
                    .contains(&Entry::Unsolved(TyVar::Exists(*var), Sort::Monotype));
                let solved_entails = self
                    .0
                    .iter()
                    .any(|entry| matches!(
                        entry,
                        Entry::SolvedExists(found_var, found_sort, _) if found_var == var && *found_sort == Sort::Monotype
                    ));

                unsolved_entails || solved_entails
            }
            // UnitWF
            Type::Unit => true,
            // BinWF
            Type::Binary(a, _, b) => self.ty_well_formed(a) && self.ty_well_formed(b),
            // VecWF
            Type::Vec(t, a) => self.entails(t, &Sort::Natural) && self.ty_well_formed(a),
            // ForallWF
            Type::Forall(ident, sort, ty) => self
                .extend(Entry::Unsolved(TyVar::Forall(ForallVar(ident.0)), *sort))
                .ty_well_formed(ty),
            // ExistsWF
            Type::Exists(ident, sort, ty) => self
                .extend(Entry::Unsolved(TyVar::Exists(ExistsVar(ident.0)), *sort))
                .ty_well_formed(ty),
            // ImpliesWF
            // WithWF
            Type::Implies(p, a) | Type::With(a, p) => {
                self.prop_well_formed(p) && self.ty_well_formed(a)
            }
        }
    }

    /// Γ ⊢ A p type, under `self`, `ty` is well-formed and respects principality `p`.
    fn ty_principality_well_formed(&self, ty: Type, p: Principality) -> bool {
        match p {
            // PrincipalWF
            Principality::Principal => {
                self.ty_well_formed(&ty) && self.apply_to_ty(ty).free_exists_vars().is_empty()
            }
            // NonPrincipalWF
            Principality::NonPrincipal => self.ty_well_formed(&ty),
        }
    }

    /// Γ ⊢ A⃗ p types, under `self`, `tys` are well-formed with principality `p`.
    fn tys_principality_well_formed(&self, tys: Vec<Type>, p: Principality) -> bool {
        // PrincipalTypevecWF
        tys.into_iter()
            .all(|ty| self.ty_principality_well_formed(ty, p))
    }

    /// Γ ctx, algorithmic context `self` is well-formed.
    fn well_formed(mut self) -> bool {
        match self.0.pop() {
            // EmptyCtx
            None => true,
            // HypCtx
            // Hyp!Ctx
            Some(Entry::ExprTyping(x, a, p)) => {
                let ty_well_formed = self.ty_well_formed(&a);
                let x_not_in_domain = self.find_expr_solution(&x).is_none();
                let principality_condition = match p {
                    Principality::Principal => self.apply_to_ty(a).free_exists_vars().is_empty(),
                    Principality::NonPrincipal => true,
                };
                let self_wf = self.well_formed();

                self_wf && x_not_in_domain && ty_well_formed && principality_condition
            }
            // VarCtx
            Some(Entry::Unsolved(var, _)) => !self.domain().contains(&var) && self.well_formed(),
            // SolvedCtx
            Some(Entry::SolvedExists(var, sort, term)) => {
                !self.domain().contains(&TyVar::Exists(var))
                    && self.entails(&term, &sort)
                    && self.well_formed()
            }
            // EqnVarCtx
            Some(Entry::SolvedForall(var, term)) => {
                let no_solution = self.find_forall_solution(&var).is_none();
                let sort = self.find_unsolved(&TyVar::Forall(var));
                let term_wf = sort.is_some_and(|sort| self.entails(&term, &sort));
                let self_wf = self.well_formed();

                self_wf && no_solution && term_wf
            }
            // MarkerCtx
            Some(Entry::Marker(var)) => !self.0.contains(&Entry::Marker(var)) && self.well_formed(),
        }
    }

    fn domain(&self) -> HashSet<TyVar> {
        let mut domain = HashSet::new();

        for entry in &self.0 {
            match entry {
                Entry::Unsolved(var, _) => {
                    domain.insert(*var);
                }
                Entry::ExprTyping(_, _, _) => {}
                Entry::SolvedExists(var, _, _) => {
                    domain.insert(TyVar::Exists(*var));
                }
                Entry::SolvedForall(var, _) => {
                    domain.insert(TyVar::Forall(*var));
                }
                Entry::Marker(_) => {}
            }
        }

        domain
    }

    /// Γ ⊢ P true ⊣ ∆, under `self`, check `prop`, with output ctx ∆.
    fn check_prop(self, prop: Proposition) -> Self {
        // CheckpropEq
        let Proposition(t1, t2) = prop;
        self.check_equation(t1, t2, Sort::Natural)
    }

    /// Γ / P true ⊣ ∆⊥, incorporate `prop` into `self`, producing output ctx ∆ or ⊥.
    fn assume_prop(self, prop: Proposition) -> MaybeTcx {
        // ElimpropEq
        let Proposition(t1, t2) = prop;
        self.unify(t1, t2, Sort::Natural)
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
            Some(Type::Exists(ident, sort, a)) => {
                let new_tcx = self.extend(Entry::Unsolved(TyVar::Exists(ExistsVar(ident.0)), sort));
                tys.push_front(*a);
                new_tcx.branches_cover(branches, tys, principality)
            }
            Some(Type::With(ty, prop)) => {
                tys.push_front(*ty);

                match principality {
                    // Covers∧
                    Principality::Principal => self.branches_cover_assuming(prop, branches, tys),
                    // Covers∧!̸
                    Principality::NonPrincipal => {
                        self.branches_cover(branches, tys, Principality::NonPrincipal)
                    }
                }
            }
            Some(Type::Vec(term, ty)) if branches.guarded() => {
                let (nils, conses) = branches.expand_vec_pats();

                let nil_tys = tys.clone();

                let mut cons_tys = tys;
                let n = ForallVar::fresh("n");
                cons_tys.push_front(Type::Vec(Term::ForallVar(n), ty.clone()));
                cons_tys.push_front(*ty);
                let new_tcx = self.extend(Entry::Unsolved(TyVar::Forall(n), Sort::Natural));

                match principality {
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
                    Principality::NonPrincipal => {
                        let covers_nil =
                            self.branches_cover(nils, nil_tys, Principality::NonPrincipal);
                        let covers_cons =
                            new_tcx.branches_cover(conses, cons_tys, Principality::NonPrincipal);

                        covers_nil && covers_cons
                    }
                }
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

        let new_term1 = self.apply_to_term(term1);
        let new_term2 = self.apply_to_term(term2);
        let maybe_tcx = self.unify(new_term1, new_term2, Sort::Natural);

        match maybe_tcx {
            // CoversEq
            MaybeTcx::Valid(new_tcx) => {
                let new_tys = tys.into_iter().map(|ty| new_tcx.apply_to_ty(ty)).collect();
                new_tcx.branches_cover(branches, new_tys, Principality::Principal)
            }
            // CoversEqBot
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
            (term1, term2, sort) => {
                panic!("unexpected unification pattern for two terms: {term1:?} {term2:?} {sort:?}")
            }
        }
    }
}

/// An equality can yield inconsistency, so the resulting [TyCtx] can be valid or ⊥.
enum MaybeTcx {
    Valid(TyCtx),
    Bottom,
}

#[cfg(test)]
mod tests {
    use internment::Intern;

    use crate::syntax::Value;

    use super::*;

    #[test]
    fn basic() {
        let tcx = TyCtx::new();
        let (ty, p, _) = tcx.synth_expr_ty(Expr::Unit);
        assert_eq!(ty, Type::Unit);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn basic_vec() {
        // TODO: this should be inferred without annotation
        let tcx = TyCtx::new();
        let vec_ty = Type::vec(Term::succ(Term::succ(Term::Zero)), Type::Unit);
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(
            Expr::cons(Expr::Unit, Expr::cons(Expr::Unit, Expr::Nil)),
            vec_ty.clone(),
        ));
        assert_eq!(ty, vec_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn basic_case() {
        let tcx = TyCtx::new();
        let x = Ident(Intern::new("x".to_string()));
        let vec_ty = Type::vec(Term::succ(Term::Zero), Type::Unit);
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(
            Expr::case(
                Expr::Unit,
                Branches::from_iter([Branch::from_iter(
                    [Pattern::Var(x)],
                    Expr::cons(Expr::Var(x), Expr::Nil),
                )]),
            ),
            vec_ty.clone(),
        ));
        assert_eq!(ty, vec_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn basic_sum() {
        let tcx = TyCtx::new();
        let x = Ident(Intern::new("x".to_string()));
        let sum_ty = Type::binary(
            Type::Unit,
            Connective::Sum,
            Type::forall(
                x,
                Sort::Monotype,
                Type::binary(
                    Type::ForallVar(ForallVar(x.0)),
                    Connective::Function,
                    Type::ForallVar(ForallVar(x.0)),
                ),
            ),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(
            Expr::inj2(Expr::function(x, Expr::Var(x))),
            sum_ty.clone(),
        ));
        assert_eq!(ty, sum_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn basic_product() {
        let tcx = TyCtx::new();
        let x = Ident(Intern::new("x".to_string()));
        let y = Ident(Intern::new("y".to_string()));
        let prod_ty = Type::binary(Type::Unit, Connective::Product, Type::Unit);
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(
            Expr::case(
                Expr::annotation(Expr::pair(Expr::Unit, Expr::Unit), prod_ty.clone()),
                Branches::from_iter([
                    Branch::from_iter(
                        [Pattern::pair(Pattern::Var(x), Pattern::Var(y))],
                        Expr::pair(Expr::Var(x), Expr::Var(y)),
                    ),
                    Branch::from_iter([Pattern::Wildcard], Expr::pair(Expr::Unit, Expr::Unit)),
                ]),
            ),
            prod_ty.clone(),
        ));
        assert_eq!(ty, prod_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn basic_app() {
        let tcx = TyCtx::new();
        let x = Ident(Intern::new("x".to_string()));
        let result_ty = Type::binary(
            Type::Unit,
            Connective::Sum,
            Type::vec(Term::Zero, Type::Unit),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::app(
            Expr::annotation(
                Expr::function(x, Expr::inj1(Expr::Var(x))),
                Type::binary(Type::Unit, Connective::Function, result_ty.clone()),
            ),
            Spine::from_iter([Expr::Unit]),
        ));
        assert_eq!(ty, result_ty);
        assert_eq!(p, Principality::Principal);
    }

    // TODO: can't apply id function to a vector?
    #[test]
    fn from_paper() {
        let id = Ident(Intern::new("id".to_string()));
        let alpha = Ident(Intern::new("α".to_string()));
        let tcx = TyCtx::new().extend(Entry::ExprTyping(
            id,
            Type::forall(
                alpha,
                Sort::Monotype,
                Type::binary(
                    Type::ForallVar(ForallVar(alpha.0)),
                    Connective::Function,
                    Type::ForallVar(ForallVar(alpha.0)),
                ),
            ),
            Principality::Principal,
        ));

        let (ty, p, _) =
            tcx.synth_expr_ty(Expr::app(Expr::Var(id), Spine::from_iter([Expr::Unit])));
        assert_eq!(ty, Type::Unit);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn reconstruct_vec() {
        let tcx = TyCtx::new();
        let xs = Ident(Intern::new("xs".to_string()));
        let y = Ident(Intern::new("y".to_string()));
        let ys = Ident(Intern::new("ys".to_string()));

        let n = Ident(Intern::new("n".to_string()));
        let alpha = Ident(Intern::new("α".to_string()));
        let fn_ty = Type::forall(
            n,
            Sort::Natural,
            Type::forall(
                alpha,
                Sort::Monotype,
                Type::binary(
                    Type::vec(
                        Term::ForallVar(ForallVar(n.0)),
                        Type::ForallVar(ForallVar(alpha.0)),
                    ),
                    Connective::Function,
                    Type::vec(
                        Term::ForallVar(ForallVar(n.0)),
                        Type::ForallVar(ForallVar(alpha.0)),
                    ),
                ),
            ),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(
            Expr::function(
                xs,
                Expr::case(
                    Expr::Var(xs),
                    Branches::from_iter([
                        Branch::from_iter(
                            [Pattern::cons(Pattern::Var(y), Pattern::Var(ys))],
                            Expr::cons(Expr::Var(y), Expr::Var(ys)),
                        ),
                        // TODO: wildcard or var here in pattern fails?
                        Branch::from_iter([Pattern::Nil], Expr::Nil),
                    ]),
                ),
            ),
            fn_ty.clone(),
        ));
        assert_eq!(ty, fn_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn rec_vec_id() {
        let tcx = TyCtx::new();
        let id = Ident(Intern::new("id".to_string()));
        let xs = Ident(Intern::new("xs".to_string()));
        let y = Ident(Intern::new("y".to_string()));
        let ys = Ident(Intern::new("ys".to_string()));

        let n = Ident(Intern::new("n".to_string()));
        let alpha = Ident(Intern::new("α".to_string()));
        let fn_ty = Type::forall(
            n,
            Sort::Natural,
            Type::forall(
                alpha,
                Sort::Monotype,
                Type::binary(
                    Type::vec(
                        Term::ForallVar(ForallVar(n.0)),
                        Type::ForallVar(ForallVar(alpha.0)),
                    ),
                    Connective::Function,
                    Type::vec(
                        Term::ForallVar(ForallVar(n.0)),
                        Type::ForallVar(ForallVar(alpha.0)),
                    ),
                ),
            ),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(
            Expr::Fix(
                id,
                Value::function(
                    xs,
                    Expr::case(
                        Expr::Var(xs),
                        Branches::from_iter([
                            Branch::from_iter([Pattern::Nil], Expr::Nil),
                            Branch::from_iter(
                                // TODO: add app to id
                                [Pattern::cons(Pattern::Var(y), Pattern::Var(ys))],
                                Expr::cons(
                                    Expr::Var(y),
                                    Expr::app(Expr::Var(id), Spine::from_iter([Expr::Var(ys)])),
                                ),
                            ),
                        ]),
                    ),
                ),
            ),
            fn_ty.clone(),
        ));
        assert_eq!(ty, fn_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn apply_id() {
        let tcx = TyCtx::new();

        let f = Ident(Intern::new("f".to_string()));
        let x = Ident(Intern::new("x".to_string()));
        let a = Ident(Intern::new("a".to_string()));
        let b = Ident(Intern::new("b".to_string()));
        let apply_fn = Expr::annotation(
            Expr::function(
                f,
                Expr::function(x, Expr::app(Expr::Var(f), Spine::from_iter([Expr::Var(x)]))),
            ),
            Type::forall(
                a,
                Sort::Monotype,
                Type::forall(
                    b,
                    Sort::Monotype,
                    Type::binary(
                        Type::binary(
                            Type::ForallVar(ForallVar(a.0)),
                            Connective::Function,
                            Type::ForallVar(ForallVar(b.0)),
                        ),
                        Connective::Function,
                        Type::binary(
                            Type::ForallVar(ForallVar(a.0)),
                            Connective::Function,
                            Type::ForallVar(ForallVar(b.0)),
                        ),
                    ),
                ),
            ),
        );
        let id = Expr::function(x, Expr::Var(x));
        let (ty, p, _) = tcx.synth_expr_ty(Expr::app(apply_fn, Spine::from_iter([id, Expr::Unit])));
        assert_eq!(ty, Type::Unit);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn head() {
        let tcx = TyCtx::new();
        let list = Ident(Intern::new("list".to_string()));
        let x = Ident(Intern::new("x".to_string()));
        let xs = Ident(Intern::new("xs".to_string()));
        let head = Expr::function(
            list,
            Expr::case(
                Expr::Var(list),
                Branches::from_iter([Branch::from_iter(
                    [Pattern::cons(Pattern::Var(x), Pattern::Var(xs))],
                    Expr::Var(x),
                )]),
            ),
        );

        let n = Ident(Intern::new("n".to_string()));
        let a = Ident(Intern::new("A".to_string()));
        let head_ty = Type::forall(
            n,
            Sort::Natural,
            Type::forall(
                a,
                Sort::Monotype,
                Type::binary(
                    Type::vec(
                        Term::succ(Term::ForallVar(ForallVar(n.0))),
                        Type::ForallVar(ForallVar(a.0)),
                    ),
                    Connective::Function,
                    Type::ForallVar(ForallVar(a.0)),
                ),
            ),
        );

        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(head, head_ty.clone()));
        assert_eq!(ty, head_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn poly_id() {
        let tcx = TyCtx::new();
        let id = Ident(Intern::new("id".to_string()));
        let a = Ident(Intern::new("a".to_string()));
        let result_ty = Type::binary(
            Type::Unit,
            Connective::Product,
            Type::binary(Type::Unit, Connective::Product, Type::Unit),
        );
        let apply_id = Expr::annotation(
            Expr::function(
                id,
                Expr::pair(
                    Expr::app(Expr::Var(id), Spine::from_iter([Expr::Unit])),
                    Expr::app(
                        Expr::Var(id),
                        Spine::from_iter([Expr::pair(Expr::Unit, Expr::Unit)]),
                    ),
                ),
            ),
            Type::binary(
                Type::forall(
                    a,
                    Sort::Monotype,
                    Type::binary(
                        Type::ForallVar(ForallVar(a.0)),
                        Connective::Function,
                        Type::ForallVar(ForallVar(a.0)),
                    ),
                ),
                Connective::Function,
                result_ty.clone(),
            ),
        );

        let x = Ident(Intern::new("x".to_string()));
        let id_fn = Expr::function(x, Expr::Var(x));
        let (ty, p, _) = tcx.synth_expr_ty(Expr::app(apply_id, Spine::from_iter([id_fn])));
        assert_eq!(ty, result_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn map() {
        let tcx = TyCtx::new();
        let map = Ident(Intern::new("map".to_string()));
        let f = Ident(Intern::new("f".to_string()));
        let xs = Ident(Intern::new("xs".to_string()));
        let y = Ident(Intern::new("y".to_string()));
        let ys = Ident(Intern::new("ys".to_string()));

        let rec_map = Expr::Fix(
            map,
            Value::function(
                f,
                Expr::function(
                    xs,
                    Expr::case(
                        Expr::Var(xs),
                        Branches::from_iter([
                            Branch::from_iter([Pattern::Nil], Expr::Nil),
                            Branch::from_iter(
                                [Pattern::cons(Pattern::Var(y), Pattern::Var(ys))],
                                Expr::cons(
                                    Expr::app(Expr::Var(f), Spine::from_iter([Expr::Var(y)])),
                                    Expr::app(
                                        Expr::Var(map),
                                        Spine::from_iter([Expr::Var(f), Expr::Var(ys)]),
                                    ),
                                ),
                            ),
                        ]),
                    ),
                ),
            ),
        );

        let n = Ident(Intern::new("n".to_string()));
        let alpha = Ident(Intern::new("α".to_string()));
        let beta = Ident(Intern::new("β".to_string()));
        let anno_ty = Type::forall(
            n,
            Sort::Natural,
            Type::forall(
                alpha,
                Sort::Monotype,
                Type::forall(
                    beta,
                    Sort::Monotype,
                    Type::binary(
                        Type::binary(
                            Type::ForallVar(ForallVar(alpha.0)),
                            Connective::Function,
                            Type::ForallVar(ForallVar(beta.0)),
                        ),
                        Connective::Function,
                        Type::binary(
                            Type::vec(
                                Term::ForallVar(ForallVar(n.0)),
                                Type::ForallVar(ForallVar(alpha.0)),
                            ),
                            Connective::Function,
                            Type::vec(
                                Term::ForallVar(ForallVar(n.0)),
                                Type::ForallVar(ForallVar(beta.0)),
                            ),
                        ),
                    ),
                ),
            ),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(rec_map, anno_ty.clone()));
        assert_eq!(ty, anno_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn zip() {
        let tcx = TyCtx::new();
        let zip = Ident(Intern::new("zip".to_string()));
        let p = Ident(Intern::new("p".to_string()));
        let x = Ident(Intern::new("x".to_string()));
        let xs = Ident(Intern::new("xs".to_string()));
        let y = Ident(Intern::new("y".to_string()));
        let ys = Ident(Intern::new("ys".to_string()));

        let rec_zip = Expr::Fix(
            zip,
            Value::function(
                p,
                Expr::case(
                    Expr::Var(p),
                    Branches::from_iter([
                        Branch::from_iter([Pattern::pair(Pattern::Nil, Pattern::Nil)], Expr::Nil),
                        Branch::from_iter(
                            [Pattern::pair(
                                Pattern::cons(Pattern::Var(x), Pattern::Var(xs)),
                                Pattern::cons(Pattern::Var(y), Pattern::Var(ys)),
                            )],
                            Expr::cons(
                                Expr::pair(Expr::Var(x), Expr::Var(y)),
                                Expr::app(
                                    Expr::Var(zip),
                                    Spine::from_iter([Expr::pair(Expr::Var(xs), Expr::Var(ys))]),
                                ),
                            ),
                        ),
                    ]),
                ),
            ),
        );

        let n = Ident(Intern::new("n".to_string()));
        let alpha = Ident(Intern::new("α".to_string()));
        let beta = Ident(Intern::new("β".to_string()));
        let anno_ty = Type::forall(
            n,
            Sort::Natural,
            Type::forall(
                alpha,
                Sort::Monotype,
                Type::forall(
                    beta,
                    Sort::Monotype,
                    Type::binary(
                        Type::binary(
                            Type::vec(
                                Term::ForallVar(ForallVar(n.0)),
                                Type::ForallVar(ForallVar(alpha.0)),
                            ),
                            Connective::Product,
                            Type::vec(
                                Term::ForallVar(ForallVar(n.0)),
                                Type::ForallVar(ForallVar(beta.0)),
                            ),
                        ),
                        Connective::Function,
                        Type::vec(
                            Term::ForallVar(ForallVar(n.0)),
                            Type::binary(
                                Type::ForallVar(ForallVar(alpha.0)),
                                Connective::Product,
                                Type::ForallVar(ForallVar(beta.0)),
                            ),
                        ),
                    ),
                ),
            ),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(rec_zip, anno_ty.clone()));
        assert_eq!(ty, anno_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn basic_exists() {
        let tcx = TyCtx::new();
        let k = Ident(Intern::new("k".to_string()));
        let anno_ty = Type::exists(
            k,
            Sort::Natural,
            Type::vec(Term::ExistsVar(ExistsVar(k.0)), Type::Unit),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(Expr::Nil, anno_ty.clone()));
        assert_eq!(ty, anno_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn case_exists() {
        let tcx = TyCtx::new();
        let k = Ident(Intern::new("k".to_string()));
        let anno_ty = Type::exists(
            k,
            Sort::Natural,
            Type::vec(Term::ExistsVar(ExistsVar(k.0)), Type::Unit),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(
            Expr::case(
                Expr::Unit,
                Branches::from_iter([
                    Branch::from_iter([Pattern::Wildcard], Expr::Nil),
                    Branch::from_iter([Pattern::Unit], Expr::cons(Expr::Unit, Expr::Nil)),
                ]),
            ),
            anno_ty.clone(),
        ));
        assert_eq!(ty, anno_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn maybe_pop_front() {
        let tcx = TyCtx::new();
        let p = Ident(Intern::new("p".to_string()));
        let xs = Ident(Intern::new("xs".to_string()));
        let y = Ident(Intern::new("y".to_string()));
        let ys = Ident(Intern::new("ys".to_string()));

        let maybe_pop_front = Expr::function(
            p,
            Expr::function(
                xs,
                Expr::case(
                    Expr::Var(xs),
                    Branches::from_iter([
                        Branch::from_iter([Pattern::Nil], Expr::Nil),
                        // TODO: shadowing makes the context not well formed?
                        Branch::from_iter(
                            [Pattern::cons(Pattern::Var(y), Pattern::Var(ys))],
                            Expr::case(
                                Expr::app(Expr::Var(p), Spine::from_iter([Expr::Var(y)])),
                                Branches::from_iter([
                                    Branch::from_iter(
                                        [Pattern::inj1(Pattern::Wildcard)],
                                        Expr::Var(ys),
                                    ),
                                    Branch::from_iter(
                                        [Pattern::inj2(Pattern::Wildcard)],
                                        Expr::cons(Expr::Var(y), Expr::Var(ys)),
                                    ),
                                ]),
                            ),
                        ),
                    ]),
                ),
            ),
        );

        let n = Ident(Intern::new("n".to_string()));
        let alpha = Ident(Intern::new("α".to_string()));
        let k = Ident(Intern::new("k".to_string()));
        let anno_ty = Type::forall(
            n,
            Sort::Natural,
            Type::forall(
                alpha,
                Sort::Monotype,
                Type::binary(
                    Type::binary(
                        Type::ForallVar(ForallVar(alpha.0)),
                        Connective::Function,
                        Type::binary(Type::Unit, Connective::Sum, Type::Unit),
                    ),
                    Connective::Function,
                    Type::binary(
                        Type::vec(
                            Term::ForallVar(ForallVar(n.0)),
                            Type::ForallVar(ForallVar(alpha.0)),
                        ),
                        Connective::Function,
                        Type::exists(
                            k,
                            Sort::Natural,
                            Type::vec(
                                Term::ExistsVar(ExistsVar(k.0)),
                                Type::ForallVar(ForallVar(alpha.0)),
                            ),
                        ),
                    ),
                ),
            ),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(maybe_pop_front, anno_ty.clone()));
        assert_eq!(ty, anno_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn nested_exists() {
        let tcx = TyCtx::new();
        let k = Ident(Intern::new("k".to_string()));
        let anno_ty = Type::exists(
            k,
            Sort::Natural,
            Type::vec(Term::ExistsVar(ExistsVar(k.0)), Type::Unit),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(
            Expr::cons(Expr::Unit, Expr::annotation(Expr::Nil, anno_ty.clone())),
            anno_ty.clone(),
        ));
        assert_eq!(ty, anno_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn filter() {
        let tcx = TyCtx::new();
        let filter = Ident(Intern::new("filter".to_string()));
        let p = Ident(Intern::new("p".to_string()));
        let xs = Ident(Intern::new("xs".to_string()));
        let y = Ident(Intern::new("y".to_string()));
        let ys = Ident(Intern::new("ys".to_string()));

        let tl = Expr::app(
            Expr::Var(filter),
            Spine::from_iter([Expr::Var(p), Expr::Var(ys)]),
        );
        let rec_filter = Expr::Fix(
            filter,
            Value::function(
                p,
                Expr::function(
                    xs,
                    Expr::case(
                        Expr::Var(xs),
                        Branches::from_iter([
                            Branch::from_iter([Pattern::Nil], Expr::Nil),
                            Branch::from_iter(
                                [Pattern::cons(Pattern::Var(y), Pattern::Var(ys))],
                                Expr::case(
                                    Expr::app(Expr::Var(p), Spine::from_iter([Expr::Var(y)])),
                                    Branches::from_iter([
                                        Branch::from_iter(
                                            [Pattern::inj1(Pattern::Wildcard)],
                                            tl.clone(),
                                        ),
                                        Branch::from_iter(
                                            [Pattern::inj2(Pattern::Wildcard)],
                                            Expr::cons(Expr::Var(y), tl),
                                        ),
                                    ]),
                                ),
                            ),
                        ]),
                    ),
                ),
            ),
        );

        let n = Ident(Intern::new("n".to_string()));
        let alpha = Ident(Intern::new("α".to_string()));
        let k = Ident(Intern::new("k".to_string()));
        let anno_ty = Type::forall(
            n,
            Sort::Natural,
            Type::forall(
                alpha,
                Sort::Monotype,
                Type::binary(
                    Type::binary(
                        Type::ForallVar(ForallVar(alpha.0)),
                        Connective::Function,
                        Type::binary(Type::Unit, Connective::Sum, Type::Unit),
                    ),
                    Connective::Function,
                    Type::binary(
                        Type::vec(
                            Term::ForallVar(ForallVar(n.0)),
                            Type::ForallVar(ForallVar(alpha.0)),
                        ),
                        Connective::Function,
                        Type::exists(
                            k,
                            Sort::Natural,
                            Type::vec(
                                Term::ExistsVar(ExistsVar(k.0)),
                                Type::ForallVar(ForallVar(alpha.0)),
                            ),
                        ),
                    ),
                ),
            ),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(rec_filter, anno_ty.clone()));
        assert_eq!(ty, anno_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn nested_forall() {
        let f = Ident(Intern::new("f".to_string()));
        let x = Ident(Intern::new("x".to_string()));
        let y = Ident(Intern::new("y".to_string()));
        let alpha = Ident(Intern::new("α".to_string()));
        let beta = Ident(Intern::new("β".to_string()));

        let x_ty = Type::forall(
            beta,
            Sort::Monotype,
            Type::binary(
                Type::ForallVar(ForallVar(beta.0)),
                Connective::Function,
                Type::ForallVar(ForallVar(beta.0)),
            ),
        );
        let tcx = TyCtx::new().extend(Entry::ExprTyping(x, x_ty.clone(), Principality::Principal));

        let res_ty = Type::binary(Type::Unit, Connective::Function, Type::Unit);
        let function = Expr::annotation(
            Expr::function(
                f,
                Expr::function(y, Expr::app(Expr::Var(f), Spine::from_iter([Expr::Var(y)]))),
            ),
            Type::forall(
                alpha,
                Sort::Monotype,
                Type::binary(
                    x_ty,
                    Connective::Function,
                    Type::binary(
                        Type::ForallVar(ForallVar(alpha.0)),
                        Connective::Function,
                        Type::ForallVar(ForallVar(alpha.0)),
                    ),
                ),
            ),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(
            Expr::app(function, Spine::from_iter([Expr::Var(x)])),
            res_ty.clone(),
        ));
        assert_eq!(ty, res_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn nested_pattern() {
        let x = Ident(Intern::new("x".to_string()));
        let y = Ident(Intern::new("y".to_string()));
        let tcx = TyCtx::new().extend(Entry::ExprTyping(
            x,
            Type::binary(
                Type::binary(Type::Unit, Connective::Product, Type::Unit),
                Connective::Sum,
                Type::binary(Type::Unit, Connective::Sum, Type::Unit),
            ),
            Principality::Principal,
        ));
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(
            Expr::case(
                Expr::Var(x),
                Branches::from_iter([
                    Branch::from_iter(
                        [Pattern::inj1(Pattern::pair(
                            Pattern::Wildcard,
                            Pattern::Var(y),
                        ))],
                        Expr::Var(y),
                    ),
                    Branch::from_iter(
                        [Pattern::inj2(Pattern::inj2(Pattern::Var(y)))],
                        Expr::Var(y),
                    ),
                    Branch::from_iter(
                        [Pattern::inj2(Pattern::inj1(Pattern::Wildcard))],
                        Expr::Unit,
                    ),
                ]),
            ),
            Type::Unit,
        ));
        assert_eq!(ty, Type::Unit);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn exists_vec_ty() {
        let t = Ident(Intern::new("T".to_string()));
        let tcx = TyCtx::new();

        let anno_ty = Type::exists(
            t,
            Sort::Monotype,
            Type::vec(Term::succ(Term::Zero), Type::ExistsVar(ExistsVar(t.0))),
        );
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(
            Expr::case(
                Expr::annotation(
                    Expr::inj1(Expr::Unit),
                    Type::binary(Type::Unit, Connective::Sum, Type::Unit),
                ),
                Branches::from_iter([
                    Branch::from_iter(
                        [Pattern::inj1(Pattern::Wildcard)],
                        Expr::cons(Expr::Unit, Expr::Nil),
                    ),
                    Branch::from_iter(
                        [Pattern::Wildcard],
                        Expr::cons(Expr::pair(Expr::Unit, Expr::Unit), Expr::Nil),
                    ),
                ]),
            ),
            anno_ty.clone(),
        ));
        assert_eq!(ty, anno_ty);
        assert_eq!(p, Principality::Principal);
    }

    #[test]
    fn exists_vec_head() {
        let x = Ident(Intern::new("x".to_string()));
        let xs = Ident(Intern::new("xs".to_string()));
        let t = Ident(Intern::new("T".to_string()));
        let tcx = TyCtx::new().extend(Entry::ExprTyping(
            xs,
            Type::exists(
                t,
                Sort::Monotype,
                Type::vec(Term::succ(Term::Zero), Type::ExistsVar(ExistsVar(t.0))),
            ),
            Principality::Principal,
        ));

        let res_ty = Type::exists(t, Sort::Monotype, Type::ExistsVar(ExistsVar(t.0)));
        let (ty, p, _) = tcx.synth_expr_ty(Expr::annotation(
            Expr::case(
                Expr::Var(xs),
                Branches::from_iter([Branch::from_iter(
                    [Pattern::cons(Pattern::Var(x), Pattern::Wildcard)],
                    Expr::Var(x),
                )]),
            ),
            res_ty.clone(),
        ));
        assert_eq!(ty, res_ty);
        assert_eq!(p, Principality::Principal);
    }
}
