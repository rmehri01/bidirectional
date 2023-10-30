use crate::{
    syntax::Ident,
    ty::{ExistsVar, ForallVar, Principality, Proposition, Sort, Term, TyVar, Type},
};

#[derive(Debug, Clone)]
pub struct TyCtx(Vec<Item>);

#[derive(Debug, Clone)]
pub enum Item {
    Decl(TyVar, Sort),
    ExprTyping(Ident, Type, Principality),
    SolvedExists(ExistsVar, Sort, Term),
    SolvedForall(ForallVar, Term),
    Marker(TyVar),
}

impl TyCtx {
    /// Extend `self` with the given `item`.
    pub fn extend(&self, item: Item) -> Self {
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
}
