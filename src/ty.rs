use crate::syntax::Ident;

#[derive(Debug, Clone)]
pub enum Type {
    Unit,
    Function(Box<Type>, Box<Type>),
    Sum(Box<Type>, Box<Type>),
    ForallVar(ForallVar),
    ExistsVar(ExistsVar),
    Product(Box<Type>, Box<Type>),
    Forall(Ident, Sort, Box<Type>),
    Exists(Ident, Sort, Box<Type>),
    Implies(Proposition, Box<Type>),
    With(Box<Type>, Proposition),
    Vec(Term, Box<Type>),
}

impl Type {
    fn polarity(&self) -> Polarity {
        match self {
            Self::Forall(_, _, _) => Polarity::Negative,
            Self::Exists(_, _, _) => Polarity::Positive,
            _ => Polarity::None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sort {
    Natural,
    Monotype,
}

/// Terms and monotypes share the same grammar but are distinguished by [Sort].
#[derive(Debug, Clone)]
pub enum Term {
    Zero,
    Succ(Box<Term>),
    Unit,
    ForallVar(ForallVar),
    ExistsVar(ExistsVar),
    Function(Box<Term>, Box<Term>),
    Sum(Box<Term>, Box<Term>),
    Product(Box<Term>, Box<Term>),
}

impl Term {
    pub fn to_ty(self) -> Type {
        match self {
            // TODO: should this be a panic? also in applying ctx to ty
            Self::Zero | Self::Succ(_) => panic!("cannot convert a Natural term to a type"),
            Self::Unit => Type::Unit,
            Self::ForallVar(f) => Type::ForallVar(f),
            Self::ExistsVar(e) => Type::ExistsVar(e),
            Self::Function(a, b) => Type::Function(Box::new(a.to_ty()), Box::new(b.to_ty())),
            Self::Sum(a, b) => Type::Sum(Box::new(a.to_ty()), Box::new(b.to_ty())),
            Self::Product(a, b) => Type::Product(Box::new(a.to_ty()), Box::new(b.to_ty())),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Proposition(pub Term, pub Term);

pub enum Principality {
    Principal,
    NotPrincipal,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForallVar(String);
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExistsVar(String);

pub enum TyVar {
    Forall(ForallVar),
    Exists(ExistsVar),
}

#[derive(Debug, Clone, Copy)]
enum Polarity {
    Positive,
    Negative,
    None,
}

impl Polarity {
    fn non_positive(&self) -> bool {
        !matches!(self, Polarity::Positive)
    }

    fn non_negative(&self) -> bool {
        !matches!(self, Polarity::Negative)
    }

    fn join(&self, other: Self) -> Self {
        match (self, other) {
            (Polarity::Positive, _) => Polarity::Positive,
            (Polarity::Negative, _) => Polarity::Negative,
            (Polarity::None, Polarity::Positive) => Polarity::Positive,
            (Polarity::None, Polarity::Negative) => Polarity::Negative,
            (Polarity::None, Polarity::None) => Polarity::Negative,
        }
    }
}
