use std::{
    collections::HashSet,
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::syntax::Ident;

#[derive(Debug, Clone)]
pub enum Type {
    Unit,
    ForallVar(ForallVar),
    ExistsVar(ExistsVar),
    Binary(Box<Type>, Connective, Box<Type>),
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
    Binary(Box<Term>, Connective, Box<Term>),
}

impl Term {
    pub fn to_ty(self) -> Type {
        match self {
            // TODO: should this be a panic? also in applying ctx to ty
            Self::Zero | Self::Succ(_) => panic!("cannot convert a Natural term to a type"),
            Self::Unit => Type::Unit,
            Self::ForallVar(f) => Type::ForallVar(f),
            Self::ExistsVar(e) => Type::ExistsVar(e),
            Self::Binary(a, op, b) => Type::Binary(Box::new(a.to_ty()), op, Box::new(b.to_ty())),
        }
    }

    pub fn free_forall_vars(&self) -> HashSet<ForallVar> {
        match self {
            Self::Zero | Self::Unit | Self::ExistsVar(_) => HashSet::new(),
            Self::Succ(t) => t.free_forall_vars(),
            Self::ForallVar(f) => HashSet::from([f.clone()]),
            Self::Binary(a, _, b) => {
                let mut fvs = a.free_forall_vars();
                fvs.extend(b.free_forall_vars());
                fvs
            }
        }
    }

    /// t1 # t2, produces true if `self` and `other` have incompatible head constructors
    pub fn clashes_with(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Zero, Self::Succ(_)) => true,
            (Self::Succ(_), Self::Zero) => true,
            (Self::Unit, Self::Binary(_, _, _)) => true,
            (Self::Binary(_, _, _), Self::Unit) => true,
            (Self::Binary(_, op1, _), Self::Binary(_, op2, _)) if op1 != op2 => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Connective {
    Function,
    Sum,
    Product,
}

#[derive(Debug, Clone)]
pub struct Proposition(pub Term, pub Term);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Principality {
    Principal,
    NotPrincipal,
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

static NEXT_ID: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ForallVar(pub String);

impl ForallVar {
    /// Generate a new, globally unique name.
    pub fn fresh(prefix: &str) -> Self {
        Self(format!(
            "'{prefix}{}",
            NEXT_ID.fetch_add(1, Ordering::SeqCst)
        ))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExistsVar(pub String);

impl ExistsVar {
    /// Generate a new, globally unique name.
    pub fn fresh(prefix: &str) -> Self {
        Self(format!(
            "'{prefix}{}",
            NEXT_ID.fetch_add(1, Ordering::SeqCst)
        ))
    }
}

#[derive(Debug, Clone)]
pub enum TyVar {
    Forall(ForallVar),
    Exists(ExistsVar),
}
