use std::{
    collections::HashSet,
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::syntax::Ident;

#[derive(Debug, Clone, PartialEq)]
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

    pub fn to_term(self) -> Term {
        match self {
            // TODO: should this be a panic?
            Type::Forall(_, _, _)
            | Type::Exists(_, _, _)
            | Type::Implies(_, _)
            | Type::With(_, _)
            | Type::Vec(_, _) => panic!("cannot convert type to a term"),
            Self::Unit => Term::Unit,
            Self::ForallVar(f) => Term::ForallVar(f),
            Self::ExistsVar(e) => Term::ExistsVar(e),
            Self::Binary(a, op, b) => {
                Term::Binary(Box::new(a.to_term()), op, Box::new(b.to_term()))
            }
            Type::Unit => todo!(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sort {
    Natural,
    Monotype,
}

// TODO: combine terms and types?
/// Terms and monotypes share the same grammar but are distinguished by [Sort].
#[derive(Debug, Clone, PartialEq)]
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

    pub fn free_exists_vars(&self) -> HashSet<ExistsVar> {
        match self {
            Self::Zero | Self::Unit | Self::ForallVar(_) => HashSet::new(),
            Self::Succ(t) => t.free_exists_vars(),
            Self::ExistsVar(e) => HashSet::from([e.clone()]),
            Self::Binary(a, _, b) => {
                let mut fvs = a.free_exists_vars();
                fvs.extend(b.free_exists_vars());
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

/// An equation, t = t'.
#[derive(Debug, Clone, PartialEq)]
pub struct Proposition(pub Term, pub Term);

/// A principal type is a type such that all other types for this term
/// in this environment are an instance of the principal type.
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

// TODO: combine different var types
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyVar {
    Forall(ForallVar),
    Exists(ExistsVar),
}
