use std::{
    collections::HashSet,
    sync::atomic::{AtomicUsize, Ordering},
};

use internment::Intern;

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
            Self::Forall(_, _, _)
            | Self::Exists(_, _, _)
            | Self::Implies(_, _)
            | Self::With(_, _)
            | Self::Vec(_, _) => panic!("cannot convert type to a term"),
            Self::Unit => Term::Unit,
            Self::ForallVar(f) => Term::ForallVar(f),
            Self::ExistsVar(e) => Term::ExistsVar(e),
            Self::Binary(a, op, b) => {
                Term::Binary(Box::new(a.to_term()), op, Box::new(b.to_term()))
            }
        }
    }

    pub fn free_exists_vars(&self) -> HashSet<ExistsVar> {
        // keep track of bound variables
        fn free_vars_with_bound(
            ty: &Type,
            mut bound_vars: HashSet<ExistsVar>,
        ) -> HashSet<ExistsVar> {
            match ty {
                Type::Unit => HashSet::new(),
                Type::ForallVar(_) => HashSet::new(),
                Type::ExistsVar(var) => {
                    if !bound_vars.contains(var) {
                        HashSet::from([*var])
                    } else {
                        HashSet::new()
                    }
                }
                Type::Binary(l, _, r) => free_vars_with_bound(l, bound_vars.clone())
                    .into_iter()
                    .chain(free_vars_with_bound(r, bound_vars))
                    .collect(),
                Type::Forall(_, _, ty) => free_vars_with_bound(ty, bound_vars),
                Type::Exists(ident, _, ty) => {
                    bound_vars.insert(ExistsVar(ident.0));
                    free_vars_with_bound(ty, bound_vars)
                }
                Type::Implies(_, ty) | Type::With(ty, _) => free_vars_with_bound(ty, bound_vars),
                Type::Vec(term, ty) => term
                    .free_exists_vars()
                    .into_iter()
                    .chain(free_vars_with_bound(ty, bound_vars))
                    .collect(),
            }
        }

        free_vars_with_bound(self, HashSet::new())
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
            Self::ForallVar(f) => HashSet::from([*f]),
            Self::Binary(a, _, b) => a
                .free_forall_vars()
                .into_iter()
                .chain(b.free_forall_vars())
                .collect(),
        }
    }

    pub fn free_exists_vars(&self) -> HashSet<ExistsVar> {
        match self {
            Self::Zero | Self::Unit | Self::ForallVar(_) => HashSet::new(),
            Self::Succ(t) => t.free_exists_vars(),
            Self::ExistsVar(e) => HashSet::from([*e]),
            Self::Binary(a, _, b) => a
                .free_exists_vars()
                .into_iter()
                .chain(b.free_exists_vars())
                .collect(),
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
    NonPrincipal,
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ForallVar(pub Intern<String>);

impl ForallVar {
    /// Generate a new, globally unique name.
    pub fn fresh(prefix: &str) -> Self {
        Self(Intern::new(format!(
            "'{prefix}{}",
            NEXT_ID.fetch_add(1, Ordering::SeqCst)
        )))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExistsVar(pub Intern<String>);

impl ExistsVar {
    /// Generate a new, globally unique name.
    pub fn fresh(prefix: &str) -> Self {
        Self(Intern::new(format!(
            "'{prefix}{}",
            NEXT_ID.fetch_add(1, Ordering::SeqCst)
        )))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TyVar {
    Forall(ForallVar),
    Exists(ExistsVar),
}
