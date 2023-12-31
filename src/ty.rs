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
    /// Returns `true` if the type is [`Forall`].
    ///
    /// [`Forall`]: Type::Forall
    #[must_use]
    pub fn is_forall(&self) -> bool {
        matches!(self, Self::Forall(..))
    }

    /// Returns `true` if the type is [`Exists`].
    ///
    /// [`Exists`]: Type::Exists
    #[must_use]
    pub fn is_exists(&self) -> bool {
        matches!(self, Self::Exists(..))
    }

    /// Returns `true` if the type is either [`Forall`] or [`Exists`].
    ///
    /// [`Forall`]: Type::Forall
    /// [`Exists`]: Type::Exists
    #[must_use]
    pub fn is_quantifier(&self) -> bool {
        self.is_forall() || self.is_exists()
    }

    pub fn polarity(&self) -> Polarity {
        match self {
            Self::Forall(_, _, _) => Polarity::Negative,
            Self::Exists(_, _, _) => Polarity::Positive,
            _ => Polarity::None,
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
                    if bound_vars.contains(var) {
                        HashSet::new()
                    } else {
                        HashSet::from([*var])
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
                Type::Vec(term, ty) => {
                    let mut free_vars = term.free_exists_vars();
                    free_vars.retain(|e| !bound_vars.contains(e));
                    free_vars.extend(free_vars_with_bound(ty, bound_vars));
                    free_vars
                }
            }
        }

        free_vars_with_bound(self, HashSet::new())
    }

    // NOTE: This is not capture avoiding, just normal substitution. We could probably
    //       get around this with De Bruijn indices or a better way of doing alpha-equivalence.
    /// [α̂/α]A, substitute all instances of `this` for `that` in `self`.
    pub fn substitute_forall(&mut self, this: ForallVar, that: ExistsVar) {
        match self {
            Self::Unit => {}
            Self::ExistsVar(_) => {}
            Self::ForallVar(var) => {
                if *var == this {
                    *self = Self::ExistsVar(that);
                }
            }
            Self::Binary(l, _, r) => {
                l.substitute_forall(this, that);
                r.substitute_forall(this, that);
            }
            Self::Forall(ident, _, body) => {
                if ident.0 != this.0 {
                    body.substitute_forall(this, that);
                }
            }
            Self::Exists(_, _, body) => body.substitute_forall(this, that),
            Self::Implies(Proposition(t1, t2), ty) | Self::With(ty, Proposition(t1, t2)) => {
                t1.substitute_forall(this, that);
                t2.substitute_forall(this, that);
                ty.substitute_forall(this, that);
            }
            Self::Vec(term, ty) => {
                term.substitute_forall(this, that);
                ty.substitute_forall(this, that);
            }
        }
    }

    /// [α̂/α]A, substitute all instances of `this` for `that` in `self`.
    pub fn substitute_exists(&mut self, this: ExistsVar, that: ExistsVar) {
        match self {
            Self::Unit => {}
            Self::ForallVar(_) => {}
            Self::ExistsVar(var) => {
                if *var == this {
                    *self = Self::ExistsVar(that);
                }
            }
            Self::Binary(l, _, r) => {
                l.substitute_exists(this, that);
                r.substitute_exists(this, that);
            }
            Self::Exists(ident, _, body) => {
                if ident.0 != this.0 {
                    body.substitute_exists(this, that);
                }
            }
            Self::Forall(_, _, body) => body.substitute_exists(this, that),
            Self::Implies(Proposition(t1, t2), ty) | Self::With(ty, Proposition(t1, t2)) => {
                t1.substitute_exists(this, that);
                t2.substitute_exists(this, that);
                ty.substitute_exists(this, that);
            }
            Self::Vec(term, ty) => {
                term.substitute_exists(this, that);
                ty.substitute_exists(this, that);
            }
        }
    }

    pub fn binary(a: Self, connective: Connective, b: Self) -> Self {
        Self::Binary(Box::new(a), connective, Box::new(b))
    }

    pub fn forall(ident: Ident, sort: Sort, ty: Self) -> Self {
        Self::Forall(ident, sort, Box::new(ty))
    }

    pub fn exists(ident: Ident, sort: Sort, ty: Self) -> Self {
        Self::Exists(ident, sort, Box::new(ty))
    }

    pub fn implies(prop: Proposition, ty: Self) -> Self {
        Self::Implies(prop, Box::new(ty))
    }

    pub fn with(ty: Self, prop: Proposition) -> Self {
        Self::With(Box::new(ty), prop)
    }

    pub fn vec(term: Term, ty: Self) -> Self {
        Self::Vec(term, Box::new(ty))
    }
}

impl TryFrom<Term> for Type {
    type Error = String;

    fn try_from(term: Term) -> Result<Self, Self::Error> {
        match term {
            Term::Zero | Term::Succ(_) => Err(format!("Term {term:?} is not a valid monotype.")),
            Term::Unit => Ok(Self::Unit),
            Term::ForallVar(f) => Ok(Self::ForallVar(f)),
            Term::ExistsVar(e) => Ok(Self::ExistsVar(e)),
            Term::Binary(a, op, b) => {
                Ok(Self::binary(Self::try_from(*a)?, op, Self::try_from(*b)?))
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sort {
    Natural,
    Monotype,
}

/// Terms and monotypes share the same grammar but are distinguished by [`Sort`].
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

    /// [α̂/α]A, substitute all instances of `this` for `that` in `self`.
    pub fn substitute_forall(&mut self, this: ForallVar, that: ExistsVar) {
        match self {
            Self::Zero => {}
            Self::Succ(t) => t.substitute_forall(this, that),
            Self::Unit => {}
            Self::ExistsVar(_) => {}
            Self::ForallVar(var) => {
                if *var == this {
                    *self = Self::ExistsVar(that);
                }
            }
            Self::Binary(l, _, r) => {
                l.substitute_forall(this, that);
                r.substitute_forall(this, that);
            }
        }
    }

    /// [α̂/α]A, substitute all instances of `this` for `that` in `self`.
    pub fn substitute_exists(&mut self, this: ExistsVar, that: ExistsVar) {
        match self {
            Self::Zero => {}
            Self::Succ(t) => t.substitute_exists(this, that),
            Self::Unit => {}
            Self::ForallVar(_) => {}
            Self::ExistsVar(var) => {
                if *var == this {
                    *self = Self::ExistsVar(that);
                }
            }
            Self::Binary(l, _, r) => {
                l.substitute_exists(this, that);
                r.substitute_exists(this, that);
            }
        }
    }

    pub fn succ(term: Self) -> Self {
        Self::Succ(Box::new(term))
    }

    pub fn binary(a: Self, connective: Connective, b: Self) -> Self {
        Self::Binary(Box::new(a), connective, Box::new(b))
    }
}

impl TryFrom<Type> for Term {
    type Error = String;

    fn try_from(ty: Type) -> Result<Self, Self::Error> {
        match ty {
            Type::Forall(_, _, _)
            | Type::Exists(_, _, _)
            | Type::Implies(_, _)
            | Type::With(_, _)
            | Type::Vec(_, _) => Err(format!("Type {ty:?} is not a valid monotype.")),
            Type::Unit => Ok(Self::Unit),
            Type::ForallVar(f) => Ok(Self::ForallVar(f)),
            Type::ExistsVar(e) => Ok(Self::ExistsVar(e)),
            Type::Binary(a, op, b) => {
                Ok(Self::binary(Self::try_from(*a)?, op, Self::try_from(*b)?))
            }
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

impl Principality {
    /// Returns `true` if the principality is [`Principal`].
    ///
    /// [`Principal`]: Principality::Principal
    #[must_use]
    pub fn is_principal(self) -> bool {
        matches!(self, Self::Principal)
    }

    /// Returns `true` if the principality is [`NonPrincipal`].
    ///
    /// [`NonPrincipal`]: Principality::NonPrincipal
    #[must_use]
    pub fn is_non_principal(self) -> bool {
        matches!(self, Self::NonPrincipal)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Polarity {
    Positive,
    Negative,
    None,
}

impl Polarity {
    /// Returns `true` if the polarity is [`Positive`].
    ///
    /// [`Positive`]: Polarity::Positive
    #[must_use]
    pub fn is_positive(self) -> bool {
        matches!(self, Self::Positive)
    }

    /// Returns `true` if the polarity is [`Negative`].
    ///
    /// [`Negative`]: Polarity::Negative
    #[must_use]
    pub fn is_negative(self) -> bool {
        matches!(self, Self::Negative)
    }

    pub fn is_non_positive(self) -> bool {
        !self.is_positive()
    }

    pub fn is_non_negative(self) -> bool {
        !self.is_negative()
    }

    pub fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Positive, _) => Self::Positive,
            (Self::Negative, _) => Self::Negative,
            (Self::None, Self::Positive) => Self::Positive,
            (Self::None, Self::Negative) => Self::Negative,
            (Self::None, Self::None) => Self::Negative,
        }
    }
}

static NEXT_ID: AtomicUsize = AtomicUsize::new(0);

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
