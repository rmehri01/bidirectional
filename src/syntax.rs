use std::collections::VecDeque;

use internment::Intern;

use crate::{pat::Branches, ty::Type};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ident(pub Intern<String>);

#[derive(Debug, Clone)]
pub enum Expr {
    Var(Ident),
    Unit,
    Function(Ident, Box<Expr>),
    App(Box<Expr>, Spine),
    Fix(Ident, Value),
    Annotation(Box<Expr>, Type),
    Pair(Box<Expr>, Box<Expr>),
    Inj1(Box<Expr>),
    Inj2(Box<Expr>),
    Case(Box<Expr>, Branches),
    Nil,
    Cons(Box<Expr>, Box<Expr>),
}

impl Expr {
    /// e chk-I, `self` is a checked introduction form.
    pub fn is_intro_form(&self) -> bool {
        matches!(
            self,
            Self::Function(..)
                | Self::Unit
                | Self::Pair(..)
                | Self::Inj1(_)
                | Self::Inj2(_)
                | Self::Nil
                | Self::Cons(..)
        )
    }

    /// Returns `true` if the expr is [`Case`].
    ///
    /// [`Case`]: Expr::Case
    #[must_use]
    pub fn is_case(&self) -> bool {
        matches!(self, Self::Case(..))
    }

    pub fn function(ident: Ident, body: Self) -> Self {
        Self::Function(ident, Box::new(body))
    }

    pub fn app(function: Self, spine: Spine) -> Self {
        Self::App(Box::new(function), spine)
    }

    pub fn annotation(expr: Self, ty: Type) -> Self {
        Self::Annotation(Box::new(expr), ty)
    }

    pub fn pair(e1: Self, e2: Self) -> Self {
        Self::Pair(Box::new(e1), Box::new(e2))
    }

    pub fn inj1(expr: Self) -> Self {
        Self::Inj1(Box::new(expr))
    }

    pub fn inj2(expr: Self) -> Self {
        Self::Inj2(Box::new(expr))
    }

    pub fn case(expr: Self, branches: Branches) -> Self {
        Self::Case(Box::new(expr), branches)
    }

    pub fn cons(hd: Self, tl: Self) -> Self {
        Self::Cons(Box::new(hd), Box::new(tl))
    }
}

#[derive(Debug, Clone)]
pub struct Spine(pub VecDeque<Expr>);

impl Spine {
    pub fn from_iter(exprs: impl IntoIterator<Item = Expr>) -> Self {
        Self(VecDeque::from_iter(exprs))
    }
}

// TODO: combine with expr?
#[derive(Debug, Clone)]
pub enum Value {
    Var(Ident),
    Unit,
    Function(Ident, Box<Expr>),
    Fix(Ident, Box<Value>),
    Annotation(Box<Value>, Type),
    Pair(Box<Value>, Box<Value>),
    Inj1(Box<Value>),
    Inj2(Box<Value>),
    Nil,
    Cons(Box<Value>, Box<Value>),
}

impl Value {
    pub fn into_expr(self) -> Expr {
        match self {
            Self::Var(v) => Expr::Var(v),
            Self::Unit => Expr::Unit,
            Self::Function(x, e) => Expr::Function(x, e),
            Self::Fix(x, v) => Expr::Fix(x, *v),
            Self::Annotation(v, t) => Expr::annotation(v.into_expr(), t),
            Self::Pair(v1, v2) => Expr::pair(v1.into_expr(), v2.into_expr()),
            Self::Inj1(v) => Expr::inj1(v.into_expr()),
            Self::Inj2(v) => Expr::inj2(v.into_expr()),
            Self::Nil => Expr::Nil,
            Self::Cons(hd, tl) => Expr::cons(hd.into_expr(), tl.into_expr()),
        }
    }

    pub fn function(ident: Ident, body: Expr) -> Self {
        Self::Function(ident, Box::new(body))
    }
}
