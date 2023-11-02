use std::collections::VecDeque;

use internment::Intern;

use crate::{pat::Branches, ty::Type};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ident(pub Intern<String>);

// TODO: should use rc?
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
}

// TODO: non empty?
#[derive(Debug, Clone)]
pub struct Spine(pub VecDeque<Expr>);

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
            Self::Annotation(v, t) => Expr::Annotation(Box::new(v.into_expr()), t),
            Self::Pair(v1, v2) => Expr::Pair(Box::new(v1.into_expr()), Box::new(v2.into_expr())),
            Self::Inj1(v) => Expr::Inj1(Box::new(v.into_expr())),
            Self::Inj2(v) => Expr::Inj2(Box::new(v.into_expr())),
            Self::Nil => Expr::Nil,
            Self::Cons(hd, tl) => Expr::Cons(Box::new(hd.into_expr()), Box::new(tl.into_expr())),
        }
    }
}
