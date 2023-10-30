use crate::{pat::Branches, ty::Type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident(pub String);

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

// TODO: non empty?
#[derive(Debug, Clone)]
pub struct Spine(Vec<Expr>);

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
