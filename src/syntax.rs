use crate::ty::Type;

pub struct Ident(String);

enum Expr {
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
struct Spine(Vec<Expr>);

struct Branches(Vec<Branch>);

// TODO: why list of pattern?
struct Branch(Vec<Pattern>, Expr);

enum Pattern {
    Var(Ident),
    Pair(Box<Pattern>, Box<Pattern>),
    Inj1(Box<Pattern>),
    Inj2(Box<Pattern>),
    Nil,
    Cons(Box<Pattern>, Box<Pattern>),
}

enum Value {
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
