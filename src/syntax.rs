use crate::subtyping::Polarity;

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
    Case(Box<Expr>, BranchList),
    Nil,
    Cons(Box<Expr>, Box<Expr>),
}

// TODO: non empty?
struct Spine(Vec<Expr>);

// TODO: might want to inline this
struct BranchList(Vec<Branch>);

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForallVar(String);
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExistsVar(String);

pub enum TyVar {
    Forall(ForallVar),
    Exists(ExistsVar),
}

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

pub struct Proposition(pub Term, pub Term);

pub enum Principality {
    Principal,
    NotPrincipal,
}
