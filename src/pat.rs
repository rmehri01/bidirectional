use crate::syntax::{Expr, Ident};

pub struct Branches(Vec<Branch>);

struct Branch(Vec<Pattern>, Expr);

enum Pattern {
    Var(Ident),
    Pair(Box<Pattern>, Box<Pattern>),
    Inj1(Box<Pattern>),
    Inj2(Box<Pattern>),
    Nil,
    Cons(Box<Pattern>, Box<Pattern>),
}
