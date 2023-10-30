use crate::subtyping::Polarity;

// TODO: string might not be the best
enum Expr {
    Var(String),
    Unit,
    Function(String, Box<Expr>),
    App(Box<Expr>, Spine),
    Fix(String, Value),
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
    Var(String),
    Pair(Box<Pattern>, Box<Pattern>),
    Inj1(Box<Pattern>),
    Inj2(Box<Pattern>),
    Nil,
    Cons(Box<Pattern>, Box<Pattern>),
}

enum Value {
    Var(String),
    Unit,
    Function(String, Box<Expr>),
    Fix(String, Box<Value>),
    Annotation(Box<Value>, Type),
    Pair(Box<Value>, Box<Value>),
    Inj1(Box<Value>),
    Inj2(Box<Value>),
    Nil,
    Cons(Box<Value>, Box<Value>),
}

enum Type {
    Unit,
    Function(Box<Type>, Box<Type>),
    Sum(Box<Type>, Box<Type>),
    Var(String),
    Product(Box<Type>, Box<Type>),
    Forall(String, Sort, Box<Type>),
    Exists(String, Sort, Box<Type>),
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

enum Sort {
    Natural,
    Monotype,
}

/// Terms and monotypes share the same grammar but are distinguished by [Sort].
enum Term {
    Zero,
    Succ(Box<Term>),
    Unit,
    Var(String),
    Function(Box<Monotype>, Box<Monotype>),
    Sum(Box<Monotype>, Box<Monotype>),
    Product(Box<Monotype>, Box<Monotype>),
}

// TODO: make into its own type?
type Monotype = Term;

struct Proposition(Term, Term);
