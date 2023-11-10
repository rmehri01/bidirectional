# ↔️ Bidirectional Typechecking

This is an implementation of the 2019 POPL paper, [Sound and Complete Bidirectional Typechecking for Higher-Rank Polymorphism with Existentials and Indexed Types](https://www.cl.cam.ac.uk/~nk480/gadt.pdf) by Dunfield and Krishnaswami.

## About

Bidirectional typechecking is a technique for making typing rules syntax-directed where you switch between type synthesis and type checking. This tends to be relatively straightforward to implement, produces good error messages, 
usually just requires annotation at the top level, and scales much more nicely to advanced type system features than other systems such as Damas–Hindley–Milner for example. This paper in particular explores a type system that 
supports existential and indexed types, allowing for implementing [GADTs](https://en.wikipedia.org/wiki/Generalized_algebraic_data_type) such as length-indexed vectors, as well as functions over them that correctly check exhaustiveness of patterns:

```agda
data Vec : Nat → Type → Type where
  [] : A → Vec 0 A
  (::) : A → Vec n A → Vec (succ n) A

head : ∀n,A. Vec (succ n) A → A
head (x :: xs) = x
```

I actually got it to typecheck the `map`, `zip`, and `filter` examples from the paper, along with a few other tests with just a few modifications to the algorithm, which seems like a promising start! 😄

```ocaml
rec map. λf. λxs. case(xs, [] ⇒ []
                         | y :: ys ⇒ (f y) :: map f ys)
: ∀n : ℕ. ∀α : ⋆. ∀β : ⋆. (α → β) → Vec n α → Vec n β

rec zip. λp. case(p, ([], []) ⇒ []
                   | (x :: xs, y :: ys) ⇒ (x, y) :: zip (xs, ys))
: ∀n : ℕ. ∀α : ⋆. ∀β : ⋆. (Vec n α × Vec n β) → Vec n (α × β)

rec filter. λp. λxs. case(xs, [] ⇒ []
                            | x :: xs ⇒ let tl = filter p xs in
                                             case(p x, inj1 _ ⇒ tl
                                                     | inj2 _ ⇒ x :: tl))
: ∀n : ℕ. ∀α : ⋆. (α → 1 + 1) → Vec n α → ∃k : ℕ. Vec k α
```

If you want to find out more, I highly recommend the paper or talk by David Christiansen as a starting point: https://davidchristiansen.dk/tutorials/bidirectional.pdf.

## Future Work

- I tried to stick relatively close to the paper, so this definitely isn't the most efficient implementation.
  - For the AST it would probably be better to use `Rc` instead of `Box` or to use an arena instead and for the context, I think it can just be mutable instead of being threaded everywhere.
  - There is a bit of duplication with `Type`/`Term`, `Expr`/`Value`, and the existential and forall variables.
- Using De Bruijn indices or a library such as [moniker](https://github.com/brendanzab/moniker) or [unbound](https://github.com/sweirich/replib) to handle alpha-equivalence properly.
- Adding to the synthesis for common types to reduce the number of annotations.
- Extending the type system, for example with type constructors, recursive types, type classes, etc.
