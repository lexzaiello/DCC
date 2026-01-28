import Mathlib.Data.Nat.Notation

/-
Universe levels.
All combinators that take explicit type arguments
are universe polymoprhic.
-/
abbrev Level := ℕ

inductive Expr where
  | ty     : Level → Expr
   -- Cons can be partially applied, so it is a combinator
  | cons   : Expr
  | app    : Expr → Expr → Expr
   -- Nil "downgrades" a term to a type
   -- nil (α : Ty m) : α → Ty m
  | nil    : Expr
  -- Id is the I combinator in SK
  | id     : Level → Expr
  -- Dependent K combinator
  | const  : Level → Level → Expr
   -- Nondependent K. Closes the loop of type dependency.
  | const' : Level → Level → Expr
  -- forms a new sigma pair from (both f g x) ::[(f x), (g x)]
  -- but does not force application of (f x) (g x)
  -- combined with snd projection results in S
  | both   : Level → Level → Level → Expr
  -- Branch on def-eq. For practical applications.
  | eq     : Level → Expr

/-
to type-check function application:

two approaches:
- carry the found type -> this should not change the eval rule for sigma projection
  - allows later apps to use functions on them

we don't carry around the entire context.
assertions should assume they get passed just the next argument
without its type

f : ::[t_in, t_out]
x : α

Γ = ::[α, nil]

t_in Γ = α_type

Δ = ::[
-/
