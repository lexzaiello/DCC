import Dcc.Ast
import Dcc.Eval

/-
An "unsubstituted" Π expression is all the arguments and the codomain are prefixed by
a type combinator program.

M (Π α, β)

TySize M (m + 1)
PiSize α (n + 1)
PiSize β (n + 1)

PiSize (M (Π α, β))

A "substituted" Π expression is one where none of the arguments are prefixed by
a type combinator program.

Note that Π α, β is not well-typed.
B

pi_size is not total, since M Π reduction always results in another Π expression.
-/

inductive Expr.PiSize : Expr → ℕ → Prop
  | pi_app  : Expr.TySize f (m + 1)
    → Expr.PiSize (SK Π α, β) n
    → Expr.PiSize (SK (f (Π α, β))) ((m + 1) + n)
  | pi_atom : Expr.PiSize α m
    → Expr.PiSize β n
    → Expr.PiSize (SK Π α, β) (m + n)
