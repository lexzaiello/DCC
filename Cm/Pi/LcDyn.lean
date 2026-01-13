import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.LcAst
import Cm.Pi.Nat
import Cm.Pi.List

open Expr

/-
Lambda calculus with De Bruijn-indexed arguments.

(:: apply (:: lam (:: apply (:: var zero))) (symbol "hello world"))
= symbol "hello world"
-/

/-
De Bruijn indices correspond to variable lookups in the context.
-/
def var : Expr :=
  .cons both (:: (quote list.get_n) (:: both (:: (quote both) (:: const (quote id)))))

/-
A lambda passes its future context onto its child.
It creates the context by prefixing the substitution with (:: (symbol "x") _)
-/
/-def lam : Expr :=
  let my_bdy := :: π (:: nil id)

  let future_sub := quote <| :: π (:: id nil)
  -/
