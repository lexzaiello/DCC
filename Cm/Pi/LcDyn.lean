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
  (:: both (:: (quote apply) (:: both (:: (quote list.get_n') id))))

def test_ctx := :: (symbol "a") (:: (symbol "discard") nil)

#eval do_step run (:: apply (:: var Nat'.zero))
#eval try_step_n run 100 (:: apply (:: (:: apply (:: var Nat'.zero)) test_ctx))

/-
A lambda passes its future context onto its child.
It creates the context by prefixing the substitution with (:: (symbol "x") _)
-/
/-def lam : Expr :=
  let my_bdy := :: π (:: nil id)

  let future_sub := quote <| :: π (:: id nil)
  -/
