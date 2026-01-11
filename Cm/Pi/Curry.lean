import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

def curry (n : ℕ) : Expr := then_cons

def example_then_cons_late_apply : Except Error Expr := do
  let my_data := symbol "hi"
  let my_l := :: (symbol "head") (:: (symbol "tail") nil)

  do_step run (:: apply (:: (:: then_cons my_data) my_l))

/-
See here:
- the inner (:: then_cons my_data) doesn't run,
since it needs an apply.

It has sufficient arguments.
-/
#eval example_then_cons_late_apply
