import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Applies the argument.
-/
def apply_now' : Expr :=
  :: both (:: (:: const apply) id)

def example_apply_now : Except Error Expr :=
  do_step run (:: apply (:: apply_now' (:: id (symbol "applied!"))))

#eval example_apply_now

/-
We can chain then_cons, but the last thing we run then_cons with
should be the function.

So, currying with one argument should be
let f' ← (:: apply (:: then_cons my_f))
(:: apply (:: f' my_arg))

Or, alternatively:

Hypothesis: just repeat this?
(:: apply (:: then_cons f))

Currying with zero arguments is the same, I believe.
-/
def curry : ℕ → Except Error Expr
  | .zero => 

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
