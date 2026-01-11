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

Note:
we can chain then_cons witth multiple data

let c  := (:: apply (:: then_cons my_data))
let l := (:: apply (:: c my_l))
do_step run (:: apply (:: c l))

So, the function is the outermost (:: apply (:: then_cons f))

Then-cons left-associates.

(:: f (:: a (:: b c))) = (:: apply (:: apply (:: then_cons f)) (:: apply (:: (:: apply (:: then_cons a)) (:: (:: apply (:: then_cons b) c)))))

curry f = (:: both (:: const (:: apply (:: then_cons f)))

We could make a "run_curry" method that does all the apps?

Really, what I want is append.

(:: apply (:: apply (:: then_append f)) b) = (:: b f)

Doesn't seem particularly hard.

This is not particularly helpful.
HOWEVER, note that then_cons allows us to defer execution.


Currying with zero arguments is the same, I believe.
-/
--def curry : ℕ → Except Error Expr
--  | .zero => 

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
