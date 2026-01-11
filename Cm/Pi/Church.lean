import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util
import Cm.Pi.Curry

open Expr

/-
zero f x = x

This expects that at most two arguments are applied,
with no terminal nil value.
-/
def zero : Expr := :: π (:: (:: const id) id)

def example_zero_church : Except Error Expr :=
  let my_fn := :: const (symbol "const")
  let my_x  := :: const (symbol "intact")

  do_step run (:: apply (:: zero (:: my_fn my_x)))

#eval example_zero_church
  >>= step_apply

/-
Partially applying zero by only supplying one argument.
:: then_cons x = :: both (:: (:: const f) id)

(:: (:: then_cons f) x) = (:: f x)

For currying, we want the opposite.
We want append?

We want something we can do to our function to make it curry.

then_cons will cons the argument onto later arguments


(:: (:: then_cons (:: (:: then_cons f) x)) y) =

-/
/-def example_curry : Except Error Expr :=
  let my_fn := Expr.id
  let my_x  := (symbol "intact")

  -- curry twice
  -- so now we should be able to plug
  -- stuff in
  do_step run (:: apply (:: curry zero))
    >>= (fun c => do_step run (:: apply ))

#eval example_curry-/
