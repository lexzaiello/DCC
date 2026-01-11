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

/-
Partially applying zero by only supplying one argument.
-/
def example_curry : Except Error Expr :=
  let my_fn := :: const (symbol "const")
  let my_x  := :: const (symbol "intact")

  do_step run (:: apply (:: curry zero))

#eval example_curry
