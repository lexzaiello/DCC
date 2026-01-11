import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Curries a combinator expecting many arguments into a combinator
expecting one argument and the rest of the arguments in a list.

The first argument must already be known.

(:: apply (:: curry_rest (:: f x)))
= (:: apply (:: f (:: x (:: (symbol "a") (:: (symbol "b") nil)))))

This is essentially set_tail_args'.
-/
def curry : Expr := then_cons

/-
Partially applying a function expecting two arguments.
For example, partially applying the church numeral zero.
-/
def example_curry : Except Error Expr :=
  
