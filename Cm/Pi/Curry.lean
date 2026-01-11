import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Curries a combinator expecting many arguments into a combinator
expecting one argument and the rest of the arguments in a list.

The first argument must already be known.

(:: apply (:: (:: curry_rest nil) (:: f (:: x nil)) (:: (symbol "a") (:: (symbol "b") nil))))

= (:: apply (:: f (:: x (:: (symbol "a") (:: (symbol "b") nil)))))

This is essentially set_tail_args'.
-/
def curry_rest : Expr :=
  /-
    We need to make a new both expression to do this.
    As in, we need to quote / insert it in the resulting expression.
    We assume that f and x are in scope like such, in order:

    π id id

    for each, we can make "append" methods:
    :: both (:: (:: const f) id)

    Our then_cons helper lets us give a value to prepend to a later list

    π then_cons then_cons
  -/
  let mk_my_map := 
