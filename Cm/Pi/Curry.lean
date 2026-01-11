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

This is essentially
-/
def curry_rest : Expr :=
  /-
    This works by 
  -/
  let mk_my_map := 
