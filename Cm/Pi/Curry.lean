import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Curries a combinator expecting many arguments into a combinator
expecting one argument and the rest of the arguments in a list.

The first argument must already be known.

(:: curry_rest nil) (:: f (:: x nil))
-/
def curry_rest : Expr :=
  -- this is just map_head, but we're inserting the specified argument.

  let insert_π := (:: const (:: π nil))

  -- our mapping function just prepends the x argument
  -- we can do this by 
  let mk_my_map := 
