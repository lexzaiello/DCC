import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
(:: (:: curry f) x) = (:: f x)

(:: (:: then_cons x) y) = (:: x y)
-/
def curry : Expr := then_cons

/-
See an example in Church.lean
-/

def example_curry : Except Error Expr :=
  let my_f := const

  -- const takes two arguments:
