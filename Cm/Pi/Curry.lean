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
