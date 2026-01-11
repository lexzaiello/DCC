import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Expects the first both argument, but will wait for the second.

(:: (:: both_partial f) x) = (:: f x)

TODO: should this insert an apply by default? probably not.
-/
def both_partial : Expr :=
  (:: both (:: (quote both) (:: both (:: const (quote id)))))

def test_both_partial : Except Error Expr := do
  let my_f := symbol "f"
  let my_x := symbol "x"

  do_step run (:: apply (:: (:: apply (:: both_partial my_f)) my_x))

-- :: "f" "x"
#eval test_both_partial

/-
Currying:

- create a new function returning our function,
with whatever value substituted.

(:: f (:: x y)) = (:: (:: (:: curry f) x) y)

Each layer, just bubble up a partially applied

(:: both (const me))
-/
def curry : Expr :=
  -- (:: both (:: const (:: both (const me))) id)
  /-let me := (:: (:: const const) id)
  let mk_me := (:: both me)
  :: both (::
    (quote both)
    (:: both
      (:: both (::
        (quote const)
        (:: both (::
          (quote both)
          mk_me)))))
      (quote id))-/
