import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Thought:
- partial apply? We have partial both. Why not both?
-/

/-
Expects the first both argument, but will wait for the second.

(:: (:: both_partial f) x) = (:: f x)
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
:: apply (:: f x) = (:: (:: apply_partial f) x)
-/
def apply_partial : Expr :=
  (:: both (:: (quote both) (:: both (:: (quote (quote apply)) (:: both (:: (quote both) (:: both (:: const (quote id)))))))))

def test_apply_partial : Except Error Expr := do
  let my_f := symbol "f"
  let my_x := symbol "x"

  do_step run (:: apply (:: (:: apply (:: apply_partial my_f)) my_x))

/-def test_apply_partial' : Except Error Expr := do
  -- this will only work with an :: x xs argument
  let my_f := π id id
  let -/

-- :: "f" "x"
#eval test_apply_partial

/-
curry = apply_partial?

apply_partial only works for one argument, which is confusing.
:: apply technically works for n-ary arguments.
More like one single massive array argument.
-/
--def curry : Expr :=
  


/-
Simple case: currying once.
(X × Y) → Z => X → (Y → Z)

This is just both_partial.
-/

/-
curr 0 f = nil
curr 1 f = 
-/
/-def curr : ℕ → Expr
  | .zero => id-/
