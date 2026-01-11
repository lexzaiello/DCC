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

/-
:: apply (:: f (:: x y)) = (:: (:: (:: apply_partial₂ f) x) y)
-/
def apply_partial₂ : Expr :=
  let x := (quote (:: both (:: (quote id) id))) -- drops f, then drops y later and just returns x
  let y := (quote (quote id)) -- drops f and x
  let xy := (:: x y) -- x and y arguments
  let f := (:: both (:: (quote const) (:: both (:: (quote const) id)))) -- drops x and y
  let app_at_end := (quote (quote (quote apply))) -- drops f, x, and y

  -- quotations are inert, and we skip over them. useful for "control flow"
  let both_x := (quote both) -- dropped by f, left for x
  let both_y := (quote (quote both)) -- dropped by x, left for y

  (:: both (:: (quote both) (:: both (:: app_at_end (:: both (:: (quote both) (:: both (:: f (:: both xy)))))))))

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
curry = prepend?

curry f = (:: then_cons f)

curry f = both_partial (const (:: then_cons f)) then_cons

curry 
-/
def curry : Expr :=
  


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
