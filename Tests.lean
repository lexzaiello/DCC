import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Error
import Cm.Pi.Infer
import Cm.Pi.List
import LSpec

open LSpec
open Expr

def test_nat_plus_nat (m n : ℕ) (max_steps : ℕ := 100) : Except Error (Option ℕ) := do
  let m' := Nat'.of_nat m
  let n' := Nat'.of_nat n
  try_step_n max_steps (:: apply (:: nat.plus (:: m' n')))
    >>= (pure ∘ Nat'.to_nat)

def assert_nat_plus (m n : ℕ) (expected : ℕ) (max_steps : ℕ := 100) : Bool :=
  ((· == expected) <$> ·) <$> (test_nat_plus_nat m n max_steps)
    |> ((·.getD false) <$> ·)
    |> (·.toOption.getD false)

def assert_out {α : Type} [BEq α] (expected : α) (actual : Except Error α) : Bool :=
  ((expected == ·) <$> actual).toOption.getD false

def run_assert (expected : Expr) (fn args : Expr) (n_steps : ℕ := 1000) : Bool :=
  assert_out expected (try_step_n n_steps (:: apply (:: fn args)))

def main := lspecIO $ .ofList [
    ("Nat", [test "Nat.plus 1 100 is 101" (assert_nat_plus 1 100 101 100)
      , test "Nat.plus 20 19 is 39" (assert_nat_plus 20 19 39 5000)]),
    ("List", [test "List.get_n'" (assert_out (symbol "b") (try_step_n 100 (:: apply (:: (:: apply (:: list.get_n' (:: (symbol "succ") (symbol "zero")))) (:: (symbol "test") (:: (symbol "b") nil))))))
    , test "List.reverse" (run_assert
      (:: (symbol "c") (:: (symbol "b") (:: (symbol "a") nil)))
      list.reverse
      (:: (symbol "a") (:: (symbol "b") (:: (symbol "c") nil))))
    , test "List.length" (run_assert
      (:: succ (:: succ zero))
      list.length
      (:: (symbol "a") (:: (symbol "b") nil)))])
  ]
