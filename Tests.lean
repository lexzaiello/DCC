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
  try_step_n run max_steps (:: apply (:: nat.plus (:: m' n')))
    >>= (pure ∘ Nat'.to_nat)

def assert_nat_plus (m n : ℕ) (expected : ℕ) (max_steps : ℕ := 100) : Bool :=
  ((· == expected) <$> ·) <$> (test_nat_plus_nat m n max_steps)
    |> ((·.getD false) <$> ·)
    |> (·.toOption.getD false)



def main := lspecIO $ .ofList [
    ("Nat", [test "Nat.plus 1 100 is 101" (assert_nat_plus 1 100 101 100)
      , test "Nat.plus 20 19 is 39" (assert_nat_plus 20 19 39 5000)]),
    ("List", [test "List.get_n'" ((try_step_n run 100 (:: apply (:: (:: apply (:: list.get_n' (:: (symbol "succ") (symbol "zero")))) (:: (symbol "test") (:: (symbol "b") nil))))) == Except.ok (symbol "b"))])
  ]
