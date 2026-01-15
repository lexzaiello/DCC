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

def assert_nat_plus : Bool :=
  ((· == 101) <$> ·) <$> (test_nat_plus_nat 1 100)
    |> ((·.getD false) <$> ·)
    |> (·.toOption.getD false)

def main := lspecIO $ .ofList [
    ("Nat", [test "Nat.plus" assert_nat_plus]),
  ]
