import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Natural numbers, featuring pattern matching.
-/

def zero : Expr := symbol "zero"

abbrev Nat'.zero := symbol "zero"
abbrev Nat'.succ := symbol "succ"

def succ : Expr := symbol "succ"

def Nat'.of_nat : ℕ → Expr
  | .zero => zero
  | .succ n => (:: succ (Nat'.of_nat n))

def Nat'.to_nat : Expr → Option ℕ
  | .symbol "zero" => pure .zero
  | (:: (symbol "succ") n) => Nat.succ <$> (Nat'.to_nat n)
  | _ => .none

/-
induction on natural numbers.
zero_case only gets passed the number,
but succ_case gets passed (:: num (:: nat.rec_with (:: zero_case succ_case)))

(:: apply (:: apply (:: nat.rec_with (:: zero_case succ_case))) (:: succ zero)) =
  (:: apply (:: succ_case (:: (:: zero_case succ_case) zero)))

No nil delimeter after succ_case.
-/

def nat.rec_with.self :=
  :: π (:: id nil)

def nat.rec_with.zero_case :=
  :: π (:: nil (:: π (:: id nil)))

def nat.rec_with.succ_case :=
  :: π (:: nil (:: π (:: nil id)))

-- produces (:: const (:: nat.rec_with (:: zero_case succ_case)))
def nat.rec_with.match_args : Expr :=
  (:: both (:: (quote const) (:: both (:: nat.rec_with.self (:: both (:: nat.rec_with.self (:: both (:: nat.rec_with.zero_case nat.rec_with.succ_case))))))))

def nat.rec_with.quoted_succ_case :=
  (:: both (:: (quote const) nat.rec_with.succ_case))

def nat.rec_with.xs_num :=
  :: π (:: nil id)

def nat.rec_with.quote_fix'' (case : Expr) : Expr :=
  :: both (::
    (quote both) (:: both (::
    (:: both (:: (quote const) case))
    (:: both (::
      (quote both) (:: both (::
      nat.rec_with.match_args
      (quote nat.rec_with.xs_num))))))))

def nat.rec_with.quote_fix_and_run (case : Expr) : Expr :=
  :: both (::
    (quote both) (:: both (::
      (quote (quote apply)) (nat.rec_with.quote_fix'' case))))

/-
Assumes nat.rec_with is the first argument, zero_case 2nd, succ_case 3rd
-/
def nat.rec_with : Expr :=
  let inner_eq := :: both (:: (quote eq) (:: both (:: (nat.rec_with.quote_fix_and_run nat.rec_with.zero_case) (nat.rec_with.quote_fix_and_run nat.rec_with.succ_case))))
  .cons both (:: inner_eq (quote zero))

/-
(:: apply (:: nat.plus (:: m n)))
Recurse on m, base case n
-/
def nat.plus : Expr :=
  let do_app := :: both (:: (quote apply) (:: π (:: (:: both (:: (quote apply) id)) id)))
  let do_succ := :: both (:: (quote succ) do_app)

  let m := :: π (:: id nil)
  let n := :: π (:: nil const)

  let zero_case := n

  -- generates recursor
  let do_rec := (:: both
    (:: (quote apply) (:: both
      (:: (quote nat.rec_with) (:: both
        (:: (quote nat.rec_with)
          (:: both (:: zero_case (quote do_succ)))))))))

  (:: both (:: (quote apply) (:: both (:: do_rec m))))

def nat.fib : Expr :=
  let do_app (fn : Expr) := :: both (:: (quote apply) (:: π (:: (:: both (:: (quote apply) id)) fn)))
  let cmp := (:: both (:: (:: both (:: (quote eq) (quote (::
    (quote (:: succ zero))
    (:: both (:: (quote apply) (:: both (::
      (quote nat.plus) (:: both (::
        (do_app id)
        (do_app (:: π (:: nil id))))))))))))) (:: π (:: id (quote zero)))))
  let do_succ := :: both (:: (quote apply) (:: both (:: cmp id)))

  let zero_case := (quote zero)

  -- generates recursor
  (:: apply (:: nat.rec_with (:: nat.rec_with (:: zero_case do_succ))))

set_option maxRecDepth 5000
example : Nat'.to_nat <$> try_step_n' 1000 (:: apply (:: nat.fib (Nat'.of_nat 5))) = (.ok (.some 5)) := rfl
example : try_step_n' 50 (:: apply (:: nat.fib (Nat'.of_nat 1))) = (.ok (:: succ zero)) := rfl
example : try_step_n' 50 (:: apply (:: nat.fib (Nat'.of_nat 0))) = (.ok zero) := rfl

namespace test_nat

def nat_plus (m n : Expr) : Except Error Expr := do
  try_step_n 100 (:: apply (:: nat.plus (:: m n)))

#eval nat_plus (:: succ (:: succ zero)) (:: succ (:: succ zero))
  >>= (pure <| · == :: (symbol "succ") (:: (symbol "succ") (:: (symbol "succ") (:: (symbol "succ") (symbol "zero")))))

def test_nat_plus_nat (m n : ℕ) (max_steps : ℕ := 100) : Except Error (Option ℕ) := do
  let m' := Nat'.of_nat m
  let n' := Nat'.of_nat n
  try_step_n max_steps (:: apply (:: nat.plus (:: m' n')))
    >>= (pure ∘ Nat'.to_nat)

#eval test_nat_plus_nat 1 100 (max_steps := 100)
#eval test_nat_plus_nat 100 1 (max_steps := 10000)
#eval test_nat_plus_nat 20 19 (max_steps := 5000)

/-
Just to print out the cases, prepend identifiers.
-/
def rec_with_return_is_same : Except Error Bool := do
  let my_succ_case := :: π (:: (:: π (:: id nil)) nil)
  let my_zero_case := Expr.id
  let out ← try_step_n 100 (:: apply (:: (:: apply (:: nat.rec_with (:: nat.rec_with (:: my_zero_case my_succ_case)))) (:: succ zero)))
  pure <| out == nat.rec_with

#eval rec_with_return_is_same

end test_nat
