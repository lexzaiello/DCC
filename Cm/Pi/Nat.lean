import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Natural numbers, featuring pattern matching.
-/

def zero : Expr := symbol "zero"
abbrev Nat' := zero

def succ : Expr := symbol "succ"

def Nat'.of_nat : ℕ → Expr
  | .zero => zero
  | .succ n => (:: succ (Nat'.of_nat n))

def Nat'.to_nat : Expr → Option ℕ
  | .symbol "zero" => pure .zero
  | (:: (symbol "succ") n) => Nat.succ <$> (Nat'.to_nat n)
  | _ => .none

/-
pattern matching on natural numbers.

(:: apply (:: apply (:: match_n (:: zero_case succ_case))) my_n)
-/
def nat.match_with : Expr :=
  -- with succ_case in scope
  -- want to produce :: π nil succ_case
  let mk_match_succ := :: both (:: (quote π) (:: both (:: (quote nil) id)))

  let inner_eq := :: both (:: (quote eq) (:: π (:: id mk_match_succ)))
  .cons both (:: inner_eq (quote zero))

#eval do_step run (:: apply (:: nat.match_with (:: id id)))
#eval do_step run (:: apply (:: (:: apply (:: nat.match_with (:: id id))) zero))
#eval do_step run (:: apply (:: (:: apply (:: nat.match_with (:: id id))) (:: succ (:: succ zero))))

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

def nat.rec_with.quote_fix'' : Expr :=
  :: both (::
    (quote both) (:: both (::
    nat.rec_with.quoted_succ_case
    (:: both (::
      (quote both) (:: both (::
      nat.rec_with.match_args
      (quote nat.rec_with.xs_num))))))))

def nat.rec_with.quote_fix_and_run : Expr :=
  :: both (::
    (quote both) (:: both (::
      (quote (quote apply)) nat.rec_with.quote_fix'')))

/-
Assumes nat.rec_with is the first argument, zero_case 2nd, succ_case 3rd
-/
def nat.rec_with : Expr :=
  let inner_eq := :: both (:: (quote eq) (:: both (:: nat.rec_with.zero_case nat.rec_with.quote_fix_and_run)))
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

namespace test_nat

def nat_plus (m n : Expr) : Except Error Expr := do
  try_step_n run 100 (:: apply (:: nat.plus (:: m n)))

#eval nat_plus (:: succ (:: succ zero)) (:: succ (:: succ zero))
  >>= (pure <| · == :: (symbol "succ") (:: (symbol "succ") (:: (symbol "succ") (:: (symbol "succ") (symbol "zero")))))

def test_nat_plus_nat (m n : ℕ) (max_steps : ℕ := 100) : Except Error (Option ℕ) := do
  let m' := Nat'.of_nat m
  let n' := Nat'.of_nat n
  try_step_n run max_steps (:: apply (:: nat.plus (:: m' n')))
    >>= (pure ∘ Nat'.to_nat)

#eval test_nat_plus_nat 1 100 (max_steps := 55)
#eval test_nat_plus_nat 100 1 (max_steps := 10000)
#eval test_nat_plus_nat 20 19 (max_steps := 5000)

/-
nat.rec_with tests:
- just plug in names for the functions first, to see if it's doing the fixpoint right.
-/

def rec_with_zero_works : Except Error Bool := do
  let zero_result ← do_step run (:: apply (:: (:: apply (:: nat.match_with (:: id id))) zero))
  let zero_rec ← do_step run (:: apply (:: (:: apply (:: nat.rec_with (:: nat.rec_with (:: id id)))) zero))

  dbg_trace zero_result
  dbg_trace zero_rec

  pure <| zero_result == zero_rec

#eval rec_with_zero_works

def rec_with_zero_works' : Except Error Bool := do
  let zero_result ← do_step run (:: apply (:: (:: apply (:: nat.match_with (:: (quote (symbol "hi")) id))) zero))
  let zero_result' ← do_step run (:: apply (:: (:: apply (:: nat.rec_with (:: nat.rec_with (:: (quote (symbol "hi")) id)))) zero))

  pure <| zero_result' == (symbol "hi") && zero_result' == zero_result

#eval rec_with_zero_works'

/-
Just to print out the cases, prepend identifiers.
-/
def rec_with_symb : Except Error Expr := do
  let my_succ_case := Expr.id
  let my_zero_case := Expr.id
  try_step_n run 100 (:: apply (:: (:: apply (:: nat.rec_with (:: (symbol "nat.rec_with") (:: my_zero_case my_succ_case)))) (:: succ zero)))

/-
:: (:: (symbol "nat.rec_with") (:: (symbol "nat.rec_with") (:: id id))) (symbol "zero") is output.
so we can basically just insert an apply inside and outside at the beginnings.
-/
#eval rec_with_symb

/-
Just to print out the cases, prepend identifiers.
-/
def rec_with_return_is_same : Except Error Bool := do
  let my_succ_case := :: π (:: (:: π (:: id nil)) nil)
  let my_zero_case := Expr.id
  let out ← try_step_n run 100 (:: apply (:: (:: apply (:: nat.rec_with (:: nat.rec_with (:: my_zero_case my_succ_case)))) (:: succ zero)))
  pure <| out == nat.rec_with

#eval rec_with_return_is_same

/-
Running nat.rec_with again.
Should give us zero, since we are running id in the last case.
-/
def rec_with_descent : Except Error Expr := do
  let my_succ_case := :: both (:: (quote apply) (:: π (:: (:: both (:: (quote apply) id)) id)))
  let my_zero_case := Expr.id
  let out ← try_step_n run 50 (:: apply (:: (:: apply (:: nat.rec_with (:: nat.rec_with (:: my_zero_case my_succ_case)))) (:: succ zero)))
  pure out

#eval rec_with_descent >>= (pure <| · == zero)

end test_nat
