import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Natural numbers, featuring pattern matching.
-/

def zero : Expr := symbol "zero"

def succ : Expr := symbol "succ"

/-
pattern matching on natural numbers.

(:: apply (:: apply (:: match_n (:: zero_case succ_case))) my_n)
-/
def match_nat : Expr :=
  -- with succ_case in scope
  -- want to produce :: π nil succ_case
  let mk_match_succ := :: both (:: (quote π) (:: both (:: (quote nil) id)))

  let inner_eq := :: both (:: (quote eq) (:: π (:: id mk_match_succ)))
  .cons both (:: inner_eq (quote zero))

#eval do_step run (:: apply (:: match_nat (:: id id)))
#eval do_step run (:: apply (:: (:: apply (:: match_nat (:: id id))) zero))
#eval do_step run (:: apply (:: (:: apply (:: match_nat (:: id id))) (:: succ (:: succ zero))))

/-
induction on natural numbers.
zero_case only gets passed the number,
but succ_case gets passed (:: num (:: rec_nat (:: zero_case succ_case)))

(:: apply (:: apply (:: rec_nat (:: zero_case succ_case))) (:: succ zero)) =
  (:: apply (:: succ_case (:: (:: zero_case succ_case) zero)))

No nil delimeter after succ_case.
-/

def rec_nat.self :=
  :: π (:: id nil)

def rec_nat.zero_case :=
  :: π (:: nil (:: π (:: id nil)))

def rec_nat.succ_case :=
  :: π (:: nil (:: π (:: nil id)))

-- produces (:: const (:: rec_nat (:: zero_case succ_case)))
def rec_nat.match_args : Expr :=
  (:: both (:: (quote const) (:: both (:: rec_nat.self (:: both (:: rec_nat.zero_case rec_nat.succ_case))))))

def rec_nat.quoted_succ_case :=
  (:: both (:: (quote const) rec_nat.succ_case))

/-
Make a new both expression and a new π expression.
both should be inserting apply at the beginning to advance
the program.
the apply may not be necessary since we already have a both.
both may not be necessary either.

We use the π to slice off the first element.
TODO: Not sure if we need apply.

Need to insert the succ function as well.
-/
def rec_nat.quote_fix' : Expr :=
  :: both (::
    (quote π)
    (:: both (::
      rec_nat.quoted_succ_case
      (:: both (::
      rec_nat.match_args
      (quote id))))))

/-
Assumes rec_nat is the first argument, zero_case 2nd, succ_case 3rd
-/
def rec_nat : Expr :=
  let inner_eq := :: both (:: (quote eq) (:: both (:: rec_nat.zero_case rec_nat.quote_fix')))
  .cons both (:: inner_eq (quote zero))

/-
rec_nat tests:
- just plug in names for the functions first, to see if it's doing the fixpoint right.
-/

def test_rec_nat_zero_works : Except Error Bool := do
  let zero_result ← do_step run (:: apply (:: (:: apply (:: match_nat (:: id id))) zero))
  let zero_rec ← do_step run (:: apply (:: (:: apply (:: rec_nat (:: rec_nat (:: id id)))) zero))

  dbg_trace zero_result
  dbg_trace zero_rec

  pure <| zero_result == zero_rec

#eval test_rec_nat_zero_works

def test_rec_nat_zero_works' : Except Error Bool := do
  let zero_result ← do_step run (:: apply (:: (:: apply (:: match_nat (:: (quote (symbol "hi")) id))) zero))
  let zero_result' ← do_step run (:: apply (:: (:: apply (:: rec_nat (:: rec_nat (:: (quote (symbol "hi")) id)))) zero))

  pure <| zero_result' == (symbol "hi") && zero_result' == zero_result

#eval test_rec_nat_zero_works'

/-
Just to print out the cases, prepend identifiers.
-/
def test_rec_nat_symb : Except Error Expr := do
  -- succ should have args (:: rec_nat (:: zero_case (:: my_succ_case num)))
  let my_succ_case := Expr.id
  let my_zero_case := Expr.id
  do_step run (:: apply (:: (:: apply (:: rec_nat (:: rec_nat (:: my_zero_case my_succ_case)))) (:: succ zero)))

#eval test_rec_nat_symb
