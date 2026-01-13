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

def rec_nat.quote_succ :=
  :: both (:: (quote const) rec_nat.succ_case)

def rec_nat.quote_zero :=
  :: both (:: (quote const) rec_nat.zero_case)

-- produces (:: const (:: rec_nat (:: zero_case succ_case)))
def rec_nat.quote_match_args : Expr :=
  :: both (:: (quote const) (:: both (:: rec_nat.self (:: both (:: rec_nat.zero_case rec_nat.succ_case)))))

/-
Slices off the head of the number.
-/
def rec_nat.quote_xs_succ : Expr :=
  (quote (:: π (:: nil id)))

-- id is the number argument
-- produces a quoted (:: both (quote succ_case) (:: (quote (:: zero_case succ_case)) id))
-- assuming succ_case and zero_case are in scope
def rec_nat.quote_fix : Expr :=
  :: both (:: (quote both) (:: both (:: rec_nat.quote_succ (:: both (:: rec_nat.quote_xs_succ rec_nat.quote_match_args)))))

/-
Assumes rec_nat is the first argument, zero_case 2nd, succ_case 3rd
-/
def rec_nat : Expr :=
  -- assuming zero_case and succ_case are in scope
  -- mk_id is like id above in match_nat
  -- we want to make a (:: both that inserts the quoted match args back in
  -- this will take in our number as an argument
  let mk_rec_succ := :: both (:: (quote π) (:: both (:: (quote nil) rec_nat.quote_fix)))

  let inner_eq := :: both (:: (quote eq) (:: both (:: rec_nat.zero_case rec_nat.quote_fix)))
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

/-
Just to print out the cases, prepend identifiers.
-/
def test_rec_nat_symb : Except Error Expr := do
  -- succ should have args (:: num (:: rec_nat (:: zero_case succ_case)))
  let my_succ_case := :: π (:: id nil)
  let my_zero_case := (:: both (:: (quote <| symbol "my_zero_case") id))
  do_step run (:: apply (:: (:: apply (:: rec_nat (:: (symbol "rec_nat") (:: my_zero_case my_succ_case)))) (:: succ zero)))

#eval test_rec_nat_symb
