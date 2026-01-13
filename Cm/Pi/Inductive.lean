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
  (:: apply (:: succ_case (:: zero (:: zero_case succ_case))))
-/
def rec_nat : Expr :=
  let my_zero_case := :: π (:: id nil)
  let my_succ_case := :: π (:: nil id)

  -- assuming zero_case and succ_case are in scope
  let mk_match_succ := :: both 

  let inner_eq := :: both (:: (quote eq) (:: both )
  .cons both (:: inner_eq (quote zero))

/-
(:: apply (:: plus (:: zero (:: succ zero)))) = (:: succ zero)

zero, zero => zero
zero, x => x
y, zero => y

match x with
| .zero => y
| .succ n =>
  match y with
  | .zero => x
  | .succ m => 
-/
def plus_nat : Expr :=
  let my_x := π id nil
