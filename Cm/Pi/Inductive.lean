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
induction on natural numbers.

(:: apply (:: apply (:: match_n (:: zero_case succ_case))) my_n)
-/
def match_nat : Expr :=
  -- with succ_case in scope
  -- want to produce :: π nil succ_case
  let mk_match_succ := :: both (:: (quote π) (:: (quote nil) id))

  let inner_eq := :: both (:: (:: const eq) (:: π (:: id mk_match_succ)))
  .cons both (:: inner_eq (quote zero))
