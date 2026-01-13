import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
(:: apply (:: list.rec_with (:: list.rec_with (:: nil_case xs_case))))

xs_case should accept the head of the list as an argument.
Note that this is a somewhat unsafe operation on lists that are not
delimited with nil.
-/

def list.rec_with.self :=
  :: π (:: id nil)

def list.rec_with.nil_case :=
  :: π (:: nil (:: π (:: id nil)))

def list.rec_with.xs_case :=
  :: π (:: nil (:: π (:: nil id)))

-- produces (:: const (:: list.rec_with (:: nil_case xs_case)))
def list.rec_with.match_args : Expr :=
  (:: both (:: (quote const) (:: both (:: list.rec_with.self (:: both (:: list.rec_with.self (:: both (:: list.rec_with.nil_case list.rec_with.xs_case))))))))

def list.rec_with.quoted_xs_case :=
  (:: both (:: (quote const) list.rec_with.xs_case))

def list.rec_with.xs_num :=
  :: π (:: nil id)

def list.rec_with.quote_fix'' : Expr :=
  :: both (::
    (quote both) (:: both (::
    list.rec_with.quoted_xs_case
    (:: both (::
      (quote both) (:: both (::
      list.rec_with.match_args
      (quote list.rec_with.xs_num))))))))

def list.rec_with.quote_fix_and_run : Expr :=
  :: both (::
    (quote both) (:: both (::
      (quote (quote apply)) list.rec_with.quote_fix'')))

/-
Assumes list.rec_with is the first argument, nil_case 2nd, xs_case 3rd
-/
def list.rec_with : Expr :=
  let inner_eq := :: both (:: (quote eq) (:: both (:: list.rec_with.nil_case list.rec_with.quote_fix_and_run)))
  .cons both (:: inner_eq (quote nil))

namespace test_list

/-
Continue running the recursor on a list until we get to nil,
then display.
-/
def rec_with_descent : Except Error Expr := do
  let my_succ_case := :: both (:: (quote apply) (:: π (:: (:: both (:: (quote apply) id)) id)))
  let my_zero_case := Expr.id
  let out ← try_step_n run 50 (:: apply (:: (:: apply (:: list.rec_with (:: list.rec_with (:: my_zero_case my_succ_case)))) (:: (symbol "discard") nil)))
  pure out

#eval rec_with_descent

end test_list
