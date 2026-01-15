import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Custom error types for the list calculus.

Either (:: (symbol "error") ε) or
(:: (symbol "ok") α)

Completely untyped.
-/

def Except'.ok : Expr :=
  ((quote (symbol "ok")) ·')

def Except'.err : Expr :=
  ((quote (symbol "error")) ·')

/-
matches on the ok and error cases.
expects functions on the inner values of
ok and err, respectively

(:: apply (:: apply (:: Except'.match_with (:: ok_case err_case))) E)
-/

/-
Creates an expression that maps the inner component
of an error or ok Except value.
-/
def Except'.match_with.mk_mapper : Expr :=
  (:: both (:: (quote π) ((quote id) ·')))

#eval do_step run (:: apply (:: (:: apply (:: Except'.match_with.mk_mapper id)) (:: apply (:: Except'.err (symbol "hi")))))

def Except'.match_with.map_eq_ok : Expr :=
  :: π (:: Except'.match_with.mk_mapper nil)

def Except'.match_with.map_eq_no : Expr :=
  :: π (:: nil Except'.match_with.mk_mapper)

def Except'.match_with.mk_eq_cases : Expr :=
  (:: both (::
    (quote both) (:: both (::
      (:: both (:: (quote both) (:: both (::
        (quote (quote const))
        map_eq_ok))))
      (:: both (:: (quote both) (:: both (::
        (quote (quote const))
        map_eq_no))))))))

#eval do_step run (:: apply (:: (:: apply (:: Except'.match_with.mk_eq_cases (:: id id))) (:: apply (:: Except'.err (symbol "hi")))))

/-def Except'.match_with : Expr :=
  :: both (:: (quote both)
    (:: both (::
      (quote (quote eq))
      -/

/-
(:: apply (:: apply (:: Except'.bind (:: apply (:: Except'.ok "val")))) (Except.ok' ·'))
= (:: apply (:: Except.ok' "val"))
-/
def Except'.bind : Expr :=
  
