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

def Except'.s_ok := symbol "ok"
def Except'.s_err := symbol "error"

def Except'.ok : Expr :=
  ((quote s_ok) ·')

def Except'.err : Expr :=
  ((quote s_err) ·')

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

def Except'.mk_eq : Expr :=
  (:: both (:: (quote both) (:: both (::
    (:: both (:: (quote both) (:: both (::
      (:: both (:: (quote both) (:: both (::
        (quote (quote eq))
        match_with.mk_eq_cases)))) (quote (quote s_ok))))))
    (quote (:: π (:: id nil)))))))

#eval do_step run (:: apply (:: (:: apply (:: Except'.mk_eq (:: id id))) (:: apply (:: Except'.err (symbol "hi")))))

/-
Maps the ok and error values of an except, creating a new except.
-/
def Except'.map_with : Expr :=
  (:: both (:: (quote both) (:: both (:: (quote (quote apply))
    Except'.mk_eq))))

#eval try_step_n run 100
  (:: apply (:: (:: apply (:: Except'.map_with (:: id id))) (:: apply (:: Except'.err (symbol "hi")))))

#eval try_step_n run 100
  (:: apply (:: (:: apply (:: Except'.map_with (:: id ((quote (symbol "my error is: ")) ·')))) (:: apply (:: Except'.err (symbol "hi")))))

/-
Fetches the inner value of an Except'.
-/
def Except'.unwrap : Expr :=
  :: π (:: nil id)

def Except'.match_with : Expr :=
  (:: both (:: (quote both) (:: both (:: (quote (quote apply))
    (:: both (:: (quote both) (:: both (:: (quote (quote Except'.unwrap))
    (:: both (:: (quote both) (:: both (:: (quote (quote apply))
      Except'.mk_eq))))))))))))

#eval try_step_n run 100
  (:: apply (:: (:: apply (:: Except'.match_with (:: id ((quote (symbol "my error is: ")) ·')))) (:: apply (:: Except'.err (symbol "hi")))))

/-
(:: apply (:: apply (:: Except'.bind (:: apply (:: Except'.ok "val")))) (Except.ok' ·'))
= (:: apply (:: Except.ok' "val"))
-/
/-def Except'.bind : Expr :=
  
-/
