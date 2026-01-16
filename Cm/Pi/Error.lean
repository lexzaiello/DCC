import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util
import Cm.Pi.List
import Cm.Pi.Curry

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
(:: apply (:: Except'.flag (:: apply (:: Except'.ok (symbol "hi")))))
= (symbol "ok")
-/
def Except'.flag : Expr :=
  (:: π (:: id nil))

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

#eval do_step (:: apply (:: (:: apply (:: Except'.match_with.mk_mapper id)) (:: apply (:: Except'.err (symbol "hi")))))

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

#eval do_step (:: apply (:: (:: apply (:: Except'.match_with.mk_eq_cases (:: id id))) (:: apply (:: Except'.err (symbol "hi")))))

def Except'.mk_eq : Expr :=
  (:: both (:: (quote both) (:: both (::
    (:: both (:: (quote both) (:: both (::
      (:: both (:: (quote both) (:: both (::
        (quote (quote eq))
        match_with.mk_eq_cases)))) (quote (quote s_ok))))))
    (quote (:: π (:: id nil)))))))

#eval do_step (:: apply (:: (:: apply (:: Except'.mk_eq (:: id id))) (:: apply (:: Except'.err (symbol "hi")))))

/-
Maps the ok and error values of an except, creating a new except.
-/
def Except'.map_with : Expr :=
  (:: both (:: (quote both) (:: both (:: (quote (quote apply))
    Except'.mk_eq))))

#eval try_step_n 100
  (:: apply (:: (:: apply (:: Except'.map_with (:: id id))) (:: apply (:: Except'.err (symbol "hi")))))

#eval try_step_n 100
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

#eval try_step_n 40
  (:: apply (:: (:: apply (:: Except'.match_with (:: id ((quote (symbol "my error is: ")) ·')))) (:: apply (:: Except'.err (symbol "hi")))))

#eval try_step_n 40
  (:: apply (:: (:: apply (:: Except'.match_with (:: ((quote (symbol "my ok is: ")) ·') id))) (:: apply (:: Except'.ok (symbol "hi")))))

def Except'.pure := Except'.ok

/-
This is essentially Except'.match_with reversed.
This version is not curried.
It expects the except as the first argument,
and what to do with the ok value as the second
-/
def Except'.bind.my_match :=
  :: π (:: (quote Except'.match_with)
    (:: both (::
      id
      (quote Except'.err))))

def Except'.bind.my_except := :: π (:: id nil)

def Except'.bind :=
  (:: both (:: (quote apply)
    (:: both (::
      (:: both (:: (quote apply) Except'.bind.my_match)) Except'.bind.my_except))))

/-
Left-to-right composition of kleisli arrows.
Curried thrice. Expects the two except-monadic actions,
then the value.
-/
def Except'.kleisliRight.action₁ : Expr :=
  (:: both (:: (quote apply) (:: both
        (:: (args.read 0 (:: π (:: id nil))) (:: π (:: nil id))))))

def Except'.kleisliRight : Expr :=
  (:: apply (:: curry (:: apply (:: curry
    (:: both (:: (quote apply) (:: both (:: (quote Except'.bind)
      (:: both (:: Except'.kleisliRight.action₁ (args.read 0 (:: π (:: nil id)))))))))))))

/-
(Except.ok >=> Except.ok) "hi" = ok "hi"
-/
set_option maxRecDepth 2000
example : try_step_n' 100 (:: apply (:: (:: apply (:: (:: apply (:: Except'.kleisliRight Except'.ok))
  Except'.ok)) (symbol "hi"))) = (.ok (:: Except'.s_ok (symbol "hi"))) := rfl

infixl:60 "e>>=" => (fun e f =>
  (:: apply (:: Except'.bind (:: e f))))

/-
(:: apply (:: action args))
  e>>= f
-/
infixl:60 "e>=>" => (fun e f =>
  (:: both (:: (quote apply)
    (:: both (:: (quote Except'.bind) (:: both (::
      (:: both (:: (quote apply) (:: both
        (:: (quote e) id))))
      (quote f))))))))

#eval try_step_n 50
  (:: apply (:: Except'.bind (:: (:: apply (:: Except'.err (symbol "hi"))) id)))

#eval try_step_n 50 ((:: apply (:: Except'.ok (symbol "hi"))) e>>= id)
#eval try_step_n 50 ((:: apply (:: Except'.err (:: (symbol "other") (symbol "hi")))) e>>= id)

/-
Combines many except values in a list.
Returns a list containing all the unwrapped
ok values, or the first error value.
-/
def Except'.allM : Expr :=
  let my_l := Expr.id
  
  sorry
