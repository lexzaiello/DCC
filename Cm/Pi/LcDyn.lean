import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Nat
import Cm.Pi.List

open Expr

/-
Lambda calculus with De Bruijn-indexed arguments.

(:: apply (:: lam (:: apply (:: var zero))) (symbol "hello world"))
= symbol "hello world"
-/

/-
De Bruijn indices correspond to variable lookups in the context.
-/
def var : Expr :=
  (:: both (:: (quote apply) (:: both (:: (quote list.get_n') id))))

def test_ctx := :: (symbol "a") (:: (symbol "discard") nil)

#eval try_step_n run 100 (:: apply (:: (:: apply (:: var Nat'.zero)) test_ctx))

/-
A lambda passes its future context onto its child.
-/
def lam : Expr := Expr.id

notation "λ!" => (fun bdy => :: apply (:: lam bdy)) -- λ binders should steal their above contexts.
notation "v#" => (fun n => (:: apply (:: var (Nat'.of_nat n))))
notation "f$" => (fun f x => (:: apply (:: f (:: apply (:: list.reverse x)))))

#eval try_step_n run 100 (:: apply (:: (:: apply (:: lam (:: apply (:: var Nat'.zero)))) test_ctx))

def test_id : Except Error Expr :=
  let my_id := (:: apply (:: lam (:: apply (:: var Nat'.zero))))
  let nested_id := (:: apply (:: my_id (:: my_id nil)))
  try_step_n run 100 (:: apply (:: nested_id (:: (symbol "hello world") nil)))

#eval test_id

def test_id'_nice : Except Error Expr :=
  let my_id := λ! (v# 0)
  let nested_id := f$ my_id (:: my_id nil)
  try_step_n run 100 (f$ nested_id (:: (symbol "hello world") nil))

#eval test_id'_nice

def test_tre : Except Error Expr :=
  let my_tre := λ! (λ! (v# 1))
  try_step_n run 200 (f$ my_tre (:: (symbol "a") (:: (symbol "b") nil)))

#eval test_tre

def test_flse : Except Error Expr :=
  let my_flse := λ! (λ! (v# 0))
  try_step_n run 200 (f$ my_flse (:: (symbol "a") (:: (symbol "b") nil)))

#eval test_flse

def flse_lc : Expr := λ! (λ! (v# 0))

def tre_lc : Expr := λ! (λ! (v# 1))

/-
0 f x = x
-/
def zero_lc : Expr := λ! (λ! (v# 0))

def is_zero_lc : Expr := λ! (f$ (v# 0) (:: (λ! flse_lc) (:: tre_lc nil)))

#eval try_step_n run 200 (f$ is_zero_lc zero_lc)
