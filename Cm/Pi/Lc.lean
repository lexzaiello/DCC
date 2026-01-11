import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util
import Cm.Pi.Curry

open Expr

abbrev DebruijnIdx := ℕ

/-
A lambda calculus expression where variables are represented by
the type α.
-/
inductive LcExpr (α : Type) where
  | app : LcExpr α
    → LcExpr α
    → LcExpr α
  | lam : LcExpr α
    → LcExpr α
  | var : α → LcExpr α

notation "λ!" => LcExpr.lam
notation "f$" => LcExpr.app

/-
Fetches a variable without a nil value.
-/
def get_var_no_nil (e : Expr) : Expr :=
  (:: both (:: (:: const apply) e))

#eval do_step run (:: apply (:: (get_var_no_nil (:: π (:: const id))) (:: (symbol "var 1") (:: (symbol "var 2") nil))))

/-
Translation of de bruijn lambda calc expressions to our expressions.

We will use positional parameters for this version.
-/
def Expr.of_lc : LcExpr DebruijnIdx → Except Error Expr
  -- an n-height variable corresponds roughly to a nested π expression
  -- (:: referenced nil)
  -- for example, .var 0 => π id
  | .var 0 =>
    (:: both (:: (:: const apply) (:: π (:: const id))))
  | .var n =>
    
