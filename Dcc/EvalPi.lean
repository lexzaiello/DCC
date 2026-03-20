import Dcc.Ast
import Dcc.Eval

/-
All arguments reduce at least one step for each argument applied.
-/

inductive Expr.RedPi : Expr → Expr → Prop
  | pi    : Expr.RedPi (SK (α x)) α'
    → Expr.RedPi (SK (β x)) β'
    → Expr.RedPi (SK ((Π α, β) x)) (SK (Π α', β'))
  | ty    : Expr.RedTyTrans e e'
    → Expr.RedPi e e'

/-
Size of a function.

The core combinators have a fixed number of arguments.
Eventually, their codomain resolves with an actual application.

Just count the number of β binders the way down. This corresponds to the number
of arguments accepted.
-/
inductive Expr.PiSize : Expr → ℕ → Prop
  | pi : Expr.PiSize β m
    → Expr.PiSize (SK (Π α, β)) (m + 1)
  | ty : Expr.TySize β (m + 1)
    → Expr.PiSize (SK (Π α, β)) ((m + 1) + 1)

def Expr.pi_size : Expr → Option ℕ
  | SK (Π _α, β) =>
    match Expr.ty_size β with
    | .zero => match Expr.pi_size β with
      | .some m => .some (m + 1)
      | .none => .none
    | n => .some (n + 1)
  | _ => .none

-- For checking codomain of app types.
inductive Expr.RedAppTy : Expr → Expr → Prop
  | mk : Expr.RedPi (SK (β x)) β'
    → Expr.RedAppTy (SK ((Π α, β) x)) β'

theorem app_size_dec : Expr.RedAppTy t t' → Expr.PiSize t m → Expr.PiSize t' n → n < m := by
  intro hr hm hn
  induction hm
  cases hr
  cases hr
