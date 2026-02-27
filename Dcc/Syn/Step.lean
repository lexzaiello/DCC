import Dcc.Syn.Ast

open Expr

inductive Step : Expr → Expr → Prop
  /-
    Normal SK:
  -/
  | K'    : Step SK(K'.{[m, n]} α β x y) x
  | K     : Step SK(K.{[m, n]} α β x y) x
  | S     : Step SK(S.{[m, n, o]} α β γ x y z) SK(x z (y z))
  /-
    Quotation manipulation:
  -/
  | head  : Step SK(0 f ($ qf qx)) SK(f qx)
  | tail  : Step SK((tail xs) f ($ qf qx)) SK((pos xs) f qf)
  | app'  : Step SK(($ f x) c) SK($ (f c) (x c))
  | quot  : Step SK((quot e) x) SK(quot e)
  /-
    Congruence:
  -/
  | left  : Step f f' → Step SK(f x) SK(f' x)
  | right : Step x x' → Step SK(f x) SK(f x')

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | symm    : DefEq e e'  → DefEq e' e
  | step    : Step e e' → DefEq e e'
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq SK(f x) SK(f' x)
  | right   : DefEq x x'  → DefEq SK(f x) SK(f x')
