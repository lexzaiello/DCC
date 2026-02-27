import Dcc.Syn.Ast

open Expr

inductive IsStep : Expr → Expr → Prop
  /-
    Normal SK:
  -/
  | K'    : IsStep SK(K'.{[m, n]} α β x y) x
  | K     : IsStep SK(K.{[m, n]} α β x y) x
  | S     : IsStep SK(S.{[m, n, o]} α β γ x y z) SK(x z (y z))
  /-
    Quotation manipulation:
  -/
  | head  : IsStep SK(0 f ($ qf qx)) SK(f qx)
  | tail  : IsStep SK((tail xs) f ($ qf qx)) SK((pos xs) f qf)
  | app'  : IsStep SK(($ f x) c) SK($ (f c) (x c))
  | quot  : IsStep SK((quot e) x) SK(quot e)
  /-
    Congruence:
  -/
  | left  : IsStep f f' → IsStep SK(f x) SK(f' x)
  | right : IsStep x x' → IsStep SK(f x) SK(f x')

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | symm    : DefEq e e'  → DefEq e' e
  | step    : IsStep e e' → DefEq e e'
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq SK(f x) SK(f' x)
  | right   : DefEq x x'  → DefEq SK(f x) SK(f x')
