import Dcc.Syn.Ast

open Expr

inductive SynStep : Expr → Expr → Prop
  /-
    Quotation manipulation:
  -/
  | quot : SynStep SK((quot e) x) SK(quot e)
  | head : SynStep SK(0 f ($ qf qx)) SK(f qx)
  | tail : SynStep SK((pos xs) f qf) e'
    → SynStep SK((tail xs) f ($ qf qx)) e'
  | app' : SynStep SK(f c) f'
    → SynStep SK(x c) x'
    → SynStep SK(($ f x) c) SK($ f' x')

inductive Step : Expr → Expr → Prop
  /-
    Normal SK:
  -/
  | K'    : Step SK(K'.{[m, n]} α β x y) x
  | K     : Step SK(K.{[m, n]} α β x y) x
  | S     : Step SK(S.{[m, n, o]} α β γ x y z) SK(x z (y z))
  | syn   : SynStep e e' → Step e e'
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
