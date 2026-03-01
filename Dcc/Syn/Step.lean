import Dcc.Syn.Ast

open Expr

/-
Indices need to work from the inside out
for def eq to be straight-forward.

we can't go in order of the application,
the actual expression needs to be last argument first.

some kind of offset? nah.
just some kind of dummy value.
-/


inductive SynStep : Expr → Expr → Prop
  /-
    Quotation manipulation:
  -/
  | quot : SynStep SK((quot e) x) SK(quot e)
  | head : SynStep SK(f (quot qx)) e'
    → SynStep SK(0 f (quot (qf qx))) e'
  | id   : SynStep SK(id x) x
  | tail : SynStep SK((pos xs) f (quot qf)) e'
    → SynStep SK((tail xs) f (quot (qf qx))) e'
  | app' : SynStep SK(f c) f' → SynStep SK(x c) x'
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
