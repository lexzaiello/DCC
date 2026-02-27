import Dcc.Syn.Ast

open Expr

/-
There is no extra context being invalidated.
we have the entire expression.

Checking defeq of Pi requires the application,
but what about partial apps?

Order needs to be reversed, somehow.
then, 0 refers to the very first argument
instead of some weird index.

K x y
 ^0 ^1
y x K
-/

inductive SynStep : Expr → Expr → Prop
  /-
    Quotation manipulation:
  -/
  | quot : SynStep SK((quot e) x) SK(quot e)
  | head : SynStep SK(f qx) e'
    → SynStep SK(0 f ($ qf qx)) e'
  | id   : SynStep SK(id x) x
  | tail : SynStep SK((pos xs) f qf) e'
    → SynStep SK((tail xs) f ($ qf qx)) e'
  | app' : SynStep SK(f c) f'
    → SynStep SK(x c) x'
    → SynStep SK(($ f x) c) SK($ f' x')
  | pi   : SynStep SK(α x) α' → SynStep SK(β x) β'
    → SynStep SK((Π (α), β) x) SK(Π (α'), β')

/-
TODO: tomorrow. Need to chain the context inside Pi.

pass (f x ...) into next pi via

($ (quote Pi...) ($ (f x ...) id))

also, we may not be quoting in some places in ValidJudgment.app
-/

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
