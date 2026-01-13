import Mathlib.Data.Nat.Notation

import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util
import Cm.Pi.Curry
import Cm.Pi.LcAst

open Std (Format)
open Std (ToFormat)
open Std.ToFormat (format)

open Expr

/-
Whacky thing:
lam = (:: (symbol "λ") (:: (symbol "x") (:: (symbol "x") nil)))
-/

/-
λ (λ 1)

free variables get decremented each binder down we go
-/
def abstract (depth : ℕ) : LcExpr DebruijnIdx → Except Error Expr
  | .var 0 => pure <| .id
  | .var n => if depth - n == 0 then 
  | .symbol s => pure <| :: const (symbol s)
  | .lam b => do
    -- λ (λ 0) we just substitute our context in
    -- this is actually a no-op
    -- nested lambda requires deferring apply
    -- until we have all the arguments we're expecting
    pure <| (:: both (:: (quote apply) (:: both (:: (quote (← abstract' b)) id))))
  | .app f x => do
    /-
      Future application. λf (λx f x). To do this, we use both. Then, we apply.
    -/
    let f' ← abstract' f
    let x' ← abstract' x
    pure <| (:: both (:: (quote apply) (:: f' x')))
