import Dcc.CC.Ast
import Dcc.CC.Step2
import Dcc.CC.Judge
import Qq
import Qq.MetaM
import Lean.Elab
import Lean.Elab.Term

open Lean Elab Qq Lean.Elab

namespace tactic

abbrev MLevel := Lean.Expr

inductive MExpr where
  | sort  : MLevel    → MExpr
  | flip  : MExpr     → MExpr
  | id    : MExpr     → MExpr
  | fst   : MExpr     → MExpr  → MExpr
  | snd   : MExpr     → MExpr  → MExpr
  -- Nondependent snd
  | snd'  : MExpr     → MExpr  → MExpr
  | quot  : MExpr     → MExpr  → MExpr  → MExpr
  | comp  : MExpr     → MExpr  → MExpr  → MExpr
  -- Nondependent composition
  | comp' : MExpr     → MExpr  → MExpr
  | pair  : MExpr     → MExpr  → MExpr  → MExpr  → MExpr
  | sigma : MExpr     → MExpr  → MExpr
  | mk    : MExpr     → MExpr  → MExpr
  | pi    : MLevel    → MLevel → MExpr
  | curr  : MExpr     → MExpr  → MExpr
  -- Nondependent curry
  | curr' : MExpr     → MExpr  → MExpr  → MExpr
  | appl  : MLevel    → MExpr  → MExpr → MExpr
  | app   : MExpr     → MExpr  → MExpr
  | lean  : Lean.Expr → MExpr
deriving BEq, Repr

def MExpr.from_expr (e : Q(_root_.Expr)) : TermElabM MExpr :=
  match e with
  | ~q(Expr.sort $m) => return .sort m
  | _ =>
    match e with
    | .app (.const ``Expr.const []) e => MExpr.flip <$> from_expr e
    | .app (.const ``Expr.id []) e => MExpr.id <$> from_expr e
    | .app (.app (.const ``Expr.fst []) α) β => do
      return MExpr.fst (← from_expr α) (← from_expr β)
    | .app (.app (.const ``Expr.snd []) α) β => do
      return MExpr.snd (← from_expr α) (← from_expr β)
    | .app (.app (.const ``Expr.snd' []) α) β => do
      return MExpr.snd' (← from_expr α) (← from_expr β)
    | .app (.app (.app (.const ``Expr.quot []) α) β) x => do
      return MExpr.quot (← from_expr α) (← from_expr β) (← from_expr x)
    | .app (.app (.const ``Expr.comp' []) α) β => do
      return MExpr.comp' (← from_expr α) (← from_expr β)
    | .app (.app (.app (.app (.const ``Expr.pair []) α) β) x) y => do
      return MExpr.pair
        (← from_expr α)
        (← from_expr β)
        (← from_expr x)
        (← from_expr y)
    | .app (.app (.const ``Expr.sigma []) α) β => do
      return MExpr.sigma (← from_expr α) (← from_expr β)
    | .app (.app (.const ``Expr.mk []) α) β => do
      return MExpr.mk (← from_expr α) (← from_expr β)
    | .app (.app (.const ``Expr.pi []) m) n =>
      return MExpr.pi m n
    | .app (.app (.const ``Expr.curr []) α) x => do
      return MExpr.curr (← from_expr α) (← from_expr x)
    | .app (.app (.app (.const ``Expr.curr' []) α) β) x => do
      return MExpr.curr' (← from_expr α) (← from_expr β) (← from_expr x)
    | .app (.app (.app (.const ``Expr.appl []) m) α) x => do
      return MExpr.appl m (← from_expr α) (← from_expr x)
    | .app f x =>
      (do pure <| (← from_expr f).app (← from_expr x)) <|> return .lean e
    | e => return .lean e

/-
Tactic to reduce hypotheses like Reduce a b into Reduce a (reduce b), except b is reduced to normal form.
-/
syntax "reduce_reduces'" term : tactic

elab "reduce_reduces" hyp:term : tactic => do
  let hyp := ← Lean.Meta.whnf (← ← Lean.Meta.reduceAll <$> Lean.Elab.Term.elabTerm hyp .none)
  let ty ← Lean.Meta.inferType hyp
  match ty with
  | Lean.Expr.app (Lean.Expr.app (.const ``Expr.Reduces []) α) β =>
    let some α ← checkTypeQ α q(_root_.Expr) | throwError s!"{β} is not an expr"
    let some β ← checkTypeQ β q(_root_.Expr) | throwError s!"{α} is not an expr"
    let some h := ← checkTypeQ hyp q(_root_.Expr.Reduces $α $β) | throwError s!"{hyp} is not a Reduces {α} {β}"
    let h' := q(_root_.Expr.Reduces.complete $h)
    sorry
  | _ => throwError s!"{ty} is not a Reduces A B"

end tactic
