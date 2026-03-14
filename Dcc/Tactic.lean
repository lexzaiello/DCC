import Dcc.Ast
import Dcc.Eval
import Dcc.Judge
import Qq
import Lean
import Lean.Elab
import Mathlib.Tactic.CasesM

open Expr Qq Lean Meta Elab Tactic

namespace gen

abbrev Level := Lean.Expr

inductive MExpr where
  | Srt    : Level → MExpr
  | Pi     : Level → MExpr → MExpr → MExpr -- Pi (α : Syntax (Sort m)) (β : Sort n) : (Sort n)
  | K'     : Level → Level → MExpr
  | K      : Level → Level → MExpr
  | S      : Level → Level → Level → MExpr
  | next   : MExpr
  | read   : MExpr
  | app'   : MExpr
  | app    : MExpr  → MExpr → MExpr
  | lean_e : Lean.Expr → MExpr
deriving BEq, Repr

def MExpr.decode (e : Lean.Expr) : Lean.Elab.TermElabM MExpr := do
  match e with
  | (.app (.app (.const `Expr.app []) f) x) => return .app (← decode f) (← decode x)
  | .app (.app (.app (.const ``Expr.Pi []) m) α) β => do
    let α' ← decode α
    let β' ← decode β
    return .Pi m α' β'
  | .app (.const ``Expr.Srt []) m  => return .Srt m
  | (.app (.app (.const `Expr.K' []) m) n) => do
    return .K' m n
  | (.app (.app (.const `Expr.K []) m) n) => do
    return .K m n
  | (.app (.app (.app (.const `Expr.S []) m) n) o) => do
    return .S m n o
  | .const `Expr.next [] => return .next
  | .const `Expr.read [] => return .read
  | .const `Expr.app' [] => return .app'
  | e => return .lean_e e

end gen

def contains_spine (e : Q(_root_.Expr)) : MetaM Bool := do
  match e with
  | ~q((K'.{[$m, $n]})) => pure true
  | ~q((K.{[$m, $n]})) => pure true
  | ~q((S.{[$m, $n, $o]})) => pure true
  | ~q(Π.{[$m]} $α, $β) => pure true
  | ~q(next) => pure true
  | ~q(read) => pure true
  | ~q($) => pure true
  | ~q(Srt $m) => pure true
  | .app (.app (.const ``_root_.Expr.app []) f) _x => contains_spine f
  | _ => pure false

def cases_matcher (matcher : Lean.Expr → MetaM Bool) (recursive := false) : TacticM Unit := do
  Lean.Elab.Tactic.withMainContext do
    let (mvarId :: remainingGoals) := ← getGoals
      | throwError "No goals to solve"

    let goals ← mvarId.casesMatching matcher recursive

    setGoals (goals ++ remainingGoals)

syntax "cases_spine" : tactic

elab "cases_spine" : tactic => do
  cases_matcher (fun (ty : Q(Prop)) => do
      match ty with
      | ~q(Judge $α $x) => contains_spine x
      | ~q(ParRed $α $e') => contains_spine α
      | _ => pure false)

syntax "cases_conv" : tactic

elab "cases_conv" : tactic => do
  cases_matcher (fun (ty : Q(Prop)) => do
      match ty with
      | ~q(∃ D, ParRed $A D ∧ ParRed $B D) => pure <| (← contains_spine A) ∨ (← contains_spine B)
      | ~q(ParRed $A $D ∧ ParRed $B $D) => pure <| (← contains_spine A) ∨ (← contains_spine B)
      | _ => pure false) (recursive := true)

syntax "reduce!" term   : term
syntax "reduction" term : term

inductive ReduceCmd where | reduction | reduce

def reduce' (stx : Syntax) (cmd : ReduceCmd) : TermElabM Lean.Expr := do
  let e ← Lean.Elab.Term.elabTerm stx q(_root_.Expr)
  let e ← checkTypeQ e q(_root_.Expr)
  match e with
  | .some e =>
    match cmd with
    | .reduce => whnf (← reduceAll q((reduce $e).fst))
    | .reduction => whnf (← reduceAll q((reduce $e).snd.down))
  | .none => throwError s!"not an Expr: {repr e}"

elab "reduction" t:term : term => reduce' t .reduction
elab "reduce!" t:term : term => reduce' t .reduce

syntax "reduce_as" : tactic

def reduce_as : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let tgt ← g.getType
    let tgt' ← checkTypeQ tgt q(Prop)
    match tgt' with
    | .some ~q(ParRed $from_e $to_e) =>
      let e' : Q(_root_.Expr) ← whnf (← reduceAll q((reduce $from_e).fst))
      if ← isDefEq to_e e' then
        let proof ← whnf (← reduceAll q((reduce $from_e).snd.down))
        g.assign proof
      else
        throwError s!"reduction failed. {repr e'} is not equal to {repr to_e}"

elab "reduce_as" : tactic => reduce_as

theorem invert_k : Judge α ⸨K.{[m, n]} α β x y⸩ → Judge (Srt m) α ∧ Judge ((~> (Nat.succ n)) α, (Srt n)) β ∧ Judge α x ∧ Judge ⸨β x⸩ y := by
  intro h
  repeat cases_spine
  cases_conv
  
  sorry
