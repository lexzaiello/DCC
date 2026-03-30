import Dcc.Ast2
import Dcc.Eval2
import Dcc.Judge2
import Qq
import Lean
import Lean.Elab
import Mathlib.Tactic.CasesM
open Expr Qq Lean Meta Elab Tactic

syntax "judge_cases_spine" : tactic
syntax "cases_spine" "*"*  : tactic

def cases_matcher (matcher : Lean.Expr → MetaM Bool) (recursive := false) (allowSplit : Bool := true) : TacticM Unit := do
  Lean.Elab.Tactic.withMainContext do
    let (mvarId :: remainingGoals) := ← getGoals
      | throwError "No goals to solve"

    let goals ← mvarId.casesMatching matcher recursive allowSplit

    setGoals (goals ++ remainingGoals)

def contains_spine (e : Q(_root_.Expr)) : MetaM Bool := do
  match e with
  | ~q(SK App) => pure true
  | ~q(SK id) => pure true
  | ~q(SK pair) => pure true
  | ~q(SK flip) => pure true
  | ~q(SK quot) => pure true
  | ~q(SK Sort $m) => pure true
  | ~q(SK (∘)) => pure true
  | ~q(SK (Λ)) => pure true
  | ~q(SK fst) => pure true
  | ~q(SK snd) => pure true
  | ~q(SK coup) => pure true
  | ~q(SK lens) => pure true
  | ~q(SK K'.{[$m, $n]}) => pure true
  | ~q(SK K.{[$m, $n]}) => pure true
  | ~q(SK S.{[$m, $n, $o]}) => pure true
  | .app (.app (.const ``_root_.Expr.app []) f) _x => contains_spine f
  | _ => pure false

elab "judge_cases_spine" : tactic => do
  cases_matcher (fun (ty : Q(Prop)) => do
      match ty with
      | ~q(Judge $α $x) => do
        contains_spine (← whnf x)
      | _ => pure false)

elab "cases_spine" star:"*"* : tactic => do
  cases_matcher (fun (ty : Q(Prop)) => do
      match ty with
      | ~q(Judge $α $x) => do
        if ¬ star.isEmpty then contains_spine (← whnf x) else contains_spine x
      | ~q(RedTy $α $e') => do
        if ¬ star.isEmpty then contains_spine (← whnf α) else contains_spine α
      | ~q(Reduces $α $e') => do
        if ¬ star.isEmpty then contains_spine (← whnf α) else contains_spine α
      | ~q(RedTyTrans $α $e') => do
        if ¬ star.isEmpty then contains_spine (← whnf α) else contains_spine α
      | _ => pure false)
