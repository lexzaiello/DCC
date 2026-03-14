import Dcc.Ast
import Dcc.Eval
import Dcc.Judge
import Qq
import Lean
import Lean.Elab
import Mathlib.Tactic.CasesM

open Expr Qq Lean Meta Elab Tactic

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

def cases_matcher (matcher : Lean.Expr → MetaM Bool) (recursive := false) (allowSplit : Bool := true) : TacticM Unit := do
  Lean.Elab.Tactic.withMainContext do
    let (mvarId :: remainingGoals) := ← getGoals
      | throwError "No goals to solve"

    let goals ← mvarId.casesMatching matcher recursive allowSplit

    setGoals (goals ++ remainingGoals)

syntax "cases_spine" "*"*  : tactic
syntax "lcases_spine" "*"* : tactic

elab "cases_spine" star:"*"* : tactic => do
  cases_matcher (fun (ty : Q(Prop)) => do
      match ty with
      | ~q(Judge $α $x) => do
        if ¬ star.isEmpty then contains_spine (← whnf x) else contains_spine x
      | ~q(ParRed $α $e') => do
        if ¬ star.isEmpty then contains_spine (← whnf α) else contains_spine α
      | _ => pure false)

syntax "cases_conv" "*"* : tactic

elab "cases_conv" star:"*"* : tactic => do
  cases_matcher (fun (ty : Q(Prop)) => do
      match ty with
      | ~q(∃ D, ParRed $A D ∧ ParRed $B D) =>
        if ¬ star.isEmpty then
          pure <| (← contains_spine (← whnf A)) ∨ (← contains_spine (← whnf B))
        else
          pure <| (← contains_spine A) ∨ (← contains_spine B)
      | ~q(ParRed $A $D ∧ ParRed $B $D) =>
        if ¬ star.isEmpty then
          pure <| (← contains_spine (← whnf A)) ∨ (← contains_spine (← whnf B))
        else
          pure <| (← contains_spine A) ∨ (← contains_spine B)
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
    | .some ~q((_root_.reduce $A).fst = $B) =>
      let e' : Q(_root_.Expr) ← whnf (← reduceAll q((_root_.reduce $A).fst))
      if B.hasMVar ∨ (← isDefEq e' B) then
        let proof ← whnf (← reduceAll q((_root_.reduce $A).snd.down))
        g.assign proof
      else
        throwError "could not solve!"
    | .some ~q(ParRed $from_e $to_e) =>
      let e' : Q(_root_.Expr) ← whnf (← reduceAll q((_root_.reduce $from_e).fst))
      if ← isDefEq to_e e' then
        let proof ← whnf (← reduceAll q((reduce $from_e).snd.down))
        g.assign proof
      else
        throwError s!"reduction failed. {repr e'} is not equal to {repr to_e}"

syntax "reduce_equations" : tactic

elab "reduce_equations" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let hyps := ← (← getLCtx).decls.toList.filterMapM (fun decl => do
      decl.bindM (fun (decl : LocalDecl) => do
        let ty' ← checkTypeQ (← whnf decl.type) q(Prop)
        if let some ~q(ParRed $a $b) := ty' then
          let nm : Q(ParRed $a $b) := (Lean.Expr.fvar decl.fvarId)
          let l' := q(ParRed.reduce_complete $nm)
          let post ← mkFreshId
          let nm' := Lean.Name.str post decl.userName.toString
          pure <| .some (Hypothesis.mk nm' q((_root_.reduce $a).fst = $b) l' .default .default)
        else
          pure Option.none))
    let ⟨_fvar, g⟩ ← g.assertHypotheses ⟨hyps⟩
    let (_mvarId :: remainingGoals) := ← getGoals
      | throwError "No goals to solve"
    setGoals (g :: remainingGoals)

elab "reduce_as" : tactic => reduce_as

/-
Algorithm for solving:

Priority of judgment / parred assumptions:
1. contains_spine
2. sort by mentions of other hypotheses
-/

namespace gen

abbrev Level := Q(ℕ)

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

def MExpr.n_args_spine (e : MExpr) : Option ℕ :=
  match e with
  | .K _m _n
  | .K' _m _n
  | .S _m _n _o
  | .next
  | .read
  | .app'
  | .Srt _m    => pure 0
  | .app f _x  => do pure <| (← f.n_args_spine).succ
  | .Pi _m α β => do
    let _ ← α.n_args_spine
    let _ ← β.n_args_spine
    pure 0
  | _ => .none

/-
The number of times this expr references local decls.
-/
def MExpr.n_mentions (e : MExpr) : ℕ :=
  match e with
  | .lean_e (.fvar _v) => 1
  | .lean_e _ => 0
  | .K _m _n
  | .K' _m _n
  | .S _m _n _o
  | .next
  | .read
  | .app'
  | .Srt _m    => 0
  | .app f x   => f.n_mentions + x.n_mentions
  | .Pi _m α β => α.n_mentions + β.n_mentions

def MExpr.unify (e : MExpr) : Q(_root_.Expr) :=
  match e with
  | .lean_e e => e
  | .K m n => q(K.{[$m, $n]})
  | .Srt m => q(Expr.Srt $m)
  | .Pi m α β =>
    let α' : Q(_root_.Expr) := α.unify
    let β' : Q(_root_.Expr) := β.unify
    q(Π.{[$m]} $α', $β')
  | .K' m n => q(K'.{[$m, $n]})
  | .S m n o => q(S.{[$m, $n, $o]})
  | .next => q(next)
  | .read => q(read)
  | .app' => q($)
  | .app f x =>
    let f : Q(_root_.Expr) := f.unify
    let x : Q(_root_.Expr) := x.unify
    q(Expr.app $f $x)

instance MExpr.instToLeanExpr : Lean.ToExpr MExpr where
  toExpr := MExpr.unify
  toTypeExpr := q(_root_.Expr)

/-
Ranks ParRed or Judge proofs by:
1. The number of spines they contain
2. The number of other hypotheses they mention
-/
def rank_solutions [BEq P] {P : MExpr → MExpr → Type} {A : MExpr}
  (solutions : List ((B : MExpr) × P A B)) : List ((B : MExpr) × P A B) :=
  let with_spines_hyps := solutions.map (fun e@⟨B, _sol⟩ =>
    let n_spines := B.n_args_spine
    let n_mentions := B.n_mentions
    ((n_spines, n_mentions), e))

  let le : (Option ℕ × ℕ) × (B : MExpr) × P A B
        → (Option ℕ × ℕ) × (B : MExpr) × P A B → Bool :=
        fun ⟨⟨nargs₁, nm₁⟩, _⟩ ⟨⟨nargs₂, nm₂⟩, _⟩ =>
          match nargs₁, nargs₂ with
          | .some n₁, .some n₂ => n₁ < n₂
          | _, .some _n₂ => false
          | _, _ => nm₁ < nm₂

  ((List.mergeSort with_spines_hyps le).reverse).map Prod.snd

inductive Redex' : MExpr → Prop where
  | k    : Redex' (MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.K m n) α) β) x) y)
  | k'   : Redex' (MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.K' m n) α) β) x) y)
  | s    : Redex' (((MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.S m n o) α) β) γ) x).app y).app z)
  | pi   : Redex' (MExpr.app (.Pi m α β) x)
  | next : Redex' ((MExpr.app .next f).app x)
  | read : Redex' (MExpr.app .read e)
  | app' : Redex' ((((MExpr.app .app' π).app f).app g).app x)

inductive ParRed' : MExpr → MExpr → Type
  | k         : ParRed' x x' → ParRed' (((((MExpr.K m n).app α).app β).app x).app y) x'
  | k'        : ParRed' x x' → ParRed' (((((MExpr.K' m n).app α).app β).app x).app y) x'
  | s         : ParRed' x x' → ParRed' y y' → ParRed' z z'
    → ParRed' (((((((MExpr.S m n o).app α).app β).app γ).app x).app y).app z) (.app (.app x' z') (.app y' z'))
  | next      : ParRed' f f' → ParRed' ((MExpr.next.app f).app x) f'
  | read      : ParRed' e e' → ParRed' (MExpr.read.app e) e'
  | pi        : ParRed' α α' → ParRed' β β' → ParRed' x x'
    → ParRed' ((MExpr.Pi m α β).app x) (MExpr.Pi m (.app α' x') (.app β' x'))
  | app'      : ParRed' π π' → ParRed' f f'
    → ParRed' g g' → ParRed' x x'
    → ParRed' (((MExpr.app (MExpr.app MExpr.app' π) f).app g).app x)
      (MExpr.app (MExpr.app π' (MExpr.app f' x')) (.app g' x'))
  | app       : (¬ Redex' (MExpr.app f x)) → ParRed' f f'
    → ParRed' x x' → ParRed' (.app f x) (.app f' x')
  | pi_val    : ParRed' α α' → ParRed' β β'
    → ParRed' (.Pi m α β) (.Pi m α' β')
  | refl_srt  : ParRed' (.Srt m) (.Srt m)
  | refl_K'   : ParRed' (MExpr.K' m n) (MExpr.K' m n)
  | refl_K    : ParRed' (MExpr.K m n) (MExpr.K m n)
  | refl_S    : ParRed' (MExpr.S m n o) (MExpr.S m n o)
  | refl_next : ParRed' MExpr.next MExpr.next
  | refl_read : ParRed' MExpr.read MExpr.read
  | refl_app' : ParRed' MExpr.app' MExpr.app'

end gen
