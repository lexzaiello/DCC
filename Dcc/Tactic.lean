import Dcc.Ast
import Dcc.Eval
import Dcc.Judge
import Qq
import Lean
import Lean.Elab
import Mathlib.Tactic.CasesM
open Std (Format)

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
  | .none => throwError m!"not an Expr: {e}"

elab "reduction" t:term : term => reduce' t .reduction
elab "reduce!" t:term : term => reduce' t .reduce

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
  | lean_e : Q(_root_.Expr) → MExpr
deriving BEq, Repr

def MExpr.toFormat : MExpr → Format
  | .lean_e e => format e
  | .Srt m => s!"(Srt {m})"
  | .K' m n => "K'.{" ++ (format [m, n]) ++ "}"
  | .K m n => "K.{" ++ (format [m, n]) ++ "}"
  | .S m n o => "S.{" ++ (format [m, n, o]) ++ "}"
  | .Pi m α β => "Π.{" ++ (format [m]) ++ "}" ++ (.nest 2 <| α.toFormat ++ "," ++ β.toFormat)
  | .app f x => .bracket "⸨" (f.toFormat ++ (.nest 2 <| .line ++ x.toFormat)) "⸩"
  | .app' => "$"
  | .next => "next"
  | .read => "read"

instance : ToFormat MExpr := ⟨MExpr.toFormat⟩
instance : ToString MExpr := ⟨toString ∘ MExpr.toFormat⟩

def MExpr.decode (e : Lean.Expr) : MExpr :=
  match e with
  | (.app (.app (.const `Expr.app []) f) x) => .app (decode f) (decode x)
  | .app (.app (.app (.const ``Expr.Pi []) m) α) β =>
    let α' := decode α
    let β' := decode β
    .Pi m α' β'
  | .app (.const ``Expr.Srt []) m  => .Srt m
  | (.app (.app (.const `Expr.K' []) m) n) => .K' m n
  | (.app (.app (.const `Expr.K []) m) n) => .K m n
  | (.app (.app (.app (.const `Expr.S []) m) n) o) => .S m n o
  | .const `Expr.next [] => .next
  | .const `Expr.read [] => .read
  | .const `Expr.app' [] => .app'
  | e => .lean_e e

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

inductive MExpr.PRedex' : MExpr → Prop where
  | k    : PRedex' (MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.K m n) α) β) x) y)
  | k'   : PRedex' (MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.K' m n) α) β) x) y)
  | s    : PRedex' (((MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.S m n o) α) β) γ) x).app y).app z)
  | pi   : PRedex' (MExpr.app (.Pi m α β) x)
  | next : PRedex' ((MExpr.app .next f).app x)
  | read : PRedex' (MExpr.app .read e)
  | app' : PRedex' ((((MExpr.app .app' π).app f).app g).app x)

inductive MExpr.TmRedex' : MExpr → Type where
  | k    : TmRedex' (MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.K m n) α) β) x) y)
  | k'   : TmRedex' (MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.K' m n) α) β) x) y)
  | s    : TmRedex' (((MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.S m n o) α) β) γ) x).app y).app z)
  | pi   : TmRedex' (MExpr.app (.Pi m α β) x)
  | next : TmRedex' ((MExpr.app .next f).app x)
  | read : TmRedex' (MExpr.app .read e)
  | app' : TmRedex' ((((MExpr.app .app' π).app f).app g).app x)

theorem MExpr.TmRedex'.sound : MExpr.TmRedex' e → e.PRedex' := fun h => by
  cases h
  · exact .k
  · exact .k'
  · exact .s
  · exact .pi
  · exact .next
  · exact .read
  · exact .app'

def MExpr.is_redex (e : MExpr) : Option (TmRedex' e) :=
  match e with
  | (MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.K _m _n) _α) _β) _x) _y)  => .some TmRedex'.k
  | (MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.K' _m _n) _α) _β) _x) _y) => .some TmRedex'.k'
  | (MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.app (MExpr.S _m _n _o) _α) _β) _γ) _x) _y) _z) => .some TmRedex'.s
  | (MExpr.app (.Pi _m _α _β) _x) => .some TmRedex'.pi
  | (MExpr.app (MExpr.app .next _f) _x) => .some TmRedex'.next
  | (MExpr.app .read _e) => .some TmRedex'.read
  | (MExpr.app (MExpr.app (MExpr.app (MExpr.app .app' _π) _f) _g) _x) => .some TmRedex'.app'
  | _ => .none

inductive ParRed' : MExpr → MExpr → Type
  | lean      {A B : Q(_root_.Expr)} : Q(ParRed $A $B)
    → ParRed' (.lean_e A) (.lean_e B)
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
  | app       : (MExpr.is_redex (MExpr.app f x)).isNone → ParRed' f f'
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

theorem is_redex.sound : MExpr.is_redex e = .some p → e.PRedex' := fun _ => p.sound

theorem PRedex'.is_redex_complete : MExpr.PRedex' e → ∃ p, e.is_redex = some p := fun h => by
  induction h
  repeat exact ⟨_, rfl⟩

theorem PRedex.is_redex_complete' : ¬ MExpr.PRedex' e → ¬ (∃ p, e.is_redex = some p) := fun h ⟨p, _⟩ =>
  absurd p.sound h

instance Redex.instDecidable : Decidable (MExpr.PRedex' e) := by
  match heq : MExpr.is_redex e with
  | .some p => exact .isTrue p.sound
  | .none =>
    apply Decidable.isFalse
    intro h
    cases h
    repeat cases heq

theorem MExpr.is_redex.sound' : is_redex e = Option.none → ¬ e.PRedex' := fun e => by
  intro h
  cases h
  repeat cases e

def MExpr.TmRedex'.toLeanExpr (h : MExpr.TmRedex' A) : Q(_root_.Expr.Redex' $(A.unify)) := by
  cases h
  · exact q(.k)
  · exact q(.k')
  · exact q(.s)
  · exact q(.pi)
  · exact q(.next)
  · exact q(.read)
  · exact q(.app')

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

instance MExpr.instToLeanExpr : Lean.ToExpr MExpr where
  toExpr := MExpr.unify
  toTypeExpr := q(_root_.Expr)

/-
Ranks ParRed or Judge proofs by:
1. The number of spines they contain
2. The number of other hypotheses they mention
-/
def rank_solutions {P : Q(_root_.Expr → _root_.Expr → Prop)} {A : MExpr}
  (solutions : List ((B : MExpr) × Q($P $(MExpr.unify A) $(MExpr.unify B)))) : List ((B : MExpr) × Q($P $(MExpr.unify A) $(MExpr.unify B))) :=
  let with_spines_hyps := solutions.map (fun e@⟨B, _sol⟩ =>
    let n_spines := B.n_args_spine
    let n_mentions := B.n_mentions
    ((n_spines, n_mentions), e))

  let le : (Option ℕ × ℕ) × (B : MExpr) × Q($P $(A.unify) $(B.unify))
        → (Option ℕ × ℕ) × (B : MExpr) × Q($P $(A.unify) $(B.unify)) → Bool :=
        fun ⟨⟨nargs₁, nm₁⟩, _⟩ ⟨⟨nargs₂, nm₂⟩, _⟩ =>
          match nargs₁, nargs₂ with
          | .some n₁, .some n₂ => n₁ < n₂
          | _, .some _n₂ => false
          | _, _ => nm₁ < nm₂

  ((List.mergeSort with_spines_hyps le).reverse).map Prod.snd

open Qq in def parred_solution (A : Q(_root_.Expr)) : TacticM (Option ((B : MExpr) × Q(ParRed $A $(B.unify)))) := do
  let g ← getMainGoal
  g.withContext do
    let potential_solutions : List ((B : MExpr) × Q(ParRed $A $(B.unify))) := ← (← getLCtx).decls.toList.filterMapM (fun (decl : Option LocalDecl) =>
      decl.bindM (fun (decl : LocalDecl)=> do
        let ty' ← checkTypeQ (← whnf decl.type) q(Prop)
        match ty' with
        | .some ~q(ParRed $A' $B) =>
          if ← isDefEq A A' then
            pure <| .some ⟨MExpr.decode B, .fvar decl.fvarId⟩
          else
            pure .none
        | .some ~q((_root_.reduce $A').fst = $B) =>
          if ← isDefEq A A' then
            pure <| .some (⟨MExpr.decode B, .fvar decl.fvarId⟩ : ((B : MExpr) × Q(ParRed $A $(B.unify))))
          else
            pure .none
        | _ => pure Option.none))
    let ranked := rank_solutions potential_solutions (A := MExpr.decode A) (P := q(ParRed))
    pure ranked.head?

def MExpr.reduce (e : MExpr) : TacticM ((e' : MExpr) × ParRed' e e') :=
  match heq : e.is_redex with
  | .some r =>
    match r with
    | .k (m := m) (n := n) (α := α) (β := β) (x := x) (y := y) => do
      let ⟨e', hp⟩ ← reduce x
      pure ⟨e', .k hp⟩
    | .k' (m := m) (n := n) (α := α) (β := β) (x := x) (y := y) => do
      let ⟨e', hp⟩ ← reduce x
      pure ⟨e', .k' hp⟩
    | .s (m := m) (n := n) (o := o) (α := α) (β := β) (γ := γ) (x := x) (y := y) (z := z) => do
      let ⟨x', hx⟩ ← reduce x
      let ⟨y', hy⟩ ← reduce y
      let ⟨z', hz⟩ ← reduce z
      pure ⟨.app (.app x' z') (.app y' z'), .s hx hy hz⟩
    | .pi (m := m) (α := α) (β := β) (x := x) => do
      let ⟨x', hx⟩ ← reduce x
      let ⟨α', hα⟩ ← reduce α
      let ⟨β', hβ⟩ ← reduce β
      pure ⟨.Pi m (.app α' x') (.app β' x'), .pi hα hβ hx⟩
    | .next (f := f) => do
      let ⟨f', hf⟩ ← reduce f
      pure ⟨f', .next hf⟩
    | .read (e := e) => do
      let ⟨e', he⟩ ← reduce e
      pure ⟨e', .read he⟩
    | .app' (π := π) (f := f) (g := g) (x := x) => do
      let ⟨π', hπ⟩ ← reduce π
      let ⟨f', hf⟩ ← reduce f
      let ⟨g', hg⟩ ← reduce g
      let ⟨x', hx⟩ ← reduce x
      pure ⟨.app (.app π' (.app f' x')) (.app g' x'), .app' hπ hf hg hx⟩
  | .none =>
    let not_redex : ¬ e.PRedex' := MExpr.is_redex.sound' heq
    match heq : e with
    | .app f x => do
      let ⟨f', hf⟩ ← reduce f
      let ⟨x', hx⟩ ← reduce x
      pure ⟨.app f' x', .app (by rw [← heq]; simp_all) hf hx⟩
    | .Srt m => pure ⟨.Srt m, .refl_srt⟩
    | .Pi m α β => do
      let ⟨α', hα⟩ ← reduce α
      let ⟨β', hβ⟩ ← reduce β
      pure ⟨.Pi m α' β', .pi_val hα hβ⟩
    | .S m n o => pure ⟨.S m n o, .refl_S⟩
    | .K m n => pure ⟨.K m n, .refl_K⟩
    | .K' m n => pure ⟨.K' m n, .refl_K'⟩
    | .app' => pure ⟨.app', .refl_app'⟩
    | .read => pure ⟨.read, .refl_read⟩
    | .next => pure ⟨.next, .refl_next⟩
    | .lean_e e => do
      let  ⟨B, qhpr⟩ := (← parred_solution e).getD ⟨.lean_e q((reduce $e).fst), q((reduce $e).snd.down)⟩
      pure ⟨.lean_e B.unify, .lean qhpr⟩

def ParRed'.toLeanExpr (h : ParRed' A B) : MetaM Q(_root_.ParRed $(A.unify) $(B.unify)) :=
  match h with
  | .lean h => return h
  | .k hx => do return q(ParRed.k $(← hx.toLeanExpr))
  | .k' hx => do return q(ParRed.k' $(← hx.toLeanExpr))
  | .s hx hy hz => do return q(ParRed.s $(← hx.toLeanExpr) $(← hy.toLeanExpr) $(← hz.toLeanExpr))
  | .next hf => do return q(ParRed.next $(← hf.toLeanExpr))
  | .read he => do return q(ParRed.read $(← he.toLeanExpr))
  | .pi hα hβ hx => do return q(ParRed.pi $(← hα.toLeanExpr) $(← hβ.toLeanExpr) $(← hx.toLeanExpr))
  | .app' hπ hf hg hx => do return q(ParRed.app' $(← hπ.toLeanExpr) $(← hf.toLeanExpr) $(← hg.toLeanExpr) $(← hx.toLeanExpr))
  | .app (f := f) (x := x) _ hf hx => do
    let p ← mkDecideProofQ q(¬ (Redex (_root_.Expr.app $(MExpr.unify f) $(MExpr.unify x))))
    return q(ParRed.app $p $(← hf.toLeanExpr) $(← hx.toLeanExpr))
  | .pi_val hα hβ => do return q(ParRed.pi_val $(← hα.toLeanExpr) $(← hβ.toLeanExpr))
  | .refl_srt (m := m) => do return q(.refl_srt (m := $m))
  | .refl_K' (m := m) (n := n)  => do return q(.refl_comb (c := (.K' $m $n)))
  | .refl_K (m := m) (n := n) => do return q(.refl_comb (c := (.K $m $n)))
  | .refl_S (m := m) (n := n) (o := o) => do return q(.refl_comb (c := (.S $m $n $o)))
  | .refl_next => do return q(.refl_comb (c := .next))
  | .refl_read => do return q(.refl_comb (c := .read))
  | .refl_app' => do return q(.refl_comb (c := .app'))

declare_syntax_cat reduce_cmd
syntax "reduction"        : reduce_cmd
syntax "reduce" term      : reduce_cmd
syntax "check?" term term : reduce_cmd
syntax "check?"           : reduce_cmd
syntax "show" reduce_cmd  : reduce_cmd
syntax "close" reduce_cmd : reduce_cmd

syntax reduce_cmd : term

syntax "smart_reduce" reduce_cmd : tactic

inductive SmartReduce.Cmd where
  | reduction : Cmd
  | reduce    : Q(_root_.Expr) → Cmd
  | c_show    : Cmd → Cmd
  | c_close   : Cmd → Cmd

macro_rules
  | `(reduction) => `(SmartReduce.cmd.reduction)
  | `(reduce $t:term) => `(SmartReduce.cmd.reduce $t:term)
  | `(show $c:reduce_cmd) => do
    let c ← `($c:reduce_cmd)
    `(SmartReduce.cmd.c_show $c:term)
  | `(close $c:reduce_cmd) => do
    let c ← `($c:reduce_cmd)
    `(SmartReduce.cmd.c_close $c:term)

elab "smart_reduce" "close" "reduction" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← g.getType
    let tgt' ← checkTypeQ tgt q(Prop)
    match tgt' with
    | .some ~q((_root_.reduce $A).fst = $B) =>
      let A' := MExpr.decode A
      let B' := MExpr.decode B

      let ⟨E', hpr⟩ ← A'.reduce

      if ¬ (← isDefEq E'.unify B) then
        throwError Format.text "refusing. not def-eq: "
          ++ Format.line
          ++ (format E')
          ++ Format.line ++ (format B')
      else
        let hpr' ← hpr.toLeanExpr
        g.assign q(ParRed.reduce_complete $hpr')
    | .some ~q(ParRed $A $B) =>
      let A' := MExpr.decode A
      let B' := MExpr.decode B

      let ⟨E', hpr⟩ ← A'.reduce

      if ¬ (← isDefEq E'.unify B) then
        throwError Format.text "refusing. not def-eq: "
          ++ Format.line
          ++ (format E')
          ++ Format.line ++ (format B')
      else
        g.assign (← hpr.toLeanExpr)
    | e => throwError s!"not a valid reduction goal: {repr e}"

/-syntax "reduce_as" : tactic

def reduce_as : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let tgt ← g.getType
    let tgt' ← checkTypeQ tgt q(Prop)
    match tgt' with
    | .some ~q((_root_.reduce $A).fst = $B) =>
      let e' : Q(_root_.Expr) ← whnf (← reduceAll q((_root_.reduce $A).fst))
      let B' ← whnf (← reduceAll B)
      if B.hasMVar ∨ (← isDefEq e' B) then
        let proof ← whnf (← reduceAll q((_root_.reduce $A).snd.down))
        g.assign proof
      else
        throwError (Format.text "could not solve: ") ++ (.nest 2 <|
          (format (MExpr.decode e')) ++ Format.line ++ " ≠ " ++ format (MExpr.decode B'))
    | .some ~q(ParRed $from_e $to_e) =>
      let to_e' ← whnf (← reduceAll to_e)
      let e' : Q(_root_.Expr) ← whnf (← reduceAll q((_root_.reduce $from_e).fst))
      if ← isDefEq to_e e' then
        let proof ← whnf (← reduceAll q((reduce $from_e).snd.down))
        g.assign proof
      else
        throwError (Format.text "could not solve: ") ++ (.nest 2 <|
          (format (MExpr.decode e')) ++ Format.line ++ " ≠ " ++ format (MExpr.decode to_e'))-/

elab "reduce_as" : tactic => reduce_as

end gen
