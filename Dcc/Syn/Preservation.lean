import Dcc.Syn.JudgePi
import Dcc.Syn.Confluence
import Lean
import Qq
open Qq

syntax "gen_reduce" : tactic
syntax "convpi" : tactic
syntax "subst" : tactic

theorem gen_imp_well_typed : Judge α x → (gen α).fst = β → Judge β x := fun h_t h_g =>
  Judge.conv h_t ⟨β, gen.sound h_g, .refl⟩

theorem gen_pi {m : Level} {α β x : Expr} : ∃ α' β', (gen ⸨((Π' m) α, β) x⸩).fst = ((Π' m) α', β') := by
  cases h₁ : (gen ⸨((Π' m) α, β) x⸩).fst with
  | _ =>
    unfold gen at h₁
    repeat split at h₁
    simp_all

inductive gen.eq : Expr → Expr → Prop
  | step  : (gen a).fst = b → gen.eq a b
  | trans : gen.eq a b → gen.eq b c → gen.eq a c

def judge.step_gen : Judge α x → gen.eq α β → Judge β x := by
  intro h_t h_eq
  induction h_eq with
  | step => exact gen_imp_well_typed (by assumption) (by assumption)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₂ (ih₁ (by assumption))

inductive gen.judge_conv : Expr → Expr → Prop
  | zero : Judge α x → judge_conv α x
  | succ : gen.judge_conv α₂ x → (gen α₁).fst = α₂ → gen.judge_conv α₁ x

@[simp] theorem gen.eq.of_gen : (gen a).fst = b → gen.eq a b := gen.eq.step

def gen.n_norm (n : ℕ) (e : Expr) : ((e' : Expr) × (PLift <| gen.eq e e')) :=
  match n with
  | .zero => ⟨(gen e).fst, ⟨gen.eq.step (a := e) (b := (gen e).fst) rfl⟩⟩
  | .succ n =>
    let ⟨inner, ⟨h⟩⟩ := gen.n_norm n e
    ⟨(gen inner).fst, ⟨gen.eq.trans h (.step (b := (gen inner).fst) rfl)⟩⟩

def gen.judge_conv.judge : gen.judge_conv α x → Judge α x := by
  intro h
  induction h with
  | zero h => exact h
  | succ ih h_gen h_t =>
    apply Judge.conv
    assumption
    case succ α₂ h α₁ =>
      exact ⟨α₂, .refl, gen.sound h_gen⟩

def find_judge (tgt : Lean.Expr) : Lean.Elab.Tactic.TacticM (Option Lean.FVarId) := do
  let lctx ← Lean.MonadLCtx.getLCtx
  for localDecl in lctx do
    if localDecl.isImplementationDetail then continue
    let type := localDecl.type
    if type.isAppOfArity ``Judge 2 then
      let args := type.getAppArgs
      let xInCtx := args[1]!
      if ← Lean.Meta.isDefEq xInCtx tgt then
        return some localDecl.fvarId
  return none

def dec_n (m : Lean.Expr) : Lean.Elab.Tactic.TacticM ℕ := do
    match ← Lean.Meta.getNatValue? m with
    | .some n => pure n
    | _ => throwError "not a valid sort"

def decode (e : Lean.Expr) : Lean.Elab.Tactic.TacticM Expr :=
  match e with
  | .app (.const `Expr.Srt []) m  => .Srt <$> dec_n m
  | .app (.app (.app (.const `Expr.Pi []) m) α) β => do
    return .Pi (← dec_n m) (← decode α) (← decode β)
  | (.app (.app (.const `Expr.K' []) m) n) => do
    return .K' (← dec_n m) (← dec_n n)
  | (.app (.app (.const `Expr.K []) m) n) => do
    return .K (← dec_n m) (← dec_n n)
  | (.app (.app (.app (.const `Expr.S []) m) n) o) => do
    return .S (← dec_n m) (← dec_n n) (← dec_n o)
  | (.app (.const `Expr.I []) m) => do
    return .I (← dec_n m)
  | .const `Expr.hole [] => return .hole
  | .const `Expr.next [] => return .next
  | .const `Expr.read [] => return .read
  | .const `Expr.assert [] => return .assert
  | .const `Expr.app' [] => return .app'
  | (.app (.app (.const `Expr.app []) f) x) => return .app (← decode f) (← decode x)
  | _ => throwError "not supported"

def Expr.toLeanExpr : Expr → Q(Expr)
  | .Srt m => q(Expr.Srt $m)
  | .app' => q(Expr.app')
  | .hole => q(Expr.hole)
  | .read => q(Expr.read)
  | .assert => q(Expr.assert)
  | .next => q(Expr.next)
  | .I m => q(Expr.I $m)
  | .K' m n => q(Expr.K' $m $n)
  | .K m n => q(Expr.K $m $n)
  | .S m n o => q(Expr.S $m $n $o)
  | .Pi m α β => (((Lean.Expr.const `Expr.Pi []).app (Lean.mkNatLit m)).app (α.toLeanExpr)).app (β.toLeanExpr)
  | .app f x => ((Lean.Expr.const `Expr.app []).app (f.toLeanExpr)).app (x.toLeanExpr)

instance Expr.instToExpr : Lean.ToExpr Expr where
  toExpr := Expr.toLeanExpr
  toTypeExpr := Lean.Expr.const `Expr []

elab "gen_judge" steps:num* : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let target : Q(Prop) ← goal.getType
    let proof ← match target with
    | ~q(Judge $α $x) =>
      match ← find_judge x with
      | .some e =>
        let n_steps := (steps.toList.head?.getD (Lean.Syntax.mkNatLit 100)).getNat
        let rec do_gen (h_judge : Lean.Expr) (e : Q(Expr)) (n : ℕ) : (Lean.Elab.Tactic.TacticM Lean.Expr) := do
          let h : Q(((e' : Expr) × (PLift (Reduces $e e')))) := ← Lean.Meta.reduceAll q(gen $e)
          let mjudge : Lean.Expr := ((Lean.Expr.const `Judge.conv []).app h_judge).app
              (.app
                ((Lean.Expr.const `Prod.mk []).app ((Lean.Expr.const `Sigma.fst []).app h))
                (.app (.const `gen.sound []) (.const `rfl [])))
          match n with
          | .zero => return mjudge
          | .succ n => do_gen mjudge q(Sigma.fst $h) n
        let hyp := Lean.mkFVar e
        let proof ← do_gen hyp x n_steps
        let m ← Lean.mkFreshMVarId
        m.assign proof
        Lean.Elab.Tactic.replaceMainGoal [m]
      | .none => throwError "no matching hypothesis"
    | _ => throwError "not supported"

@[simp] theorem judge_self : ∃ C, ParRed a C ∧ ParRed a C :=
  ⟨a, .refl, .refl⟩

macro_rules
  | `(tactic| subst) => `(tactic| exact ⟨_, .app (.app (.Pi .refl .refl .refl) .refl) .refl, .refl⟩)
  | `(tactic| convpi) => `(tactic| exact ⟨_, ParRed.Pi .refl .refl .refl, .refl⟩)
  | `(tactic| gen_reduce) => `(tactic| exact ⟨(gen _).fst, (gen _).snd.down.hpar, by
    unfold gen
    split
    exact ParRed.refl⟩ )

open Expr

theorem I_well_typed (h_α : Judge (Srt m) α) (h_x : Judge α x) : Judge α ⸨(I m) α x⸩ := by
  apply Judge.conv
  apply Judge.app
  apply Judge.conv
  apply Judge.app
  apply Judge.I
  assumption
  refine ⟨Srt m, .refl, .refl⟩
  apply ParRed.Pi .refl .refl
  exact ParRed.refl
  refine ⟨_, .Pival (.read .refl) .refl, .refl⟩
  assumption
  refine ⟨_, .refl, .refl⟩
  exact ParRed.assert .refl
  exact ⟨_, .refl, .refl⟩

@[simp] theorem arrows_well_typed {n : Level} {α β : Expr} : Judge (Srt n) ((~> n) α, β) := by
  apply Judge.conv
  apply Judge.Pi
  exact ⟨_, .refl, .refl⟩

theorem assert_n' {n : ℕ} {fn : Expr} : ∃ e₁ e₂ e₃ e₄, ParRed ⸨(assert_n n.succ fn) x y⸩ e₁ ∧ ParRed e₁ e₂ ∧ ParRed e₂ e₃ ∧ ParRed e₃ e₄ ∧ ParRed e₄ ⸨(assert_n n fn) x⸩ := by
  unfold assert_n
  induction n with
  | zero | succ n h =>
    simp_all
    refine ⟨_, .app (.app' .refl .refl .refl) .refl, ?_⟩
    refine ⟨_, .app (.app (.read .refl) .refl) .refl, ?_⟩
    refine ⟨_, (.app (.app (.assert .refl) .refl) (.refl)), ?_⟩
    exact ⟨_, .assert .refl, .refl⟩

theorem K.well_typed (h_α : Judge (Srt m) α) (h_β : Judge ((~> n.succ) α, (Srt n)) β)
  (h_x : Judge α x) (h_y : Judge ⸨β x⸩ y) : Judge α ⸨(K m n) α β x y⸩ := by
  have ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ := assert_n' (x := α) (y := β) (n := 2) (fn := .read)
  apply Judge.app
  apply Judge.app
  apply Judge.app
  apply Judge.app
  apply Judge.K
  assumption
  exact judge_self
  exact gen.sound heq₁
  assumption
  refine ⟨_, ?_, .refl⟩
  
