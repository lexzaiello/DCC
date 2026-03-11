import Dcc.Syn.JudgePi
import Dcc.Syn.Gen
import Dcc.Syn.Confluence
import Dcc.Syn.Gen
import Dcc.Syn.InferPi
import Lean

open Expr
open Lean (Level)

syntax "gen_reduce" : tactic
syntax "convpi" : tactic
syntax "subst" : tactic

inductive gen.judge_conv : Expr → Expr → Prop
  | zero : Judge α x → judge_conv α x
  | succ : gen.judge_conv α₂ x → (gen α₁).fst = α₂ → gen.judge_conv α₁ x

#eval (gen ⸨(I.type 1) (Srt 0)⸩).fst

@[simp] theorem judge_self : ∃ C, ParRed a C ∧ ParRed a C :=
  ⟨a, .refl, .refl⟩

macro_rules
  | `(tactic| subst) => `(tactic| exact ⟨_, .app (.app (.Pi .refl .refl .refl) .refl) .refl, .refl⟩)
  | `(tactic| convpi) => `(tactic| exact ⟨_, ParRed.Pi .refl .refl .refl, .refl⟩)

open Expr

theorem I_well_typed (h_α : Judge (Srt m) α) (h_x : Judge α x) : Judge α ⸨(I m) α x⸩ := by
  apply Judge.conv
  apply Judge.app
  apply Judge.conv
  apply Judge.app
  apply Judge.I
  exact .refl
  assumption
  apply ParRed.Pi .refl .refl .refl
  refine ⟨_, .Pival (.read .refl) .refl, .refl⟩
  exact .refl
  assumption
  apply ParRed.assert .refl
  exact judge_self

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
  sorry

theorem I_well_typed' (h_α : Judge (Srt m) α) (h_x : Judge α x) : Judge α ⸨(I m) α x⸩ := by
  sorry
