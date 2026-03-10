import Dcc.Syn.JudgePi
import Dcc.Syn.Confluence

syntax "gen_reduce" : tactic
syntax "convpi" : tactic
syntax "subst" : tactic

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
  convpi
  apply Judge.conv
  assumption
  exact ⟨α, .refl, .read .refl⟩
  exact ⟨α, .assert .refl, .refl⟩

@[simp] theorem arrows_well_typed {n : Level} {α β : Expr} : Judge (Srt n) ((~> n) α, β) := by
  apply Judge.conv
  apply Judge.Pi
  exact ⟨_, .refl, .refl⟩

theorem assert_n' {n : ℕ} {fn : Expr} : ∃ e₁ e₂ e₃ e₄, ParRed ⸨(assert_n n.succ fn) x y⸩ e₁ ∧ ParRed e₁ e₂ ∧ ParRed e₂ e₃ ∧ ParRed e₃ e₄ ∧ ParRed e₄ ⸨(assert_n n fn) x⸩ := by
  unfold assert_n
  induction n with
  | zero =>
    simp
    unfold comp
    refine ⟨_, .app (.app' .refl .refl .refl) .refl, ?_⟩
    refine ⟨_, .app (.app (.read .refl) .refl) .refl, ?_⟩
    refine ⟨_, (.app (.app (.assert .refl) .refl) (.refl)), ?_⟩
    exact ⟨_, .assert .refl, .refl⟩
  | succ n h =>
    simp_all
    refine ⟨_, .app (.app' .refl .refl .refl) .refl, ?_⟩
    refine ⟨_, .app (.app (.read .refl) .refl) .refl, ?_⟩
    refine ⟨_, (.app (.app (.assert .refl) .refl) (.refl)), ?_⟩
    exact ⟨_, .assert .refl, .refl⟩

theorem K_well_typed (h_α : Judge (Srt m) α) (h_β : Judge ((~> Nat.succ n) α, (Srt n)) β)
  (h_x : Judge α x) (h_y : Judge (β.app x) y) : Judge α (((((K m n).app α).app β).app x).app y) := by
  apply Judge.conv
  apply Judge.app
  apply Judge.conv
  apply Judge.conv
  apply Judge.conv
  apply Judge.app
  apply Judge.conv
  apply Judge.app
  apply Judge.conv
  apply Judge.conv
  apply Judge.app
  apply Judge.K
  assumption
  convpi
  exact ⟨_, .Pival (.Pi .refl .refl .refl) (.Pi .refl .refl .refl), .refl⟩
  apply Judge.conv
  assumption
  exact ⟨_, .refl, .Pival (.read .refl) (.next .refl)⟩
  convpi
  apply Judge.conv
  assumption
  exact ⟨_, .refl, .assert .refl⟩
  subst
  refine ⟨_, .app (.Pi (.app' .refl .refl .refl) (by sorry) .refl) .refl, .refl⟩
  sorry
