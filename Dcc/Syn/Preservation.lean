import Dcc.Syn.JudgePi
import Dcc.Syn.Confluence

syntax "gen_reduce" : tactic
syntax "convpi" : tactic
syntax "subst" : tactic

theorem gen_imp_well_typed : Judge α x → (gen α).fst = β → Judge β x := fun h_t h_g =>
  Judge.conv h_t ⟨β, gen.sound h_g, .refl⟩

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
  apply Judge.conv
  apply Judge.conv
  apply Judge.app
  apply Judge.app
  apply Judge.K
  assumption
  exact ⟨_, .refl, .refl⟩
  exact ParRed.Pi .refl .refl .refl
  apply Judge.conv
  apply Judge.conv
  assumption
  refine ⟨_, .refl, ?_⟩
  apply ParRed.Pival
  apply ParRed.read .refl
  apply ParRed.next
  exact α
  exact ParRed.refl
  refine ⟨_, .refl, .Pi .refl .refl .refl⟩
  exact ⟨_, .refl, .refl⟩
  apply ParRed.app
  exact ParRed.Pi .refl .refl .refl
  exact ParRed.refl
  refine ⟨_, .Pi .refl (.Pi .refl .refl .refl) .refl, .refl⟩
  refine ⟨_, .Pival (.assert .refl) (.Pi .refl .refl .refl), .refl⟩
  assumption
  exact ⟨_, .refl, .refl⟩
  refine .Pi (β' := e₁) (.app (.app' .refl .refl .refl) .refl) e₅ .refl
  apply Judge.conv
  apply Judge.conv
  assumption
  refine ⟨_, .refl, ?_⟩
  apply ParRed.read
  apply ParRed.refl
  
  assumption
  sorry
  --exact e₅
  sorry
