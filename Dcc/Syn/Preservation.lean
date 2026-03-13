import Dcc.Syn.Gen
import Dcc.Syn.InferPi
import Dcc.Syn.JudgePi

open Expr

theorem S_well_typed (h₁ : Judge (Srt m) α) (h₂ : Judge ((~> n.succ) α, (Srt n)) β)
  (h₃ : Judge ((Π' o.succ) α
      , (Π' o.succ) β
      , ⸨next ⸨assert (Srt o)⸩⸩) γ)
  (h₄ : Judge ((Π' o) α, (Π' o) β, γ) x)
  (h₅ : Judge ((Π' n) α, β) y)
  (h₆ : Judge α z) : Judge ⸨γ z ⸨y z⸩⸩ ⸨(S m n o) α β γ x y z⸩ := by
  decide_infer

theorem K_well_typed (h₁ : Judge (Srt m) α) (h₂ : Judge ((~> n.succ) α, (Srt n)) β)
  (h₃ : Judge α x) (h₄ : Judge ⸨β x⸩ y) : Judge α ⸨(K m n) α β x y⸩ := by
  decide_infer

theorem I_well_typed (h₁ : Judge (Srt m) α) (h₂ : Judge α x) : Judge α ⸨(I m) α x⸩ := by
  decide_infer

theorem K'_well_typed (h₁ : Judge (Srt m) α) (h₂ : Judge (Srt n) β)
  (h₃ : Judge α x) (h₄ : Judge β y) : Judge α ⸨(K' m n) α β x y⸩ := by
  decide_infer

theorem I.diamond' (ih : ∀ {c : Expr}, ParRed x c → ∃ d, ParRed x' d ∧ ParRed c d) : ParRed (((Expr.I _m).app _α).app x) c → ∃ d, ParRed x' d ∧ ParRed c d := by
  intro h
  cases_spine
  · simp_all
  · extract_conv; decide_conv

theorem K.diamond (ih : ∀ {c : Expr}, ParRed x c → ∃ d, ParRed x' d ∧ ParRed c d) (h_red : ParRed (((((Expr.K _m _n).app _α).app _β).app x).app _y) c) : ∃ d, ParRed x' d ∧ ParRed c d := by
  cases_spine
  · extract_conv; decide_conv
  · extract_conv; decide_conv

theorem K'.diamond (ih : ∀ {c : Expr}, ParRed x c → ∃ d, ParRed x' d ∧ ParRed c d) (h_red : ParRed (((((Expr.K' _m _n).app _α).app _β).app x).app _y) c) : ∃ d, ParRed x' d ∧ ParRed c d := by
  cases_spine
  · extract_conv; decide_conv
  · extract_conv; decide_conv

theorem ParRed.diamond : ParRed a b → ParRed a c → ∃ d, ParRed b d ∧ ParRed c d := by
  intro ha hb
  induction ha generalizing c
  · cases_spine; decide_conv
  · cases_spine; decide_conv
  · cases_spine; decide_conv
  · cases_spine; decide_conv
  · cases_spine; decide_conv
  · cases_spine; decide_conv
  · cases_spine; decide_conv
  · cases_spine; decide_conv
  · cases_spine; decide_conv
  · cases_spine; decide_conv
  · cases_spine
    simp_all
    extract_conv
    decide_conv
  · cases_spine
    simp_all
    extract_conv
    decide_conv
  · cases_spine
    simp_all
    extract_conv
    decide_conv
  · cases_spine
    rename_i hpx₁ hpy₁ hpz₁ ih₁ ih₂ ih₃ _ _ _ hpx₂ hpy₂ hpz₂
    have ha := ih₁ hpx₂
    have hb := ih₂ hpy₂
    have hc := ih₃ hpz₂
    have ⟨d₁, heq₁, heq₂⟩ := ha
    have ⟨d₂, heq₃, heq₄⟩ := hb
    have ⟨d₃, heq₅, heq₆⟩ := hc
    refine ⟨⸨⸨d₁ d₃⸩ ⸨d₂ d₃⸩⸩, ?_, ?_⟩
    apply ParRed.app
    repeat (apply ParRed.app; repeat assumption)
    rename_i hpx₁ hpy₁ hpz₁ ih₁ ih₂ ih₃ _ _ _ _ _ _ _ _ _ _ _ _
    rename_i hpz₂ x'₄ hpy₂ x'₃ hpx₂ x'₂ hpγ x'₁ hpβ x' hα
    rename_i m n o _ _ _ _
    have ha := ih₁ hpx₂
    have hb := ih₂ hpy₂
    have hc := ih₃ hpz₂
    have ⟨d₁, heq₁, heq₂⟩ := ha
    have ⟨d₂, heq₃, heq₄⟩ := hb
    have ⟨d₃, heq₅, heq₆⟩ := hc
    refine ⟨_, ?_, ParRed.S (_m := m) (_n := n) (_o := o) (_α := x') (_β := x'₁) (_γ := x'₂) heq₂ heq₄ heq₆⟩
    apply ParRed.app
    repeat (apply ParRed.app; repeat assumption)
  · cases_spine
    rename_i m _ _ _ ih₁ ih₂ ih₃ _ _ _ hpα hpβ hpx
    have ha := ih₁ hpα
    have hb := ih₂ hpβ
    have hc := ih₃ hpx
    have ⟨d₁, heq₁, heq₂⟩ := ha
    have ⟨d₂, heq₃, heq₄⟩ := hb
    have ⟨d₃, heq₅, heq₆⟩ := hc
    refine ⟨_, ?_, ParRed.Pival (.app heq₂ heq₆) (.app heq₄ heq₆)⟩
    apply ParRed.Pival
    repeat (apply ParRed.app; repeat assumption)
    rename_i m _ _ _ ih₁ ih₂ ih₃ _ hpx _ _ hpα hpβ
    have ha := ih₁ hpα
    have hb := ih₂ hpβ
    have hc := ih₃ hpx
    have ⟨d₁, heq₁, heq₂⟩ := ha
    have ⟨d₂, heq₃, heq₄⟩ := hb
    have ⟨d₃, heq₅, heq₆⟩ := hc
    refine ⟨_, ?_, ParRed.Pi heq₂ heq₄ heq₆⟩
    apply ParRed.Pival
    repeat (apply ParRed.app; repeat assumption)
  · cases_spine
    rename_i ih₁ ih₂ _ _ hpα hpβ
    have ha := ih₁ hpα
    have hb := ih₂ hpβ
    have ⟨d₁, heq₁, heq₂⟩ := ha
    have ⟨d₂, heq₃, heq₄⟩ := hb
    exact ⟨_, .Pival heq₁ heq₃, .Pival heq₂ heq₄⟩
  · cases_spine
    simp_all
    rename_i h_ff' ih _ h_xx' _ h_fx'
    have ha := ih h_fx'
    have ⟨d, heq₁, heq₂⟩ := ha
    refine ⟨_, heq₁, ?_⟩
    apply ParRed.next
    assumption
  · cases_spine
    simp_all
    extract_conv; decide_conv
  · cases_spine
    simp_all
    rename_i h_ff' ih _ h_xx' _ h_fx'
    have ha := ih h_fx'
    have ⟨d, heq₁, heq₂⟩ := ha
    refine ⟨_, heq₁, ?_⟩
    apply ParRed.assert
    assumption
  · cases_spine
    rename_i hf'₂ hg'₂ hx'₂ ih₁ ih₂ ih₃ _ _ _ hf' hg' hx'
    have ha := ih₁ hf'
    have hb := ih₂ hg'
    have hc := ih₃ hx'
    have ⟨d₁, heq₁, heq₂⟩ := ha
    have ⟨d₂, heq₃, heq₄⟩ := hb
    have ⟨d₃, heq₅, heq₆⟩ := hc
    refine ⟨_, (.app (.app .refl (.app heq₁ heq₅)) (.app heq₃ heq₅)), ?_⟩
    apply ParRed.app
    apply ParRed.app
    exact .refl
    repeat (apply ParRed.app; assumption)
    assumption
    apply ParRed.app
    assumption
    assumption
    rename_i ih₁ ih₂ ih₃ _ hx _ hg _ hf _ hπ
    have ha := ih₁ hf
    have hb := ih₂ hg
    have hc := ih₃ hx
    have ⟨d₁, heq₁, heq₂⟩ := ha
    have ⟨d₂, heq₃, heq₄⟩ := hb
    have ⟨d₃, heq₅, heq₆⟩ := hc
    refine ⟨_, ?_, .app' heq₂ heq₄ heq₆⟩
    apply ParRed.app
    apply ParRed.app
    assumption
    repeat (apply ParRed.app; repeat assumption)
  
  sorry

theorem ParRed.preservation (h_step : ParRed x x') (h_t : Judge α x) : Judge α x' := by
  induction h_t with
  | app =>
    
    sorry
  | conv => sorry
  | _ => cases h_step; decide_infer
