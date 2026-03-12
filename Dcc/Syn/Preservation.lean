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

theorem I.diamond (ih : ∀ {c : Expr}, ParRed x c → ∃ d, ParRed x' d ∧ ParRed c d) : ParRed (((Expr.I _m).app _α).app x) c → ∃ d, ParRed x' d ∧ ParRed c d := by
  intro h
  cases h
  · simp_all
  · rename_i h_i _
    
    cases h_i
    rename_i h_i _
    cases h_i
    have h := ih (by assumption)
    have ⟨d, hx', heq₁⟩ := h
    exact ⟨d, by assumption, .I (by assumption)⟩

theorem K.diamond (ih : ∀ {c : Expr}, ParRed x c → ∃ d, ParRed x' d ∧ ParRed c d) (h_red : ParRed (((((Expr.K _m _n).app _α).app _β).app x).app _y) c) : ∃ d, ParRed x' d ∧ ParRed c d := by
  cases h_red
  · simp_all
  · rename_i ih _
    cases ih
    rename_i ih _
    cases ih
    rename_i ih _
    cases ih
    rename_i ih _
    cases ih
    have h := ih (by assumption)
    have ⟨d, h₁, h₂⟩ := h
    exact ⟨d, h₁, .K h₂⟩

theorem K'.diamond (ih : ∀ {c : Expr}, ParRed x c → ∃ d, ParRed x' d ∧ ParRed c d) (h_red : ParRed (((((Expr.K' _m _n).app _α).app _β).app x).app _y) c) : ∃ d, ParRed x' d ∧ ParRed c d := by
  cases h_red
  · simp_all
  · rename_i ih _
    cases ih
    rename_i ih _
    cases ih
    rename_i ih _
    cases ih
    rename_i ih _
    cases ih
    have h := ih (by assumption)
    have ⟨d, h₁, h₂⟩ := h
    exact ⟨d, h₁, .K' h₂⟩

theorem ParRed.triangle : ParRed a b → ParRed a c → ∃ d, ParRed a d ∧ ParRed c d := by
  intro ha hb
  induction ha
  repeat (cases hb; apply exists_red_self; exists_red)
  cases hb
  simp_all
  exact ⟨_, by decide_red, .refl⟩
  rename_i h _ _
  cases h
  rename_i h _ _
  cases h
  
  sorry

theorem ParRed.diamond : ParRed a b → ParRed a c → ∃ d, ParRed b d ∧ ParRed c d := by
  intro ha hb
  induction ha generalizing c
  · cases hb
    apply exists_red_self
    exists_red
  repeat exact ⟨c, by assumption, ParRed.refl⟩
  · exact I.diamond (by assumption) (by assumption)
  · exact K.diamond (by assumption) (by assumption)
  · exact K'.diamond  (by assumption) (by assumption)
  · cases hb
    rename_i ih₁ ih₂ ih₃ _ _ _  h_x h_y h_z
    have ha := ih₁ (by assumption)
    have hb := ih₂ (by assumption)
    have hc := ih₃ (by assumption)
    have ⟨d₁, _, _⟩ := ha
    have ⟨d₂, _, _⟩ := hb
    have ⟨d₃, _, _⟩ := hc
    exact ⟨⸨⸨d₁ d₃⸩ ⸨d₂ d₃⸩⸩, .app (.app (by assumption) (by assumption)) (.app (by assumption) (by assumption)), .app (.app (by assumption) (by assumption)) (.app (by assumption) (by assumption))⟩
    rename_i h _
    cases h
    rename_i h _
    cases h
    rename_i h _
    cases h
    rename_i h _
    cases h
    rename_i h _
    cases h
    rename_i h _
    cases h
    rename_i ih₁ ih₂ ih₃ _ _ _ _ _ _ _ _ _ _ _ _
    have ha := ih₁ (by assumption)
    have hb := ih₂ (by assumption)
    have hc := ih₃ (by assumption)
    have ⟨d₁, _, _⟩ := ha
    have ⟨d₂, _, _⟩ := hb
    have ⟨d₃, _, _⟩ := hc
    exact ⟨⸨⸨d₁ d₃⸩ ⸨d₂ d₃⸩⸩, .app (.app (by assumption) (by assumption)) (.app (by assumption) (by assumption)), .S (by assumption) (by assumption) (by assumption)⟩
  cases hb
  rename_i ih₁ ih₂ ih₃ _ _ _  h_x h_y h_z
  have ha := ih₁ (by assumption)
  have hb := ih₂ (by assumption)
  have hc := ih₃ (by assumption)
  have ⟨d₁, _, _⟩ := ha
  have ⟨d₂, _, _⟩ := hb
  have ⟨d₃, _, _⟩ := hc
  exact ⟨(Π' _) ⸨d₁ d₃⸩, ⸨d₂ d₃⸩, .Pival (.app (by assumption) (by assumption)) (.app (by assumption) (by assumption)), .Pival (.app (by assumption) (by assumption)) (.app (by assumption) (by assumption))⟩
  rename_i h _
  cases h
  rename_i ih₁ ih₂ ih₃ _ _ _ _ _ _
  have ha := ih₁ (by assumption)
  have hb := ih₂ (by assumption)
  have hc := ih₃ (by assumption)
  have ⟨d₁, _, _⟩ := ha
  have ⟨d₂, _, _⟩ := hb
  have ⟨d₃, _, _⟩ := hc
  refine ⟨(Π' _) ⸨d₁ d₃⸩, ⸨d₂ d₃⸩, .Pival (.app (by assumption) (by assumption)) (.app (by assumption) (by assumption)), ?_⟩
  apply ParRed.Pi
  repeat assumption
  cases hb
  rename_i ih₁ ih₂ _ _ _ _
  have ha := ih₁ (by assumption)
  have hb := ih₂ (by assumption)
  have ⟨d₁, heq₁, heq₂⟩ := ha
  have ⟨d₂, heq₃, heq₄⟩ := hb
  exact ⟨(Π' _) d₁, d₂, .Pival heq₁ heq₃, .Pival heq₂ heq₄⟩
  cases hb
  simp_all
  rename_i h _
  cases h
  rename_i h _
  cases h
  rename_i ih _ _ _ _
  have h := ih (by assumption)
  have ⟨d, ha, hb⟩ := h
  exact ⟨d, ha, .next hb⟩
  cases hb
  simp_all
  rename_i h _
  cases h
  rename_i ih _ _
  have h := ih (by assumption)
  have ⟨d, ha, hb⟩ := h
  exact ⟨d, ha, .read hb⟩
  cases hb
  simp_all
  rename_i h _
  cases h
  rename_i h _
  cases h
  rename_i ih _ _ _ _
  have h := ih (by assumption)
  have ⟨d, ha, hb⟩ := h
  exact ⟨d, ha, .assert hb⟩
  cases hb
  rename_i ih₁ ih₂ ih₃ _ _ _ _ _ _
  have ha := ih₁ (by assumption)
  have hb := ih₂ (by assumption)
  have hc := ih₃ (by assumption)
  have ⟨d₁, heq₁, heq₂⟩ := ha
  have ⟨d₂, heq₃, heq₄⟩ := hb
  have ⟨d₃, heq₅, heq₆⟩ := hc
  exact ⟨_, .app (.app .refl (.app heq₁ heq₅)) (.app heq₃ heq₅), .app (.app .refl (.app heq₂ heq₆)) (.app heq₄ heq₆)⟩
  rename_i h _
  cases h
  rename_i h _
  cases h
  rename_i h _
  cases h
  rename_i h _
  cases h
  rename_i ih₁ ih₂ ih₃ _ hx _ hg _ hf _ hπ
  have ha := ih₁ (by assumption)
  have hb := ih₂ (by assumption)
  have hc := ih₃ (by assumption)
  have ⟨d, heq₁, heq₂⟩ := ha
  have ⟨d₁, heq₃, heq₄⟩ := hb
  have ⟨d₂, heq₅, heq₆⟩ := hc
  refine ⟨_, .app (.app hπ (.app heq₁ heq₅)) (.app heq₃ heq₅), ?_⟩
  apply ParRed.app'
  repeat assumption
  case app f f' x x' h_f h_x ih₁ ih₂ =>
    cases hb
    case app =>
      have h₁ := ih₁ (by assumption)
      have h₂ := ih₂ (by assumption)
      have ⟨d₁, heq₁, heq₂⟩ := h₁
      have ⟨d₂, heq₃, heq₄⟩ := h₂
      exact ⟨⸨d₁ d₂⸩, .app heq₁ heq₃, .app heq₂ heq₄⟩
    cases h_f
    rename_i i _
    cases i
    have h := ih₂ (by assumption)
    repeat sorry

theorem ParRed.preservation (h_step : ParRed x x') (h_t : Judge α x) : Judge α x' := by
  induction h_t with
  | app =>
    
    sorry
  | conv => sorry
  | _ => cases h_step; decide_infer
