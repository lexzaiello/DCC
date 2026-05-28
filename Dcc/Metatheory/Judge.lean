import Dcc.Judge
import Dcc.Metatheory.Congr
import Dcc.Metatheory.Decidability

namespace Expr

namespace Judge

@[dcc_judge]
theorem unique (h₁ : Judge e τ₁) (h₂ : Judge e τ₂) : τ₁ = τ₂ := by
  have ha := h₁.complete
  have hf := h₂.complete
  simp_all

theorem invert (ht : Judge e τ) (heq : e = (DCC (f x))) : ∃ f_α f_β env α,
  (Judge f (DCC (Π(f_α, f_β) env)) ∧ Reduces (DCC (f_α env)) α
    ∧ Judge x α ∧ Reduces (DCC (f_β env x)) τ) := by
  induction ht with
  | app h_t_f h_r_α h_t_x h_r_τ =>
    cases heq
    exact ⟨_, _, _, _, h_t_f, h_r_α, h_t_x, h_r_τ⟩
  | _ => grind

theorem norm_eta (ht : Judge e τ) : IsNorm RedEta τ := by
  cases ht
  any_goals (exact Reduces.norm_eta (by assumption))
  case tintro | bot | top | sort =>
    intro ⟨_, h⟩
    cases h
  case eq =>
    intro ⟨_, h⟩
    cases h

theorem norm_aff (ht : Judge e τ) : IsNorm RedAff τ := by
  cases ht <;> (first
    | exact Reduces.norm_aff (by assumption)
    | exact fun ⟨_, h⟩ => by cases h)

theorem red_eta (ht : Judge e τ) (hr : RedEta τ τ' ) : Judge e τ' := by
  have h₁ := ht.norm_aff
  have h₂ := ht.norm_eta
  exact (h₂ ⟨_, (by assumption)⟩).elim

theorem red_eta_refl_trans (ht : Judge e τ) (hr : RedEtaReflTrans τ τ') : Judge e τ' := by
  have h₁ := ht.norm_aff
  have h₂ := ht.norm_eta
  match hr.cases_head with
  | .inl h => cases h; assumption
  | .inr ⟨_, h₁, h₂⟩ =>
    have h := ht.red_eta h₁
    have h_dec := RedEta.instRedRel.decreasing h₁
    exact h.red_eta_refl_trans h₂
termination_by τ.size

theorem red_aff (ht : Judge e τ) (hr : RedAff τ τ' ) : Judge e τ' := by
  have h₁ := ht.norm_aff
  have h₂ := ht.norm_eta
  exact (h₁ ⟨_, (by assumption)⟩).elim

theorem red_aff_refl_trans (ht : Judge e τ) (hr : RedAffReflTrans τ τ') : Judge e τ' := by
  have h₁ := ht.norm_aff
  have h₂ := ht.norm_eta
  match hr.cases_head with
  | .inl h => cases h; assumption
  | .inr ⟨_, h₁, h₂⟩ =>
    have h := ht.red_aff h₁
    have h_dec := RedAff.instRedRel.decreasing h₁
    exact h.red_aff_refl_trans h₂
termination_by τ.size

theorem reduces (ht : Judge e τ) (hr : Reduces τ τ') : Judge e τ' := by
  have h₁ := ht.norm_aff
  have h₂ := ht.norm_eta
  match hr with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    match hr₁.cases_head with
    | .inl h =>
      cases h
      have h := hr₂.elim_norm (by assumption)
      simp_all
    | .inr ⟨_, ha, hb⟩ => exact (h₁ ⟨_, ha⟩).elim

end Judge

end Expr
