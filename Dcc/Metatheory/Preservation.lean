import Dcc.Judge
import Dcc.Metatheory.Congr
import Dcc.Metatheory.Decidability
import Dcc.Metatheory.Congr

namespace Expr

namespace Judge

theorem norm_eta (ht : Judge e τ) : IsNorm RedEta τ := by
  cases ht
  any_goals (exact Reduces.norm_eta (by assumption))
  case tintro | bot | top | sort =>
    intro ⟨_, h⟩
    cases h
  case eq =>
    intro ⟨_, h⟩
    cases h

theorem invert (ht : Judge e τ) (heq : e = (DCC (f x))) : ∃ f_α f_β env α,
  (Judge f (DCC (Π(f_α, f_β) env)) ∧ Reduces (DCC (f_α env)) α
    ∧ Judge x α ∧ Reduces (DCC (f_β env x)) τ) := by
  induction ht with
  | app h_t_f h_r_α h_t_x h_r_τ =>
    cases heq
    exact ⟨_, _, _, _, h_t_f, h_r_α, h_t_x, h_r_τ⟩
  | _ => grind

@[dcc_judge]
theorem unique (h₁ : Judge e τ₁) (h₂ : Judge e τ₂) : τ₁ = τ₂ := by
  have ha := h₁.complete
  have hf := h₂.complete
  simp_all

end Judge

namespace Judge

theorem norm_aff (ht : Judge e τ) : IsNorm RedAff τ := by
  cases ht <;> (first
    | exact Reduces.norm_aff (by assumption)
    | exact fun ⟨_, h⟩ => by cases h)

end Judge

end Expr
