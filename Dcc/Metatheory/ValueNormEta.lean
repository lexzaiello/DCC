import Dcc.Ast
import Dcc.Relation
import Dcc.Reduces
import Dcc.Metatheory.Value
import Dcc.Metatheory.ValueNorm

namespace Expr

namespace Reduced

theorem head (hr : Reduced A D) : ∃ B C, RedEtaReflTrans C D ∧ RedAff A B ∧ (B = C ∨ RedAffTrans B C) ∧ IsNorm RedAff C ∧ IsNorm RedEta D := by
  match hr with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    cases hr₁ using Relation.TransGen.head_induction_on with
    | single h => exact ⟨_, _, hr₂, h, .inl rfl, hn₁, hn₂⟩
    | head h ih => exact ⟨_, _, hr₂, h, .inr ih, hn₁, hn₂⟩

/-theorem Reduced.step_comb₁ (h_f : IsRedComb f 1) (h_r : Reduced (DCC (f x))) : ∃ e' e'',
  RedAff (DCC (f x)) e' ∧ RedAffReflTrans -/

end Reduced

namespace Reduced

/-theorem Reduced.step_comb₁ (h_f : IsRedComb f 1) (h_r : Reduced (DCC (f x))) : ∃ e' e'',
  RedAff (DCC (f x)) e' ∧ RedAffReflTrans -/

end Reduced

theorem TyValue.is_norm_eta (h : TyValue τ) : IsNorm RedEta τ := by
  induction h
  any_goals (
    focus
    intro ⟨_, h⟩
    cases h
    done)
  · intro ⟨_, h⟩
    cases h with
    | pi hr hn_env hrt =>
      cases hrt with
      | pi' h =>
        rename_i h_norm_f_β _ _ _
        exact h_norm_f_β ⟨_, h⟩

theorem TyValue.red_eta (h : TyValue τ) (hr : RedEta τ τ') : False :=
  h.is_norm_eta ⟨_, hr⟩

theorem TyValue.reduces (h : TyValue τ) (hr : Reduces τ τ') : τ' = τ := by
  induction h with
  | pi =>
    have ⟨_, _, hr₁, hn₁, hr₂, hn₂, heq⟩ := hr.pi
    cases heq
    match hr₁.cases_head with
    | .inl h =>
      cases h
      match hr₂.cases_head with
      | .inl h =>
        cases h
        rfl
      | .inr ⟨_, h₁, h₂⟩ =>
        rename_i h_env_value _ _
        cases h_env_value.is_norm_aff.unique_refl (by assumption)
        rfl
    | .inr ⟨_, h₁, h₂⟩ =>
      rename_i h_n_β _ _ _ _
      exact (h_n_β ⟨_, h₁⟩).elim
  | tintro | sort | bot | top | eq =>
    match hr with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      match hr₁.cases_head with
      | .inl h =>
        cases h
        match hr₂.cases_head with
        | .inl h =>
          cases h; rfl
        | .inr ⟨_, h₁, h₂⟩ =>
          cases h₁
      | .inr ⟨_, h₁, h₂⟩ =>
        cases h₁

end Expr
