import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Red
import Dcc.Metatheory.Value

namespace Expr

theorem IsRedComb.is_norm_aff (h : IsRedComb e m) : IsNorm RedAff e := fun ⟨_, hr⟩ => by
  cases h <;> cases hr
  repeat sorry

theorem Value.is_norm_aff (h : Value e) : IsNorm RedAff e := by
  induction h with
  | pi₁ h_val_f_β =>
    exact fun ⟨_, h⟩ => by
      cases h with
      | pil h =>
        rename_i hn _ _ _
        exact (hn ⟨_, by assumption⟩).elim
      | pir h =>
        rename_i hn _ _
        exact (hn ⟨_, by assumption⟩).elim
  | pi₂ h_val_f_α h_val_f_β h_val_env  =>
    exact fun ⟨_, h⟩ => by
      cases h with
      | congrFun h =>
        cases h with
        | pil h =>
          rename_i hn _ _ _ _
          exact (hn ⟨_, by assumption⟩).elim
        | pir h =>
          rename_i hn _ _  _
          exact (hn ⟨_, by assumption⟩).elim
      | congrArg h =>
        rename_i hn _ _
        exact (hn ⟨_, by assumption⟩).elim
  | refl₁ _ ih =>
    exact fun ⟨_, h⟩ => by
      cases h with
      | congrFun h => cases h
      | congrArg h =>
        exact (ih ⟨_, h⟩).elim
  | refl₂ h_val_f_β h_val_env ih₁ ih₂  =>
    exact fun ⟨_, h⟩ => by
      cases h with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h =>
          exact (ih₁ ⟨_, h⟩).elim
      | congrArg h =>
        exact (ih₂ ⟨_, h⟩).elim
  | top | bot | tintro | sort => exact fun ⟨_, h⟩ => by cases h
  | coup _ ih =>
    exact fun ⟨_, h⟩ => by
      cases h with
    | coup h =>
      exact (ih ⟨_, h⟩).elim
  | eq h₁ h₂ ih₁ ih₂ =>
    intro ⟨_, h⟩
    cases h with
    | eql' hr => exact ih₁ ⟨_, hr⟩
    | eqr' hr => exact ih₂ ⟨_, hr⟩
  | comb h => exact h.is_norm_aff
  | c_app h_c_f h_val_f h_val_x ih₁ ih₂ =>
    cases h_c_f with
    | eql =>
      exact fun ⟨_, h⟩ => by
        cases h with
        | congrFun h => cases h
        | congrArg h => exact (ih₂ ⟨_, h⟩).elim
    | curr =>
      exact fun ⟨_, h⟩ => by
        cases h with
        | congrFun h => cases h
        | congrArg h => exact (ih₂ ⟨_, h⟩).elim

theorem TyValue.is_norm_aff (h : TyValue τ) : IsNorm RedAff τ := by
  induction h
  any_goals (
    focus
    intro ⟨_, h⟩
    cases h
    done)
  · intro ⟨_, h⟩
    cases h with
    | congrFun h =>
      cases h with
      | pil h =>
        rename_i hn _ _ _
        exact (hn.is_norm_aff ⟨_, by assumption⟩).elim
      | pir h =>
        rename_i hn _ _
        exact (hn.is_norm_aff ⟨_, by assumption⟩).elim
    | congrArg h =>
      rename_i hn _
      exact (hn.is_norm_aff ⟨_, by assumption⟩).elim
  case eq h₁ h₂ =>
    intro ⟨_, h⟩
    cases h with
    | eql' =>
      exact (h₁.is_norm_aff (⟨_, by assumption⟩)).elim
    | eqr' =>
      exact (h₂.is_norm_aff (⟨_, by assumption⟩)).elim

theorem TyValue.red_aff (h : TyValue τ) (hr : RedAff τ τ') : False :=
  h.is_norm_aff ⟨_, hr⟩

end Expr
