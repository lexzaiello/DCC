import Dcc.Judge
import Dcc.Metatheory.Value
import Dcc.Metatheory.Congr
import Dcc.Metatheory.Decidability
import Dcc.Metatheory.Congr
import Dcc.Metatheory.Judge

namespace Expr

namespace Judge

theorem ty_is_value (ht : Judge a τ) : τ.TyValue := by
  
  sorry

theorem preservation_value (ht : Judge A τ) (h_t_val : TyValue τ) (hr : RedAff A B) : Judge B τ := by
  induction ht generalizing B
  any_goals (
    focus
    cases hr
    done)
  case coup ih =>
    cases hr with
    | coup h =>
      rename_i hr _
      unfold Coup.type at hr
      cases hr.sort
      rename_i h_t_β _ _
      match h_t_β.ty_is_value with
      | .pi hn h_val => exact Judge.coup (ih (.pi hn h_val) h) (by assumption) (by assumption)
  case mk ih₁ ih₂ ih₃ =>
    rename_i h_t_β _ _ _
    match h_t_β.ty_is_value with
    | .pi hn h_val =>
      cases hr with
      | sigl h =>
        rename_i h_x _ _ βx_red _ _
        exact Judge.mk (ih₁ h_x.ty_is_value h) (by assumption) (by assumption)
          (by assumption) (βx_red.head_trans (.congrArg h)) (by assumption)
      | sigr h =>
        rename_i h_x _ βx_red _ _
        exact Judge.mk (by assumption) (ih₂ h_x.ty_is_value h) (by assumption)
          (by assumption) (by assumption) (by assumption)
  case app h_r_α ih₁ ih₂ =>
    cases hr with
    | congrFun h =>
      rename_i h_t_f _ _ _ _
      exact Judge.app (ih₁ h_t_f.ty_is_value (by assumption)) (by assumption) (by assumption) (by assumption) (by assumption)
    | congrArg h =>
      rename_i h_t_x hrτ _
      have ha := h_r_α.head_trans (.congrArg h)
      exact Judge.app (by assumption) (by assumption) (ih₂ h_t_x.ty_is_value (by assumption)) (by assumption) (by assumption)
    | quot =>
      rename_i ht
      cases ht with
      | quot h_t_B _ hr_ty =>
        have ⟨α', β', heq, hrt₁, hrt₂⟩ := hr_ty.arrow
        cases heq
        rename_i hr
        have h := h_r_α.curr.quot₁
        exact (h_t_B.red_eta_refl_trans (by assumption)).reduces (by assumption)
    | id =>
      rename_i ht
      match ht with
      | .id h_t_α h_r_α₀ hrτ =>
        have h_val_id := ht.ty_is_value
        have ⟨_, _, hrt_id, hn_id, h_r_α, h_n_id', heq⟩ := hrτ.pi
        cases heq
        rename_i hid
        have h := hid.id
        match h_val_id with
        | .pi h_norm h_val_env =>
          have h := hrt_id.curr
          simp_all
          rename_i h_r_α' _
          rename_i h_x_α₁ _ _ _ h_x_α₂
          have h := h_x_α₁.unique h_x_α₂
          have h := h_r_α'
          have h := h_r_α₀.norm_aff.unique_refl h_r_α
          have h := h_r_α'.curr.quot₁
          simp_all
          have h := h_x_α₂.unique h
          simp_all


end Judge

end Expr
