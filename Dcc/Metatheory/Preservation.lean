import Dcc.Judge
import Dcc.Metatheory.Value
import Dcc.Metatheory.Congr
import Dcc.Metatheory.Decidability
import Dcc.Metatheory.Congr
import Dcc.Metatheory.Judge

namespace Expr

namespace Judge

@[grind ., grind →, grind <=]
theorem coup_t_x (h : ⊢ ⟦β⟧(x, y) : τ)
  (h_β : ⊢ β : ((α : Sort m) → Sort n)) : ⊢ x : α := by
  match h with
  | .mk h_t_x h_t_β h_r_βx h_t_y h_r_β =>
    grind

@[grind ., grind →, grind <=]
theorem coup_t_y (h : ⊢ ⟦β⟧(x, y) : τ) (h_r_β₀ : Reduces β β') (h_r_β : Reduces (DCC (β' x)) β'') : ⊢ y : β'' := by
  match h with
  | .mk h_t_x h_t_β h_r_βx h_t_y h_r_β =>
    grind

@[grind ., grind →]
theorem coup_fst (h : ⊢ (Fstc(β) ⟦β⟧(x, y)) : α) : ⊢ x : α := by
  match h with
  | .app h_t_f h_r_α h_t_x h_r_env h_r_τ =>
    match h_t_f with
    | .fstc h_t_β h_r_β h_r_fst_τ =>
      clear h h_t_f
      have h_x_α' := coup_t_x h_t_x (by assumption)
      have ⟨_, _, h_r_η, hnη, h_coup, hn_aff, heq⟩ := h_r_fst_τ.pi
      clear h_r_fst_τ
      cases heq
      cases h_r_η.curr
      have h := h_r_τ.curr.quot₁
      cases (h_x_α'.reduces (by assumption)).unique (by assumption)
      exact h_x_α'.reduces (h_r_τ.curr.quot₁)

/-
Force β₂ = β somehow?
Both reduce to a common reduct?


-/

/-theorem coup_fst₂ (h : ⊢ (Fstc(β) ⟦β₂⟧(x, y)) : α) : ⊢ x : α := by
  match h with
  | .app h_t_f h_r_α h_t_x h_r_env h_r_τ =>
    match h_t_f with
    | .fstc h_t_β h_r_β h_r_fst_τ =>
      clear h h_t_f
      match h_t_x with
      | .mk h_t_x h_r_β h_r_β' h_r_βx h_t_y =>
        
        sorry-/

theorem coup_fst₂ (h : ⊢ (Fstc(β) ⟦β₂⟧(x, y)) : α) : ⊢ x : α := by
  match h with
  | .app h_t_f h_r_α h_t_x h_r_env h_r_τ =>
    match h_t_f with
    | .fstc h_t_β h_r_β h_r_fst_τ =>
      clear h h_t_f
      match h_t_x with
      | .mk h_t_x h_r_β h_r_β' h_r_βx h_t_y =>
        have h_x_α' := coup_t_x (by assumption) (by assumption)
        have ⟨_, _, h_r_η, hnη, h_coup, hn_aff, heq⟩ := h_r_fst_τ.pi
        clear h_r_fst_τ
        cases heq
        cases h_r_η.curr
        have h := h_r_α.id
        have h := h_r_τ.curr.quot₁
        rename_i h_x_α''
        cases h_x_α''.unique h_r_env
        have h := h_r_τ.curr.quot₁
        /-have h_x_α' := coup_t_x (x := x) (y := y) (.mk (by sorry) (by sorry) (by sorry) (by sorry) (by sorry))
          (by assumption)-/
        sorry

@[grind ., grind →]
theorem coup_snd (h : ⊢ (Sndc(β) ⟦β⟧(x, y)) : τ) : ⊢ y : τ := by
  match h with
  | .app h_t_f h_r_α h_t_x h_r_env h_r_τ =>
    match h_t_f with
    | .sndc h_t_β h_r_β₀ h_r_fst_τ =>
      match h_t_x with
      | .mk h_t_fst h_t_βx h_r_β h_r_β' h_t_snd =>
        clear h h_t_f
        have h_y_α' := coup_t_y h_t_x (by assumption) (by assumption)
        clear h_t_x
        have ⟨_, _, h_r_η, hnη, h_coup, hn_aff, heq⟩ := h_r_fst_τ.pi
        clear h_r_fst_τ
        cases heq
        cases h_r_α.id
        cases h_r_η.quot
        cases h_r_τ.quot
        rename_i h_r_fstc_comp _ _ _
        have h := (h_r_fstc_comp.comp' (by assumption)).congr_arg (by assumption) .fstc
        cases h_r_β₀.unique h_r_β
        have h := h_r_α.id
        cases h_r_α.id.norm_aff.unique_refl h_coup
        cases h_r_τ.quot
        cases ((h_r_τ.quot.head_trans .comp').head_trans (.congrArg .fstc)).unique (by assumption)
        assumption

/-
Judgments cannot contain apps except if they are Π.

This is downstream of Types being values.
-/

end Judge

end Expr
