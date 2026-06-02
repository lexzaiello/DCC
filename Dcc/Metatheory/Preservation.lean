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

/-
Judgments cannot contain apps except if they are Π.

This is downstream of Types being values.
-/

end Judge

end Expr
