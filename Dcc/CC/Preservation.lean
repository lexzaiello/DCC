import Dcc.CC.Ast
import Dcc.CC.Step2
import Dcc.CC.Judge
import Mathlib.Tactic

namespace Expr

namespace Judge

/-
⊢ ((Expr.sort m).quot ((Expr.sort m).sigma (Expr.sort m).id) α).Judge
    (arrow ((Expr.sort m).sigma (Expr.sort m).id) (Expr.sort m) (Nat.succ m) (Nat.succ m))
-/

theorem id_well_typed (h_t_α : Judge α (DCC (Sort m))) (h_t_x : Judge x α) : Judge (DCC (Id(α) x)) α :=
  .conv (.app (.id h_t_α) h_t_x) (⟨_, .single .quot, .refl⟩)

theorem app_invert {e t f x : Expr} (h_t : Judge e t) (heq : e = (DCC (f x))) : ∃ m n α β,
  Judge f (DCC (Π(m, n) α β))
    ∧ Judge x α
    ∧ (∃ C, RedAffReflTrans (DCC (β ⟦Id(Sort m)⟧(α, x))) C ∧ RedAffReflTrans t C) := by
  induction heq₂ : h_t with
  | app h_t_f h_t_x _ _ =>
    simp at heq
    have ⟨h₁, h₂⟩ := heq
    rw [← h₁, ← h₂]
    exact ⟨_, _, _, _, h_t_f, h_t_x, _, .refl, .refl⟩
  | conv _h_t_x h_conv ih =>
    simp_all
    have ⟨C, h₃, h₄⟩ := h_conv
    have ⟨m, n, α, β, h_t_f, h_t_x, D, h₁, h₂⟩ := ih (by rw [← heq]; assumption)
    have ⟨D, h₅, h₆⟩ := h₃.conf h₂
    exact ⟨m, n, α, β, h_t_f, h_t_x, _, .trans h₁ h₆, .trans h₄ h₅⟩
  | _ => contradiction

theorem preserves (h_t : Judge x T) (h_red : Red x x') : Judge x' T := by
  induction h_t generalizing x' with
  | sort | quot | app_e | curr | snd | fst | pair | comp | id =>
    cases h_red
  | app h_t_f h_t_x ih₁ ih₂ =>
    cases h_red with
    | id =>
      have ⟨m, n, α, β, h_t_f, h_t_x, C, h₁, h₂⟩ := (Judge.app h_t_f h_t_x).app_invert rfl
      cases h_t_f
      
      sorry
  | coup => sorry
  | conv => sorry

end Judge

end Expr
