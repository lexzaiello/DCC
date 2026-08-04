import Dcc.Eta.Nbe.Core

universe u

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace NormExpr

namespace EtaFn

namespace Canonicalize

open GenericExpr in
def iso {e_f₁ : EtaFn (τ_c := τ_c) ⟨f₁, hn_f₁⟩ doms} {e_f₂ : EtaFn (τ_c := τ_c) ⟨f₂, hn_f₂⟩ doms}
  (h₁ : Canonicalize e_f₁ e_f₂) (hrt₁ : RedAffNorm (DCC? (f₁ x)) B) (hrt₂ : RedAffNorm (DCC? (f₂ x)) C) : B = C := by
  cases h₁ with
  | id₁ =>
    expose_names
    
    sorry

end Canonicalize

end EtaFn

namespace EtaTm

namespace Canonicalize

set_option maxHeartbeats 100000000000 in
def is_norm_tm {e_f₁ : EtaTm (τ_c := τ_c) f₁ doms} {e_f₂ : EtaTm (τ_c := τ_c) f₂ doms}
  {e_f₃ : EtaTm (τ_c := τ_c) f₃ doms} (h₁ : Canonicalize e_f₁ e_f₂) (h₂ : Canonicalize e_f₂ e_f₃) : f₂ = f₃ := by
  cases h₁ with
  | fn h₁ =>
    cases h₂ with
    | fn h₂ => exact h₁.is_norm_fn h₂
  | pi =>
    cases h₂ with
    | pi =>
      expose_names
      simp_all
      
      sorry

end Canonicalize

namespace Canonicalize!

set_option maxHeartbeats 100000000000 in
def is_norm_fn {e_f₁ : EtaTm (τ_c := τ_c) f₁ doms} {e_f₂ : EtaTm (τ_c := τ_c) f₂ doms}
  {e_f₃ : EtaTm (τ_c := τ_c) f₃ doms} (h₁ : Canonicalize! e_f₁ e_f₂) (h₂ : Canonicalize! e_f₂ e_f₃) : f₂ = f₃ := by
  cases h₁ with
  | step h₁ =>
    cases h₂ with
    | step h₂ => exact h₁.is_norm_fn h₂
    | refl h₂ => rfl
  | refl =>
    cases h₂ with
    | step h₂ =>
      rename_i hn
      exact (hn h₂).elim
    | refl h₂ => rfl

end Canonicalize!

end EtaTm

end NormExpr

namespace GenericExpr

def is_norm_fn {f₁ f₂ f₃ : @GenericExpr τ_c} (h₁ : Canonicalize! f₁ f₂) (h₂ : Canonicalize! f₂ f₃) : f₂ = f₃ := by
  cases h₁ with
  | step h₁ =>
    cases h₂ with
    | step h₂ =>
      expose_names
      cases h₂.elim_norm (IsNorm.from_eta (by assumption) (by assumption))--check redaffnorm
      let heq_f₄ := to_eta_right_inv hn
      let h_expr : (NormExpr.mk f₄ hn_f₄) =
        (NormExpr.mk (f₄.eta_to_expr hn).expr_to_eta (IsNorm.to_eta (RedAffNorm.is_norm h₂))) :=
          NormExpr.ext (by simp [heq_f₄])
      revert e_f' a e_f_1
      rw [← h_expr]
      intro e_f' a e_f_1 b
      cases e_f'.unique e_f_1
      cases e_f'.eq e_f_1
      have h := a.is_norm_fn b
      simp_all
    | refl₁ =>
      expose_names
      cases hrt.elim_norm (IsNorm.from_eta (by assumption) (by assumption))--check redaffnorm
      let heq_f₄ := to_eta_right_inv hn
      let h_expr : (NormExpr.mk f₄ hn_f₄) =
        (NormExpr.mk (f₄.eta_to_expr hn).expr_to_eta (IsNorm.to_eta (RedAffNorm.is_norm hrt))) :=
          NormExpr.ext (by simp [heq_f₄])
      revert e_f' a hn_1
      rw [← h_expr]
      intros
      expose_names
      rfl
    | refl₂ =>
      expose_names
      cases hrt.elim_norm (IsNorm.from_eta (by assumption) (by assumption))--check redaffnorm
      let heq_f₄ := to_eta_right_inv hn
      let h_expr : (NormExpr.mk f₄ hn_f₄) =
        (NormExpr.mk (f₄.eta_to_expr hn).expr_to_eta (IsNorm.to_eta (RedAffNorm.is_norm hrt))) :=
          NormExpr.ext (by simp [heq_f₄])
      revert e_f' a e_f_1
      rw [← h_expr]
      intros
      expose_names
      rfl
  | refl₁ =>
    cases h₂ with
    | refl₁ | refl₂ => rfl
    | step =>
      expose_names
      cases hrt.unique hrt_1
      cases hn_f₂.eq hn_f₂_1
      exact (hn (by
        cases hrt.out_eq
        cases hrt_1.out_eq
        cases hrt.eq
        cases hrt_1.eq
        exact e_f)).elim
  | refl₂ =>
    expose_names
    cases h₂ with
    | refl₂ | refl₁ => rfl
    | step =>
      expose_names
      cases hrt.unique hrt_1
      cases hn_f₂.eq hn_f₂_1
      cases hrt.out_eq
      cases hrt_1.out_eq
      cases hrt.eq
      cases hrt_1.eq
      cases e_f.unique e_f_1
      cases e_f.eq e_f_1
      have ha := a.complete
      have hb := a_1.complete
      simp_all
      cases ha.left; cases ha.right
      simp_all

end GenericExpr
