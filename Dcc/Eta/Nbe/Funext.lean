import Dcc.Eta.Nbe.Funext.Unary
import Dcc.Eta.Nbe.Funext.Binary

open GenericExpr

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace NormExpr

namespace EtaFn

namespace Canonicalize

def ext {e_f₁ : EtaFn f₁ doms}
  {e_f₂ : EtaFn f₂ doms}
  {e_f₃ : EtaFn f₃ doms}
  {e_f₄ : EtaFn f₄ doms}
  (h₁ : Canonicalize (τ_c := τ_c) e_f₁ e_f₂)
  (e_h₁ : e_f₂.Holes 0 hole_tms₁)
  (h₂ : Canonicalize (τ_c := τ_c) e_f₃ e_f₄)
  (e_h₂ : e_f₄.Holes 0 hole_tms₂)
  (hrt₁ : RedAffNorm e_h₁.app B)
  (hrt₂ : RedAffNorm e_h₂.app B) : f₂ = f₄ := by
  cases e_f₁ with
  | tm₁ ha =>
    cases e_f₃ with
    | tm₁ hb =>
      expose_names
      cases e_h₁ with
      | tm₁ heq ha =>
        cases heq
        rename_i hole_e₁
        cases e_h₂ with
        | tm₁ heq hb =>
          cases heq
          expose_names
          expose_names
          cases ha.unique hb
          exact h₁.ext₁ h₂ (x := hole_e₁) (B := B) (e_h₀ := (by assumption))
            (by
              simp [NormExpr.to_eta]
              simp [Holes.app, NormExpr.raw, NormExpr.to_eta] at hrt₁
              simp [NormExpr.raw]
              assumption)
            (by
              simp [NormExpr.to_eta]
              simp [Holes.app, NormExpr.raw, NormExpr.to_eta] at hrt₂
              simp [NormExpr.raw]
              assumption)
            hb.is_norm
  | tm₂ h₁ =>
    cases e_f₃ with
    | tm₂ =>
      expose_names
      cases e_h₁ with
      | tm₂ heqa hb =>
        cases e_h₂ with
        | tm₂ heqb hc =>
          expose_names
          cases heqa
          cases heqb
          cases hb.unique hc
          cases e_f.hole_same e_f₄ (.tm₂ rfl (by assumption) (by assumption) (by assumption)) (Holes.tm₂ (Eq.refl α.to_eta) hc a_2 a_3)
          cases h_n_β_1.eq h_n_β
          cases hn_hole₁.eq hn_hole₁_1
          cases a.unique a_2
          cases a_3.unique a_1
          exact h₁.ext₂
            (by assumption)
            (by assumption) h₂
            (x := mk hole₁ hn_hole₁)
            (y := hole₂)
            (B := B)
            (e_h₀ := (by assumption))
            (by
              simp [NormExpr.raw]
              simp [Holes.app, NormExpr.raw, NormExpr.to_eta] at hrt₁
              assumption)
            (by
              simp [NormExpr.raw]
              simp [Holes.app, NormExpr.raw, NormExpr.to_eta] at hrt₂
              assumption)
            hn_hole₁

end Canonicalize

end EtaFn

end NormExpr
