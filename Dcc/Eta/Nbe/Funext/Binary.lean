import Dcc.Eta.Nbe.Canonicalize.Normal.Core

open GenericExpr

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace NormExpr

namespace EtaFn

namespace Canonicalize

set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
set_option maxHeartbeats 2000000000000 in
def ext₂
  {f₁ f₂ f₃ f₄ : @NormExpr τ_c RedAff}
  {e_f₁ : EtaFn f₁ [α, β₀]} {e_f₂ : EtaFn f₂ [α, β₀]} {e_f₃ : EtaFn f₃ [α, β₀]} {e_f₄ : EtaFn f₄ [α, β₀]}
  {e_h₀ : Hole α.to_eta 2 x}
  (hrt  : RedAffNorm (DCC? (#(expr_to_eta β₀.raw) x.raw)) β)
  (e_h₁ : Hole β 1 y)
  (h₁   : Canonicalize e_f₁ e_f₂) (h₂ : Canonicalize e_f₃ e_f₄)
  (hrt₁ : RedAffNorm (DCC? (f₂.to_eta.raw x.raw y.raw)) B)
  (hrt₂ : RedAffNorm (DCC? (f₄.to_eta.raw x.raw y.raw)) B)
  (hn_x : IsNorm RedAff x.raw) : f₂ = f₄ := by
  cases h₁ with
  | id₂ =>
    expose_names
    cases e_f.hole_same e_f₃ e_h (.tm₂ rfl e_h₀ hrt e_h₁)
    cases e_f.hole_same e_f₄ e_h (.tm₂ rfl e_h₀ hrt e_h₁)
    dcc_simp at hrt
    cases hrt.unique ⟨.single .quot, hn_τ'.to_eta⟩
    cases hrt₁.unique ⟨.single (.congrFun .id), by assumption⟩
    cases h₂ with
    | id₂ => rfl
    | quot₂ =>
      expose_names
      simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₂
      cases heq
      simp [GenericExpr.to_eta_right_inv hn] at hrt₂
      cases hrt₂.unique ⟨.trans (.single (.congrFun .quot)) (.single .quot), by assumption⟩
      have h := e_h.hole_mem_tm ⟨0, e_f.arity_pos⟩
      simp [Holes.v_elems, raw, Vector.get] at h
      grind
  | quot₂ =>
    expose_names
    cases e_f.hole_same e_f₃ e_h (.tm₂ rfl e_h₀ hrt e_h₁)
    cases e_f.hole_same e_f₄ e_h (.tm₂ rfl e_h₀ hrt e_h₁)
    dcc_simp at hrt
    cases heq
    simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₁
    cases hrt₁.unique ⟨.trans (.single (.congrFun .quot)) (.single .quot), by
      simp [GenericExpr.to_eta_right_inv hn]
      assumption⟩
    cases h₂ with
    | id₂ =>
      expose_names
      cases e_f.hole_same e_f₃ (by assumption) e_h_1
      simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₂
      simp [GenericExpr.to_eta_right_inv hn] at hrt₂
      cases hrt₂.unique ⟨(.single (.congrFun .id)), by assumption⟩
      have h_mem := mem_imp_contains_hole (e_h.hole_mem_tm ⟨0, e_f.arity_pos⟩)
      simp [Holes.v_elems, raw, Vector.get] at h_mem
      grind
    | quot₂ =>
      expose_names
      cases e_f.hole_same e_f₃ (by assumption) e_h_1
      simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₂
      simp [GenericExpr.to_eta_right_inv hn] at hrt₂
      cases heq
      cases hrt₂.unique ⟨.trans (.single (.congrFun .quot)) (.single .quot), by
        simp [GenericExpr.to_eta_right_inv hn_1]
        assumption⟩
      simp [GenericExpr.to_eta_right_inv hn_1]
  | quot_bang =>
    expose_names
    cases e_f.hole_same e_f₃ e_h (.tm₂ rfl e_h₀ hrt e_h₁)
    cases e_f.hole_same e_f₄ e_h (.tm₂ rfl e_h₀ hrt e_h₁)
    dcc_simp at hrt
    cases heq
    simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₁
    cases h₂ with
    | quot_bang =>
      expose_names
      cases heq
      cases e_f.hole_same e_f₃ e_h e_h_1
      simp [NormExpr.to_eta] at e_h₀
      cases e_f with
      | tm₂ =>
        expose_names
        cases e_f₃ with
        | tm₂ =>
          expose_names
          simp [GenericExpr.expr_to_eta] at hrt
          cases e_h₀ with
          | pure =>
            expose_names
            simp [GenericExpr.expr_to_eta] at h_2
            exact (h_2 .bang).elim
          | bang h =>
            simp [NormExpr.to_eta, GenericExpr.expr_to_eta, NormExpr.raw] at hrt₂
            cases e_h with
            | tm₂ =>
              expose_names
              simp [NormExpr.to_eta, GenericExpr.expr_to_eta] at heq₁
              cases a_2 with
              | pure =>
                expose_names
                cases hrt₂.elim_norm (fun ⟨_, h⟩ => by
                  cases h with
                  | congrFun h =>
                    cases h with
                    | congrFun h => cases h
                    | congrArg h => cases h
                  | congrArg h => cases h)
                simp_all
                rw [to_eta_right_inv hn] at *
                --rw [to_eta_right_inv hn_1] at *
                cases hrt₁.elim_norm (fun ⟨_, h⟩ => by
                  cases h with
                  | congrFun h =>
                    cases h with
                    | congrFun h => cases h
                    | congrArg h => cases h
                  | congrArg h => cases h)
                dcc_simp
              | coup =>
                expose_names
                cases hrt₂.elim_norm (fun ⟨_, h⟩ => by
                  cases h with
                  | congrFun h =>
                    cases h with
                    | congrFun h => cases h
                    | congrArg h => cases h
                  | congrArg h => cases h with
                    | sigl h =>
                      exact hn_hole₁_3 ⟨_, h⟩
                    | sigr h => exact hn_hole₂_2 ⟨_, h⟩)
                simp_all
                rw [to_eta_right_inv hn] at *
                --rw [to_eta_right_inv hn_1] at *
                cases hrt₁.elim_norm (fun ⟨_, h⟩ => by
                  cases h with
                  | congrFun h =>
                    cases h with
                    | congrFun h => cases h
                    | congrArg h => cases h
                  | congrArg h => cases h with
                    | sigl h => exact hn_hole₁_3 ⟨_, h⟩
                    | sigr h => exact hn_hole₂_2 ⟨_, h⟩)
                dcc_simp
              | bang h =>
                cases hrt₂.unique ⟨.trans (.single .curr') (.single .quot), by
                  simp [GenericExpr.to_eta_right_inv hn_1]
                  assumption⟩
                simp [GenericExpr.to_eta_right_inv hn_1] at hrt₂
                simp [GenericExpr.to_eta_right_inv hn_1] at hrt₁
                cases hrt₁.unique ⟨.trans (.single .curr') (.single .quot), by
                  simp [GenericExpr.to_eta_right_inv hn]
                  assumption⟩
                cases heq₁
                simp [GenericExpr.to_eta_right_inv hn]

end Canonicalize

end EtaFn

end NormExpr
