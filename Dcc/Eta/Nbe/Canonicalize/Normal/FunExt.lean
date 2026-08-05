import Dcc.Eta.Nbe.Canonicalize.Normal.Core

open GenericExpr

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

namespace RedAff

def elim (h : RedAff x x) : False := by
  have h_dec := h.decreasing
  grind

@[grind .]
theorem elim' (h : RedAff x x) : False := by
  have h_dec := h.decreasing
  grind

def no_fst_self (h : RedAff (DCC? (Fstc(β) x)) x) : False := by
  cases h with
  | congrArg h =>
    have h_dec := h.decreasing
    exact h.no_fst_self
termination_by size x

end RedAff

namespace RedAffNorm

--def id_self

/-
For elim divergent cases in funext.

This property does not hold for quotation, however,
since (`(β, x) x) = x

-/
def no_fst_self (h : RedAffNorm (DCC? (Fstc(β) x)) ⟨x, hn_x⟩) : False := by
  match h with
  | ⟨hrt, hn⟩ =>
    match hrt.cases_head with
    | .inl h => cases h
    | .inr ⟨_, h₁, h₂⟩ =>
      cases h₁ with
      | fstc =>
        expose_names
        generalize heq : β_1.mkc w b = coup_e
        have h := heq ▸ h₂
        induction h generalizing β_1 b with
        | refl => cases heq
        | tail =>
          expose_names
          have hn := hn.sigl
          change RedAffReflTrans _ _ at h_1
          change RedAffReflTrans _ _ at h₂
          cases h_1.elim_norm (by assumption)
          cases h₂.elim_norm (by assumption)
      | congrFun h => cases h
      | congrArg h =>
        expose_names
        cases hn_x.unique h
        have h_dec := h.decreasing
        grind

def no_snd_self (h : RedAffNorm (DCC? (Sndc(β) x)) ⟨x, hn_x⟩) : False := by
  match h with
  | ⟨hrt, hn⟩ =>
    match hrt.cases_head with
    | .inl h => cases h
    | .inr ⟨_, h₁, h₂⟩ =>
      cases h₁ with
      | sndc =>
        expose_names
        generalize heq : β_1.mkc a w = coup_e
        have h := heq ▸ h₂
        induction h generalizing β_1 a with
        | refl => cases heq
        | tail =>
          expose_names
          have hn := hn.sigr
          change RedAffReflTrans _ _ at h_1
          change RedAffReflTrans _ _ at h₂
          cases h_1.elim_norm (by assumption)
          cases h₂.elim_norm (by assumption)
      | congrFun h => cases h
      | congrArg h =>
        expose_names
        cases hn_x.unique h
        have h_dec := h.decreasing
        grind

def quot_self (h : RedAffNorm (DCC? (`(β, x) y)) ⟨B, hn_b⟩) (hn₁ : IsNorm RedAff x) (hn₂ : IsNorm RedAff y) : B = x := by
  match h with
  | ⟨hrt, hn⟩ =>
    match hrt.cases_head with
    | .inl h =>
      cases h
      exact hn.elim _ .quot
    | .inr ⟨_, h₁, h₂⟩ =>
      expose_names
      cases hn_b.eq hn
      cases h₁ with
      | quot =>
        change RedAffReflTrans _ _ at h₂
        cases h₂.elim_norm hn₁
        rfl
      | congrFun h => cases h
      | congrArg h =>
        cases hn₂.unique h
        grind

end RedAffNorm

end GenericExpr

/-
Notes on function extensionality:

when both canonicalizations take similar paths (e.g., both id),
we can easily prove it

when one side disagrees, we get an equality like this:
-/

namespace NormExpr

/-def step_imp_hole {f : @GenericExpr τ_c}
  {hn : IsNorm RedAff f}
  (hr : RedAff (DCC? (f x)) B) :
  ((level : ℕ) × (α : @EtaExpr.Norm τ_c)
    × (dom    : Domain (mk f hn).to_eta α)
    × (C      : @GenericExpr (@EtaConst τ_c))
    × (hole_e : @EtaExpr τ_c)
    × (hn     :  IsNorm RedAff hole_e)
    × (hole : Hole α level ⟨hole_e, hn⟩)
    × (PLift (RedAff (DCC? (f hole_e)) C))) := by-/

open GenericExpr

namespace EtaFn

namespace Canonicalize

/-
This should be provable since we assume normal forms
and canonicalize is idempotent

Furthermore, holes cover the behavior of all
primitives.

One strategy for this proof:

- note the reduction step used in canonicalization with respect to the hole
  - e.g., fstc for ⟦β⟧(hole₁, hole₂)
- induction on x is maybe a good start

lemma:
- an argument yields a step iff there exists a hole that also steps
  - we automatically get that congruence does not count for free, since
    holes are normal forms, and so is f
-/
/-def iso {e_f : EtaFn f doms} {e_f' : EtaFn f' doms} (h : Canonicalize e_f e_f') (hr₁ : RedAffNorm (DCC? (f.raw x)) B) :
  RedAffNorm (DCC? (f'.raw x)) B := by
  induction x generalizing f f' with
  | top =>
    
    sorry-/

set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
set_option maxHeartbeats 2000000000000 in
def ext₁
  {f₁ f₂ f₃ f₄ : @NormExpr τ_c RedAff}
  {e_f₁ : EtaFn f₁ [α]} {e_f₂ : EtaFn f₂ [α]} {e_f₃ : EtaFn f₃ [α]} {e_f₄ : EtaFn f₄ [α]}
  {e_h₀ : Hole α.to_eta 0 x}
  (h₁ : Canonicalize e_f₁ e_f₂) (h₂ : Canonicalize e_f₃ e_f₄) (hrt₁ : RedAffNorm (DCC? (f₂.to_eta.raw x.raw)) B)
  (hrt₂ : RedAffNorm (DCC? (f₄.to_eta.raw x.raw)) B)
  (hn_x : IsNorm RedAff x.raw) : f₂ = f₄ := by
  cases h₁ with
  | quot₁ =>
    expose_names
    cases e_f.hole_same e_f₃ e_h (.tm₁ rfl e_h₀)
    cases e_f.hole_same e_f₄ e_h (.tm₁ rfl e_h₀)
    simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₁
    cases heq
    cases hrt₁.unique ⟨.single .quot, by
      simp [GenericExpr.to_eta_right_inv hn]
      assumption⟩
    simp [NormExpr.to_eta, NormExpr.raw] at hrt₂
    dcc_simp at hrt₂
    cases h₂ with
    | eval =>
      expose_names
      simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₂
      cases hn₁.eq hn_α
      cases heq
      cases e_h.hole_same e_h_1
      cases hrt₂.unique ⟨.single .evalc, by
        dcc_simp
        assumption⟩
      have h := e_h_1.contains_hole₁
      grind
    | par =>
      expose_names
      simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₂
      cases hn_α.eq hn_α_1
      cases heq
      cases e_h.hole_same e_h_1
      cases hrt₂.elim_norm (by
        simp [GenericExpr.to_eta_right_inv hn_1]
        assumption)
      have h := e_h₀.contains_hole
      grind
    | sndc =>
      expose_names
      simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₂
      cases hn_coup.eq hn_α
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | pure =>
          cases hrt₂.elim_norm (fun ⟨_, h⟩ => by
            cases h with
            | congrFun h => cases h
            | congrArg h => cases h)
          grind
        | coup =>
          cases hrt₂.unique ⟨.single .sndc, by
            have h := e_h₀.points_norm ⟨0, by grind⟩
            simp [GenericExpr.points] at h
            assumption⟩
          expose_names
          --cases hn_e'.eq hn_hole₁_2
          have h := a_5.contains_hole
          grind
    | fstc =>
      expose_names
      simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₂
      cases hn_coup.eq hn_α
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | pure =>
          cases hrt₂.elim_norm (fun ⟨_, h⟩ => by
            cases h with
            | congrFun h => cases h
            | congrArg h => cases h)
          grind
        | coup =>
          cases hrt₂.unique ⟨.single .fstc, by
            have h := e_h₀.points_norm ⟨0, by grind⟩
            simp [GenericExpr.points] at h
            assumption⟩
          expose_names
          cases hn_e'.eq hn_hole₁_2
          have h := a_5.contains_hole
          grind
    | quot₁ =>
      expose_names
      cases heq
      cases hrt₂.unique ⟨.single .quot, by
        simp [GenericExpr.to_eta_right_inv hn_1]
        assumption⟩
      dcc_simp
    | fstc' =>
      expose_names
      simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₂
      cases hn_coup.eq hn_α
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | pure =>
          cases hrt₂.elim_norm (fun ⟨_, h⟩ => by
            cases h with
            | congrFun h => cases h
            | congrArg h => cases h)
          grind
        | bang h =>
          cases h with
          | coup =>
            cases hrt₂.unique ⟨.trans (.single .unmap) (.single .fstc), by
              have h := e_h₀.points_norm ⟨0, by grind⟩
              simp [GenericExpr.points] at h
              exact h.sigl⟩
            expose_names
            cases hn_e'.eq hn_hole₁_2
            have h := a_5.contains_hole
            grind
          | pure =>
            expose_names
            cases hrt₂.unique ⟨.single .unmap, fun ⟨_, h⟩ => by
              cases h with
              | congrFun h => cases h
              | congrArg h => cases h⟩
            grind
    | sndc' =>
      expose_names
      simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₂
      cases hn_coup.eq hn_α
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | pure =>
          cases hrt₂.elim_norm (fun ⟨_, h⟩ => by
            cases h with
            | congrFun h => cases h
            | congrArg h => cases h)
          grind
        | bang h =>
          cases h with
          | coup =>
            cases hrt₂.unique ⟨.trans (.single .unmap) (.single .sndc), by
              have h := e_h₀.points_norm ⟨0, by grind⟩
              simp [GenericExpr.points] at h
              exact h.sigr⟩
            expose_names
            --ocases hn_e'.eq hn_hole₁_2
            have h := a_5.contains_hole
            grind
          | pure =>
            expose_names
            cases hrt₂.unique ⟨.single .unmap, fun ⟨_, h⟩ => by
              cases h with
              | congrFun h => cases h
              | congrArg h => cases h⟩
            grind
      /-cases hrt₂.unique ⟨.trans (.single .unmap) (.single .fstc), by assumption⟩
      cases e_f.hole_same e_f₃ (by assumption) (by assumption)
      have ha := e_f.hole_same e_f₃ e_h e_h_1
      have h  := e_h.contains_hole₁
      grind-/
    | id₁ =>
      expose_names
      cases hrt₂.unique ⟨.single (by constructor), by assumption⟩
      cases e_f.hole_same e_f₃ (by assumption) (by assumption)
      have ha := e_f.hole_same e_f₃ e_h e_h_1
      have h  := e_h.contains_hole₁
      grind
  | fstc' =>
    expose_names
    cases e_f.hole_same e_f₃ e_h (.tm₁ rfl e_h₀)
    cases e_f.hole_same e_f₄ e_h (.tm₁ rfl e_h₀)
    simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₁
    cases hrt₁.unique ⟨.trans (.single .unmap) (.single .fstc), by
      have h := e_h₀.points_norm ⟨0, by grind⟩
      simp [GenericExpr.points] at h
      exact h.sigl⟩
    simp [NormExpr.to_eta, NormExpr.raw] at hrt₂
    dcc_simp at hrt₂
    cases h₂ with
    | fstc' => rfl
    | sndc'  =>
      expose_names
      cases hrt₂.unique ⟨.trans (.single .unmap) (.single .sndc), by
        have h := e_h₀.points_norm ⟨0, by grind⟩
        exact h.sigr⟩
      cases e_f.hole_same e_f₃ (by assumption) (by assumption)
      cases e_f.hole_same e_f₃ e_h (.tm₁ rfl e_h₀)
      have h := e_h₀.bang_coup_points_neq
      grind
    | par =>
      expose_names
      exact (h .bang).elim
    | id₁ =>
      expose_names
      cases hrt₂.unique ⟨.single (by constructor), by assumption⟩
      try (cases e_f.hole_same e_f₃ (by assumption) (by assumption))
      try (have h := e_h₀.coup_points_neq)
      try (grind)
    | quot₁ =>
      expose_names
      cases heq
      cases hrt₂.unique ⟨.single (by constructor), by
        dcc_simp
        assumption⟩
      cases e_f.hole_same e_f₃ (by assumption) (by assumption)
      simp [GenericExpr.expr_to_eta] at hrt₂
      cases hrt₂.unique ⟨.single .quot, by
        simp [GenericExpr.to_eta_right_inv hn]
        assumption⟩
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | bang h =>
          cases h with
          | coup =>
            expose_names
            simp [GenericExpr.to_eta_right_inv hn] at a_3
            have h := a_3.contains_hole
            grind
  | sndc' =>
    expose_names
    cases e_f.hole_same e_f₃ e_h (.tm₁ rfl e_h₀)
    cases e_f.hole_same e_f₄ e_h (.tm₁ rfl e_h₀)
    simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₁
    cases hrt₁.unique ⟨.trans (.single .unmap) (.single .sndc), by
      have h := e_h₀.points_norm ⟨0, by grind⟩
      simp [GenericExpr.points] at h
      exact h.sigr⟩
    simp [NormExpr.to_eta, NormExpr.raw] at hrt₂
    dcc_simp at hrt₂
    cases h₂ with
    | sndc' => rfl
    | fstc'  =>
      expose_names
      cases hrt₂.unique ⟨.trans (.single .unmap) (.single .fstc), by
        have h := e_h₀.points_norm ⟨0, by grind⟩
        exact h.sigl⟩
      cases e_f.hole_same e_f₃ (by assumption) (by assumption)
      cases e_f.hole_same e_f₃ e_h (.tm₁ rfl e_h₀)
      have h := e_h₀.bang_coup_points_neq
      grind
    | par =>
      expose_names
      exact (h .bang).elim
    | id₁ =>
      expose_names
      cases hrt₂.unique ⟨.single (by constructor), by assumption⟩
      try (cases e_f.hole_same e_f₃ (by assumption) (by assumption))
      try (have h := e_h₀.coup_points_neq)
      try (grind)
    | quot₁ =>
      expose_names
      cases heq
      cases hrt₂.unique ⟨.single (by constructor), by
        dcc_simp
        assumption⟩
      cases e_f.hole_same e_f₃ (by assumption) (by assumption)
      simp [GenericExpr.expr_to_eta] at hrt₂
      cases hrt₂.unique ⟨.single .quot, by
        simp [GenericExpr.to_eta_right_inv hn]
        assumption⟩
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | bang h =>
          cases h with
          | coup =>
            expose_names
            simp [GenericExpr.to_eta_right_inv hn] at a_5
            have h := a_5.contains_hole
            grind
  | sndc =>
    expose_names
    cases e_f.hole_same e_f₃ e_h (.tm₁ rfl e_h₀)
    cases e_f.hole_same e_f₄ e_h (.tm₁ rfl e_h₀)
    have hn_l := hn_hole₁.sigl
    have hn_r := hn_hole₁.sigr
    simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₁
    cases hrt₁.unique ⟨.single .sndc, hn_hole₁.sigr⟩
    simp [NormExpr.to_eta, NormExpr.raw] at hrt₂
    dcc_simp at hrt₂
    cases h₂ with
    | par =>
      expose_names
      exact (h .coup).elim
    | eval =>
      expose_names
      cases heq
      simp [GenericExpr.expr_to_eta, GenericExpr.to_eta_right_inv hn] at hrt₂
      cases e_f.hole_same e_f₃ (by assumption) (by assumption)
      cases hrt₂.unique ⟨.single (by constructor), by assumption⟩
    | sndc => rfl
    | fstc | id₁ =>
      expose_names
      cases hrt₂.unique ⟨.single (by constructor), by assumption⟩
      try (cases e_f.hole_same e_f₃ (by assumption) (by assumption))
      try (have h := e_h₀.coup_points_neq)
      try (grind)
    | quot₁ =>
      expose_names
      cases heq
      cases hrt₂.unique ⟨.single (by constructor), by
        dcc_simp
        assumption⟩
      cases e_f.hole_same e_f₃ (by assumption) (by assumption)
      simp [GenericExpr.expr_to_eta] at hrt₂
      cases hrt₂.unique ⟨.single .quot, by
        simp [GenericExpr.to_eta_right_inv hn]
        assumption⟩
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | coup =>
          expose_names
          simp [GenericExpr.to_eta_right_inv hn] at a_5
          have h := a_5.contains_hole
          grind
  | fstc =>
    expose_names
    cases e_f.hole_same e_f₃ e_h (.tm₁ rfl e_h₀)
    cases e_f.hole_same e_f₄ e_h (.tm₁ rfl e_h₀)
    have hn_l := hn_hole₁.sigl
    have hn_r := hn_hole₁.sigr
    simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₁
    cases hrt₁.unique ⟨.single .fstc, hn_hole₁.sigl⟩
    simp [NormExpr.to_eta, NormExpr.raw] at hrt₂
    dcc_simp at hrt₂
    cases h₂ with
    | par =>
      expose_names
      exact (h .coup).elim
    | eval =>
      expose_names
      cases heq
      simp [GenericExpr.expr_to_eta, GenericExpr.to_eta_right_inv hn] at hrt₂
      cases e_f.hole_same e_f₃ (by assumption) (by assumption)
      cases hrt₂.unique ⟨.single (by constructor), by assumption⟩
    | fstc => rfl
    | sndc | id₁ =>
      expose_names
      cases hrt₂.unique ⟨.single (by constructor), by assumption⟩
      try (cases e_f.hole_same e_f₃ (by assumption) (by assumption))
      try (have h := e_h₀.coup_points_neq)
      try (grind)
    | quot₁ =>
      expose_names
      cases heq
      cases hrt₂.unique ⟨.single (by constructor), by
        dcc_simp
        assumption⟩
      cases e_f.hole_same e_f₃ (by assumption) (by assumption)
      simp [GenericExpr.expr_to_eta] at hrt₂
      cases hrt₂.unique ⟨.single .quot, by
        simp [GenericExpr.to_eta_right_inv hn]
        assumption⟩
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | coup =>
          expose_names
          simp [GenericExpr.to_eta_right_inv hn] at a_3
          have h := a_3.contains_hole
          grind
  | id₁ =>
    expose_names
    cases h₂ with
    | fstc' =>
      expose_names
      cases e_f.hole_same e_f_1 e_h e_h_1
      cases hn_coup.eq hn_α
      cases e_f.hole_same e_f_1 e_h (.tm₁ rfl e_h₀)
      cases hrt₁.unique ⟨.single .id, hn_x⟩
      simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₂
      cases hrt₂.unique ⟨.trans (.single .unmap) (.single .fstc), by
        cases e_h_1 with
        | tm₁ heq h =>
          cases heq
          cases h with
          | bang h =>
            cases h with
            | coup =>
              expose_names
              exact hn_hole₁_2⟩
    | sndc' =>
      expose_names
      cases e_f.hole_same e_f_1 e_h e_h_1
      cases hn_coup.eq hn_α
      cases e_f.hole_same e_f_1 e_h (.tm₁ rfl e_h₀)
      cases hrt₁.unique ⟨.single .id, hn_x⟩
      simp [NormExpr.to_eta, NormExpr.raw, GenericExpr.expr_to_eta] at hrt₂
      cases hrt₂.unique ⟨.trans (.single .unmap) (.single .sndc), by
        cases e_h_1 with
        | tm₁ heq h =>
          cases heq
          cases h with
          | bang h =>
            cases h with
            | coup =>
              expose_names
              assumption⟩
    | par =>
      expose_names
      cases e_f.hole_same e_f₃ e_h e_h_1
      cases hn_α.eq hn_α_1
      cases e_f.hole_same e_f₃ e_h (.tm₁ rfl e_h₀)
      cases hrt₁.unique ⟨.single .id, hn_x⟩
      cases heq
      cases e_f.hole_same e_f' e_h (.tm₁ rfl e_h₀)
      simp [NormExpr.to_eta, NormExpr.raw] at hrt₂
      simp [GenericExpr.to_eta_right_inv hn] at hrt₂
      cases hrt₂.elim_norm (by assumption)
    | eval =>
      expose_names
      cases e_f.hole_same e_f_1 e_h e_h_1
      have hn_eq : hn_α = hn₁ := by grind
      cases hn₁.eq hn_α
      cases e_f.hole_same e_f_1 e_h (.tm₁ rfl e_h₀)
      cases hrt₁.unique ⟨.single .id, hn_x⟩
      cases heq
      cases hrt₂.unique ⟨.single .evalc, by
        simp [GenericExpr.to_eta_right_inv hn]
        exact hn'⟩
    | id₁ =>
      expose_names
      have ha := e_f.hole_same e_f₃ e_h e_h_1
      simp_all
    | sndc | fstc =>
      expose_names
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | coup =>
          expose_names
          cases hrt₁.unique ⟨.single .id, x.is_norm⟩
          try (exact hrt₂.no_fst_self.elim)
          try (exact hrt₂.no_snd_self.elim)
        | pure =>
          expose_names
          simp [expr_to_eta] at h
          exact (h .coup).elim
    | quot₁ =>
      expose_names
      cases hrt₁.unique ⟨.single .id, x.is_norm⟩
      cases heq
      have h := to_eta_no_hole (e := e')
      simp [NormExpr.to_eta] at hrt₂
      dcc_simp at hrt₂
      have hrt' := hrt₂.unique ⟨.single .quot, by
        dcc_simp
        assumption⟩
      dcc_simp at hrt'
      cases hrt'
      have h_eq_x₀ := hrt₂.quot_self (by
        simp [GenericExpr.to_eta_right_inv hn]
        assumption) (by assumption)
      have h_mem := e_h₀.contains_hole
      simp [raw] at h_mem
      exact (hn h_mem).elim

set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
def ext₁
  {f₁ f₂ f₃ f₄ : @NormExpr τ_c RedAff}
  {e_f₁ : EtaFn f₁ [α]} {e_f₂ : EtaFn f₂ [α]} {e_f₃ : EtaFn f₃ [α]} {e_f₄ : EtaFn f₄ [α]}
  {e_h₀ : Hole α.to_eta level x}
  {e_h₂ : e_f₃.Holes level hole_tms₂}
  (h₁ : Canonicalize e_f₁ e_f₂) (h₂ : Canonicalize e_f₃ e_f₄) (hrt₁ : RedAffNorm (DCC? (f₂.to_eta.raw x.raw)) B)
  (hrt₂ : RedAffNorm (DCC? (f₄.to_eta.raw x.raw)) B)
  (hn_x : IsNorm RedAff x.raw) : f₂ = f₄ := by
  cases h₁ with
  | id₁ =>
    cases h₂ with
    | id₁ =>
      expose_names
      have ha := e_f.hole_same e_f₃ e_h e_h_1
      simp_all
    | sndc | fstc =>
      expose_names
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | coup =>
          expose_names
          cases hrt₁.unique ⟨.single .id, x.is_norm⟩
          try (exact hrt₂.no_fst_self.elim)
          try (exact hrt₂.no_snd_self.elim)
    | quot₁ =>
      expose_names
      cases hrt₁.unique ⟨.single .id, x.is_norm⟩
      cases heq
      have h := to_eta_no_hole (e := e')
      dcc_simp at hrt₂
      have h_eq_x₀ := hrt₂.quot_self (hn_e'.from_eta hn) (by assumption)
      have h_e'_eq : (e'.eta_to_expr hn) = x.raw := h_eq_x₀.symm
      simp [h_e'_eq] at hrt₂
      have heq_x := hrt₂.unique ⟨.single .quot, by assumption⟩
      rw [heq_x] at *
      cases e_f.hole_same e_f₃ e_h e_h_1
      have h := h_e'_eq.symm ▸ e_h₀.contains_hole
      have h := h_e'_eq ▸ h
      have heq' : x.1.expr_to_eta = e' := by
        rw [h_eq_x₀]
        dcc_simp
      have heq'' : x.1 = e'.eta_to_expr (by assumption) := by grind
      
      expose_names
      have h_mem : x.1.contains_hole := by grind
      have h_mem' := h_eq_x₀ ▸ h_mem
      
      have hn : ¬ contains_hole x.raw := by
        intro h
        rw [h_eq_x₀] at heq'
        have h := to_eta_no_hole (e := e')
        rename_i h_mem
        simp [raw] at h_mem
        rw [h_eq_x₀] at h_mem
        have h := h_eq_x₀ ▸ h_mem
        /-rw [h_eq_x₀] at heq'
        have h := to_eta_no_hole (e := e')
        simp_all
        have h := heq'.symm ▸ hn-/
        sorry
      cases e_h with
      | tm₁ heq h =>
        cases h with
        | pure =>
          expose_names
          cases heq
          /-cases hrt₁.unique ⟨.single .id, x.is_norm⟩
          cases heq
          have h := to_eta_no_hole (e := e')
          dcc_simp at hrt₂
          have h_eq_x₀ := hrt₂.quot_self (hn_e'.from_eta hn) (by assumption)
          have h_e'_eq : (e'.eta_to_expr hn) = x.raw := h_eq_x₀.symm
          simp [h_e'_eq] at hrt₂
          have heq_x := hrt₂.unique ⟨.single .quot, by assumption⟩
          rw [heq_x] at *
          cases e_h_1 with
          | tm₁ heq h =>
            cases heq
            generalize heq_α  : α.expr_to_eta = α'
            generalize heq_α' : (mk α hn_α_1).to_eta = α''
            cases heq_α' ▸ h with
            | pure =>
              sorry-/

/-
Since both EtaFn have same domain, we should get exactly the same canonical form,
though it will be annoying.
-/
set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
def ext {e_f₁ : EtaFn f₁ doms} {e_f₂ : EtaFn f₂ doms} {e_f₃ : EtaFn f₃ doms} {e_f₄ : EtaFn f₄ doms}
  {x : @NormExpr τ_c RedAff}
  (h₁ : Canonicalize e_f₁ e_f₂) (h₂ : Canonicalize e_f₃ e_f₄) (hrt₁ : RedAffNorm (DCC? (f₂.raw x.raw)) B)
  (hrt₂ : RedAffNorm (DCC? (f₄.raw x.raw)) B)
  (hn_x : IsNorm RedAff x.raw) : f₂ = f₄ := by
  cases h₁ with
  | id₁ =>
    cases h₂ with
    | id₁ =>
      expose_names
      have ha := e_f.hole_same e_f₃ e_h e_h_1
      simp_all
    | sndc | fstc =>
      expose_names
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | coup =>
          expose_names
          cases hrt₁.unique ⟨.single .id, x.is_norm⟩
          try (exact hrt₂.no_fst_self.elim)
          try (exact hrt₂.no_snd_self.elim)
    | quot₁ =>
      expose_names
      cases hrt₁.unique ⟨.single .id, x.is_norm⟩
      cases heq
      have h := to_eta_no_hole (e := e')
      dcc_simp at hrt₂
      have h_eq_x₀ := hrt₂.quot_self (hn_e'.from_eta hn) (by assumption)
      have h_e'_eq : (e'.eta_to_expr hn) = x.raw := h_eq_x₀.symm
      simp [h_e'_eq] at hrt₂
      have heq_x := hrt₂.unique ⟨.single .quot, by assumption⟩
      rw [heq_x] at *
      cases e_f.hole_same e_f₃ e_h e_h_1
      cases e_h with
      | tm₁ heq h =>
        cases h with
        | pure =>
          expose_names
          cases heq
          /-cases hrt₁.unique ⟨.single .id, x.is_norm⟩
          cases heq
          have h := to_eta_no_hole (e := e')
          dcc_simp at hrt₂
          have h_eq_x₀ := hrt₂.quot_self (hn_e'.from_eta hn) (by assumption)
          have h_e'_eq : (e'.eta_to_expr hn) = x.raw := h_eq_x₀.symm
          simp [h_e'_eq] at hrt₂
          have heq_x := hrt₂.unique ⟨.single .quot, by assumption⟩
          rw [heq_x] at *
          cases e_h_1 with
          | tm₁ heq h =>
            cases heq
            generalize heq_α  : α.expr_to_eta = α'
            generalize heq_α' : (mk α hn_α_1).to_eta = α''
            cases heq_α' ▸ h with
            | pure =>
              sorry-/

end Canonicalize

end EtaFn

end NormExpr

/-
Other ways to show FunExt for Canonicalize

- look at f'. these will be canonical morphisms in the category

Note that iso is a slightly different theorem.
FunExt should theoretically be easier, since we work with the normal forms,
which inhabit this set of morphisms
-/
