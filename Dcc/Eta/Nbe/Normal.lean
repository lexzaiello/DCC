import Dcc.Eta.Nbe.Canonicalize

namespace NormExpr

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace EtaFn

def unique (h₁ : EtaFn (τ_c := τ_c) f doms₁) (h₂ : EtaFn (τ_c := τ_c) f doms₂) : doms₁ = doms₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  grind

def hole_same (e_f₁ : EtaFn (τ_c := τ_c) f doms) (e_f₂ : EtaFn (τ_c := τ_c) f' doms) (e_h₁ : e_f₁.Holes level h₁) (e_h₂ : e_f₂.Holes level h₂) : h₁ = h₂ := by
  cases e_h₁ with
  | tm₁ =>
    cases e_h₂ with
    | tm₁ =>
      rename_i e_h₁ _ e_h₂
      simp [Hole.unique e_h₁ e_h₂]
  | tm₂ =>
    cases e_h₂ with
    | tm₂ =>
      rename_i hrt₁ e_h₁ e_h₂ _ _ _ _ _ hrt₂ e_h₃ e_h₄
      have ha := hrt₁.complete
      have hb := hrt₂.complete
      cases Hole.unique e_h₁ e_h₄
      cases Hole.unique e_h₂ (ha.symm.trans hb ▸ e_h₃)
      rfl

namespace Canonicalize

def preservation₁ {e_f₁ : EtaFn (τ_c := τ_c) f [α]} {e_f₂ : EtaFn (τ_c := τ_c) f' [α]} (h₁ : Canonicalize e_f₁ e_f₂) : Domain f' α := by
  cases e_f₂
  · assumption

def preservation₂ {e_f₁ : EtaFn (τ_c := τ_c) f [α, β]} {e_f₂ : EtaFn (τ_c := τ_c) f' [α, β]} (h₁ : Canonicalize e_f₁ e_f₂) : Domain₂ f' α β := by
  cases e_f₂
  · assumption

set_option maxHeartbeats 100000000000 in
set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
def is_norm_fn {e_f₁ : EtaFn (τ_c := τ_c) f₁ doms} {e_f₂ : EtaFn (τ_c := τ_c) f₂ doms}
  {e_f₃ : EtaFn (τ_c := τ_c) f₃ doms} (h₁ : Canonicalize e_f₁ e_f₂) (h₂ : Canonicalize e_f₂ e_f₃) : f₂ = f₃ := by
  cases h₁ with
  | id₁ =>
    match h₂ with
    | .id₁ _ _ _ _ => rfl
    | .quot₁ _ _ _ _ _ =>
      expose_names
      have hrt' : (α.id.app hole₁_1).RedAffNorm ⟨hole₁_1, hn_hole₁_1⟩ :=
        ⟨.single .id, hn_hole₁_1⟩
      have h_mem := e_h.hole_mem_tm ⟨0, e_f.arity_pos⟩
      have e_f_heq := e_f.unique x
      cases e_f_heq
      have heq := GenericExpr.RedAffNorm.unique hrt' hr_τ
      simp_all
      simp [raw, Holes.v_elems, Vector.get] at h_mem
      have hole_eq := e_f.hole_same (.tm₁ (Domain.id ⟨.refl, by assumption⟩)) e_h e_h_1
      cases hole_eq
      cases heq
      grind
    | .eval _ _ _ _ | .par _ _ _ _ _ | .sndc' _ _ _ | .fstc' _ _ _ | .sndc _ _ _ | .fstc _ _ _ =>
      expose_names
      exact a_2.absurd ⟨.single .id, by assumption⟩ (fun h => by cases h)
  | fstc =>
    cases h₂
    case fstc => rfl
    any_goals (
      focus
      try (
        expose_names
        cases e_h_1 with
        | tm₁ h =>
          cases h with
          | pure h =>
            match a_2 with
            | ⟨hr, hn⟩ =>
              match hr.cases_head with
              | .inl h => cases h
              | .inr ⟨_, h₁, h₂⟩ =>
                cases h₁ with
                | congrFun h => cases h
                | congrArg h => cases h
          | coup => exact a_2.absurd ⟨.single .fstc, by assumption⟩)
      done)
    · expose_names
      cases e_h_1 with
      | tm₁ h =>
        have hn := h.coup_points_neq
        cases h with
        | coup => exact a_3.absurd ⟨.single .fstc, by assumption⟩ (fun h => by
          cases h
          grind)
    · expose_names
      exact (h .coup).elim
    · expose_names
      exact a_3.absurd ⟨.single .fstc, hn'.congrFun.congrArg⟩
    · expose_names
      cases e_h_1 with
      | tm₁ h =>
        cases h with
        | pure h =>
          match hr_τ with
          | ⟨hr, hn⟩ =>
            match hr.cases_head with
            | .inl h =>
              cases h
              grind
            | .inr ⟨_, h₁, h₂⟩ =>
              cases h₁ with
              | congrFun h => cases h
              | congrArg h => cases h
        | coup h =>
          match hr_τ with
          | ⟨hr, hn⟩ =>
            match hr.cases_head with
            | .inl h =>
              cases h
              simp [GenericExpr.hole_mem_tm] at h
              expose_names
              have h := a_3.hole_mem_tm
              grind
            | .inr ⟨_, h₁, h₂⟩ =>
              cases h₁ with
              | congrFun h => cases h
              | congrArg h => exact (hn_hole₁_1 ⟨_, h⟩).elim
              | fstc =>
                have hn_hole₁ := hn_hole₁_1.sigl
                have heq_e' := hn_hole₁.unique_refl h₂
                cases heq_e'
                expose_names
                have h := a_4.hole_mem_tm
                grind
  | sndc =>
    cases h₂
    case sndc => rfl
    any_goals (
      focus
      try (
        expose_names
        cases e_h_1 with
        | tm₁ h =>
          cases h with
          | pure h =>
            match a_2 with
            | ⟨hr, hn⟩ =>
              match hr.cases_head with
              | .inl h => cases h
              | .inr ⟨_, h₁, h₂⟩ =>
                cases h₁ with
                | congrFun h => cases h
                | congrArg h => cases h
          | coup => exact a_2.absurd ⟨.single .sndc, by assumption⟩)
      done)
    · expose_names
      cases e_h_1 with
      | tm₁ h =>
        have hn := h.coup_points_neq
        cases h with
        | coup => exact a_3.absurd ⟨.single .sndc, by assumption⟩ (fun h => by
          cases h
          grind)
    · expose_names
      exact (h .coup).elim
    · expose_names
      exact a_3.absurd ⟨.single .sndc, hn'.congrArg⟩
    · expose_names
      cases e_h_1 with
      | tm₁ h =>
        cases h with
        | pure h =>
          match hr_τ with
          | ⟨hr, hn⟩ =>
            match hr.cases_head with
            | .inl h =>
              cases h
              grind
            | .inr ⟨_, h₁, h₂⟩ =>
              cases h₁ with
              | congrFun h => cases h
              | congrArg h => cases h
        | coup h =>
          match hr_τ with
          | ⟨hr, hn⟩ =>
            match hr.cases_head with
            | .inl h =>
              cases h
              simp [GenericExpr.hole_mem_tm] at h
              expose_names
              have h := a_3.hole_mem_tm
              grind
            | .inr ⟨_, h₁, h₂⟩ =>
              cases h₁ with
              | congrFun h => cases h
              | congrArg h => exact (hn_hole₁_1 ⟨_, h⟩).elim
              | sndc =>
                have hn_hole₁ := hn_hole₁_1.sigr
                have heq_e' := hn_hole₁.unique_refl h₂
                cases heq_e'
                expose_names
                have h := a_4.hole_mem_tm
                grind
  | fstc' =>
    cases h₂
    case fstc' => rfl
    · focus
        expose_names
        cases e_h_1 with
        | tm₁ h =>
          cases h with
          | pure h =>
            match a_2 with
            | ⟨hr, hn⟩ =>
              match hr.cases_head with
              | .inl h => cases h
              | .inr ⟨_, h₁, h₂⟩ =>
                cases h₁ with
                | congrFun h => cases h
                | congrArg h => cases h
          | bang =>
            match a_2 with
            | ⟨hr, hn⟩ =>
              expose_names
              cases a_3 with
              | pure => exact a_2.absurd ⟨.single .unmap, fun ⟨_, h⟩ => by
                cases h with
                | congrFun h => cases h
                | congrArg h => cases h⟩
              | coup h => exact a_2.absurd ⟨.trans (.single .unmap) (.single .fstc), by assumption⟩
    · expose_names
      cases e_h_1 with
      | tm₁ h =>
        have hn := h.bang_coup_points_neq
        cases h with
        | bang =>
          expose_names
          cases a_4 with
          | coup h =>
            exact a_3.absurd ⟨.trans (.single .unmap) (.single .fstc), by assumption⟩ (by
              grind)
    · expose_names
      exact (h .bang).elim
    · expose_names
      cases e_h_1 with
      | tm₁ h =>
        cases h with
        | pure h =>
          match hr_τ with
          | ⟨hr, hn⟩ =>
            match hr.cases_head with
            | .inl h =>
              cases h
              grind
            | .inr ⟨_, h₁, h₂⟩ =>
              cases h₁ with
              | congrFun h => cases h
              | congrArg h => cases h
        | bang =>
          expose_names
          cases a_2 with
          | pure =>
            match hr_τ with
            | ⟨hr, hn⟩ =>
              match hr.cases_head with
              | .inl h =>
                cases h
                simp [GenericExpr.hole_mem_tm] at h
              | .inr ⟨_, h₁, h₂⟩ =>
                cases h₁ with
                | congrFun h => cases h
                | congrArg h => exact (hn_hole₁_1 ⟨_, h⟩).elim
                | unmap =>
                  match h₂.cases_head with
                  | .inl h =>
                    cases h
                    simp [GenericExpr.hole_mem_tm] at h
                  | .inr ⟨_, h₁, h₂⟩ =>
                    cases h₁ with
                    | congrArg h => cases h
                    | congrFun h => cases h
          | coup =>
            match hr_τ with
            | ⟨hr, hn⟩ =>
              match hr.cases_head with
              | .inl h =>
                cases h
                simp [GenericExpr.hole_mem_tm] at h
                expose_names
                have h := a_4.hole_mem_tm
                grind
              | .inr ⟨_, h₁, h₂⟩ =>
                cases h₁ with
                | congrFun h => cases h
                | congrArg h => exact (hn_hole₁_1 ⟨_, h⟩).elim
                | unmap =>
                  match h₂.cases_head with
                  | .inl h =>
                    expose_names
                    cases h
                    have h := a_4.hole_mem_tm
                    grind
                  | .inr ⟨_, h₁, h₂⟩ =>
                    cases h₁ with
                    | fstc =>
                      expose_names
                      have heq := hn_hole₁_2.unique_refl (by assumption)
                      cases heq
                      have h := a_4.hole_mem_tm
                      grind
                    | congrFun h => cases h
                    | congrArg h =>
                      cases h with
                      | sigl h =>
                        expose_names
                        exact (hn_hole₁_2 ⟨_, h⟩).elim
                      | sigr h =>
                        expose_names
                        exact (hn_hole₂ ⟨_, h⟩).elim
  | sndc' =>
    cases h₂
    case sndc' => rfl
    · focus
        expose_names
        cases e_h_1 with
        | tm₁ h =>
          cases h with
          | pure h =>
            match a_2 with
            | ⟨hr, hn⟩ =>
              match hr.cases_head with
              | .inl h => cases h
              | .inr ⟨_, h₁, h₂⟩ =>
                cases h₁ with
                | congrFun h => cases h
                | congrArg h => cases h
          | bang =>
            match a_2 with
            | ⟨hr, hn⟩ =>
              expose_names
              cases a_3 with
              | pure => exact a_2.absurd ⟨.single .unmap, fun ⟨_, h⟩ => by
                cases h with
                | congrFun h => cases h
                | congrArg h => cases h⟩
              | coup h => exact a_2.absurd ⟨.trans (.single .unmap) (.single .sndc), by assumption⟩
    · expose_names
      cases e_h_1 with
      | tm₁ h =>
        have hn := h.bang_coup_points_neq
        cases h with
        | bang =>
          expose_names
          cases a_4 with
          | coup h =>
            exact a_3.absurd ⟨.trans (.single .unmap) (.single .sndc), by assumption⟩ (by
              grind)
    · expose_names
      exact (h .bang).elim
    · expose_names
      cases e_h_1 with
      | tm₁ h =>
        cases h with
        | pure h =>
          match hr_τ with
          | ⟨hr, hn⟩ =>
            match hr.cases_head with
            | .inl h =>
              cases h
              grind
            | .inr ⟨_, h₁, h₂⟩ =>
              cases h₁ with
              | congrFun h => cases h
              | congrArg h => cases h
        | bang =>
          expose_names
          cases a_2 with
          | pure =>
            match hr_τ with
            | ⟨hr, hn⟩ =>
              match hr.cases_head with
              | .inl h =>
                cases h
                simp [GenericExpr.hole_mem_tm] at h
              | .inr ⟨_, h₁, h₂⟩ =>
                cases h₁ with
                | congrFun h => cases h
                | congrArg h => exact (hn_hole₁_1 ⟨_, h⟩).elim
                | unmap =>
                  match h₂.cases_head with
                  | .inl h =>
                    cases h
                    simp [GenericExpr.hole_mem_tm] at h
                  | .inr ⟨_, h₁, h₂⟩ =>
                    cases h₁ with
                    | congrArg h => cases h
                    | congrFun h => cases h
          | coup =>
            match hr_τ with
            | ⟨hr, hn⟩ =>
              match hr.cases_head with
              | .inl h =>
                cases h
                simp [GenericExpr.hole_mem_tm] at h
                expose_names
                have h := a_4.hole_mem_tm
                grind
              | .inr ⟨_, h₁, h₂⟩ =>
                cases h₁ with
                | congrFun h => cases h
                | congrArg h => exact (hn_hole₁_1 ⟨_, h⟩).elim
                | unmap =>
                  match h₂.cases_head with
                  | .inl h =>
                    expose_names
                    cases h
                    have h := a_4.hole_mem_tm
                    grind
                  | .inr ⟨_, h₁, h₂⟩ =>
                    cases h₁ with
                    | sndc =>
                      expose_names
                      have heq := hn_hole₂.unique_refl (by assumption)
                      cases heq
                      have h := a_5.hole_mem_tm
                      grind
                    | congrFun h => cases h
                    | congrArg h =>
                      expose_names
                      cases h with
                      | sigl h => exact (hn_hole₁_2 ⟨_, h⟩).elim
                      | sigr h => exact (hn_hole₂ ⟨_, h⟩).elim

end Canonicalize

end EtaFn

end NormExpr
