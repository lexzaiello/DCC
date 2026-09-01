import Dcc.Eta.Nbe.Normal

universe u

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

def IsNorm.sigt (hn : IsNorm RedAff (DCC? ⟦B⟧(x, y))) : IsNorm RedAff B := fun ⟨_, h⟩ =>
  hn ⟨_, .sig₀ h⟩

end GenericExpr

namespace NormExpr

namespace EtaFn

namespace Hole

open GenericExpr

--def cast_norm_app (e_h₁ : Hole α lv₁ hole₁) (e_h₂ : Hole β lv₂ hole₂) (h : IsNorm RedAff (DCC? (f hole₁.raw hole₂.raw))) (e_h₃ : Hole α' lv₃ hole₃)

end Hole

namespace Canonicalize

set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
set_option maxHeartbeats 100000000000 in
def is_norm_fn {e_f₁ : EtaFn (τ_c := τ_c) f₁ doms} {e_f₂ : EtaFn (τ_c := τ_c) f₂ doms}
  {e_f₃ : EtaFn (τ_c := τ_c) f₃ doms} (h₁ : Canonicalize e_f₁ e_f₂) (h₂ : Canonicalize e_f₂ e_f₃) : f₂ = f₃ := by
  let h₁₀ := h₁
  let h₂₀ := h₂
  cases h₁ with
  | id₁ =>
    match h₂ with
    | .id₁ _ _ _ _ => rfl
    | .quot₁ _ _ _ _ _ _ =>
      expose_names
      cases heq
      have hrt' : (α.id.expr_to_eta.app hole₁_1).RedAffNorm ⟨hole₁_1, hn_hole₁_1⟩ :=
        ⟨.single .id, hn_hole₁_1⟩
      have h_mem  := e_h.hole_mem_tm ⟨0, e_f.arity_pos⟩
      have h_mem' := GenericExpr.mem_imp_contains_hole h_mem
      simp [raw, Holes.v_elems, Vector.get] at h_mem'
      simp [raw, Holes.v_elems, Vector.get] at h_mem
      cases e_f.unique e_f_1
      cases GenericExpr.RedAffNorm.unique hrt' hr_τ
      cases e_f.hole_same (.tm₁ (Domain.id ⟨.refl, by assumption⟩)) e_h e_h_1
      simp_all
    | .eval _ _ _ _ _ _ | .par _ _ _ _ _ _ | .sndc' _ _ _ | .fstc' _ _ _
    | .sndc _ _ _ | .fstc _ _ _ =>
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
        | tm₁ heq h =>
          cases heq
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
      | tm₁ heq h =>
        cases heq
        have hn := h.coup_points_neq
        cases h with
        | coup => exact a_3.absurd ⟨.single .fstc, by assumption⟩ (fun h => by
          cases h
          grind)
    · expose_names
      cases e_h_1 with
      | tm₁ heq h =>
        cases heq
        simp [NormExpr.to_eta, GenericExpr.expr_to_eta] at h
        cases h with
        | pure hn =>
          exact (hn .coup).elim
        | coup => cases (a_2.push_head .fstc).elim_norm ((a_2.push_head .fstc).is_norm.congrArg.sigl)
    · expose_names
      exact a_3.absurd ⟨.single .fstc, hn'.congrFun.congrArg⟩
    · expose_names
      cases e_h_1 with
      | tm₁ heq h =>
        cases heq
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
          cases heq
          match hr_τ with
          | ⟨hr, hn⟩ =>
            match hr.cases_head with
            | .inl h =>
              cases h
              expose_names
              have h  := a_3.hole_mem_tm
              have h' := GenericExpr.mem_imp_contains_hole h
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
                have h' := GenericExpr.mem_imp_contains_hole h
                grind
  | sndc =>
    cases h₂
    case sndc => rfl
    any_goals (
      focus
      try (
        expose_names
        cases e_h_1 with
        | tm₁ heq h =>
          cases heq
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
      | tm₁ heq h =>
        cases heq
        have hn := h.coup_points_neq
        cases h with
        | coup => exact a_3.absurd ⟨.single .sndc, by assumption⟩ (fun h => by
          cases h
          grind)
    · expose_names
      cases e_h_1 with
      | tm₁ heq h =>
        cases heq
        simp [NormExpr.to_eta, GenericExpr.expr_to_eta] at h
        cases h with
        | pure hn =>
          exact (hn .coup).elim
        | coup => cases (a_2.push_head .sndc).elim_norm ((a_2.push_head .sndc).is_norm.congrArg.sigr)
    · expose_names
      exact a_3.absurd ⟨.single .sndc, hn'.congrArg⟩
    · expose_names
      cases e_h_1 with
      | tm₁ heq h =>
        cases heq
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
              expose_names
              have h := a_3.hole_mem_tm
              have h' := GenericExpr.mem_imp_contains_hole h
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
                have h' := GenericExpr.mem_imp_contains_hole h
                grind
  | fstc' =>
    cases h₂
    case fstc' => rfl
    · focus
        expose_names
        cases e_h_1 with
        | tm₁ heq h =>
          cases heq
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
      | tm₁ heq h =>
        cases heq
        have hn := h.bang_coup_points_neq
        cases h with
        | bang =>
          expose_names
          cases a_4 with
          | coup h =>
            exact a_3.absurd ⟨.trans (.single .unmap) (.single .fstc), by assumption⟩ (by
              grind)
    · expose_names
      cases e_h_1 with
      | tm₁ heq h =>
        cases heq
        simp [NormExpr.to_eta, GenericExpr.expr_to_eta] at h
        cases h with
        | pure hn =>
          exact (hn .bang).elim
        | bang h =>
          cases h with
          | coup =>
            expose_names
            cases ((a_2.push_head .unmap).push_head .fstc).elim_norm a_5.is_norm
          | pure hn =>
            exact (hn .coup).elim
    · expose_names
      cases e_h_1 with
      | tm₁ heq h =>
        cases heq
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
          cases heq
          cases a_2 with
          | pure =>
            match hr_τ with
            | ⟨hr, hn⟩ =>
              match hr.cases_head with
              | .inl h =>
                cases h
                grind
              | .inr ⟨_, h₁, h₂⟩ =>
                cases h₁ with
                | congrFun h => cases h
                | congrArg h => exact (hn_hole₁_1 ⟨_, h⟩).elim
                | unmap =>
                  match h₂.cases_head with
                  | .inl h =>
                    cases h
                    grind
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
                expose_names
                have h := GenericExpr.mem_imp_contains_hole a_4.hole_mem_tm
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
                    have h := GenericExpr.mem_imp_contains_hole a_4.hole_mem_tm
                    grind
                  | .inr ⟨_, h₁, h₂⟩ =>
                    cases h₁ with
                    | fstc =>
                      expose_names
                      have heq := hn_hole₁_2.unique_refl (by assumption)
                      cases heq
                      have h := GenericExpr.mem_imp_contains_hole a_4.hole_mem_tm
                      grind
                    | congrFun h => cases h
                    | congrArg h =>
                      cases h with
                      | sigt h =>
                        expose_names
                        exact (hn_hole₁_2 ⟨_, h⟩).elim
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
        | tm₁ heq h =>
          cases heq
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
      | tm₁ heq h =>
        cases heq
        have hn := h.bang_coup_points_neq
        cases h with
        | bang =>
          expose_names
          cases a_4 with
          | coup h =>
            exact a_3.absurd ⟨.trans (.single .unmap) (.single .sndc), by assumption⟩ (by
              grind)
    · expose_names
      cases e_h_1 with
      | tm₁ heq h =>
        cases heq
        simp [NormExpr.to_eta, GenericExpr.expr_to_eta] at h
        cases h with
        | pure hn =>
          exact (hn .bang).elim
        | bang h =>
          cases h with
          | coup =>
            expose_names
            cases ((a_2.push_head .unmap).push_head .sndc).elim_norm a_6.is_norm
          | pure hn =>
            exact (hn .coup).elim
    · expose_names
      cases e_h_1 with
      | tm₁ heq h =>
        cases heq
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
                expose_names
                grind
              | .inr ⟨_, h₁, h₂⟩ =>
                cases h₁ with
                | congrFun h => cases h
                | congrArg h => exact (hn_hole₁_1 ⟨_, h⟩).elim
                | unmap =>
                  match h₂.cases_head with
                  | .inl h =>
                    cases h
                    grind
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
                expose_names
                have h := GenericExpr.mem_imp_contains_hole a_4.hole_mem_tm
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
                    have h := GenericExpr.mem_imp_contains_hole a_4.hole_mem_tm
                    grind
                  | .inr ⟨_, h₁, h₂⟩ =>
                    cases h₁ with
                    | sndc =>
                      expose_names
                      have heq := hn_hole₂.unique_refl (by assumption)
                      cases heq
                      have h := GenericExpr.mem_imp_contains_hole a_5.hole_mem_tm
                      grind
                    | congrFun h => cases h
                    | congrArg h =>
                      expose_names
                      cases h with
                      | sigt h => exact (hn_hole₁_2 ⟨_, h⟩).elim
                      | sigl h => exact (hn_hole₁_2 ⟨_, h⟩).elim
                      | sigr h => exact (hn_hole₂ ⟨_, h⟩).elim
  | par =>
    cases h₂
    any_goals (
      focus
      try (
        expose_names
        cases heq
        cases e_f.hole_same e_f' (by assumption) (by assumption)
        cases a_1.elim_norm (by
          dcc_simp
          assumption)
        try (grind))
      done)
    any_goals (
      focus
      try (
        expose_names
        cases e_f.hole_same e_f_1 (by assumption) (by assumption)
        cases heq
        unfold NormExpr.to_eta at a_2
        simp at a_2
        simp [raw] at a_2
        dcc_simp at a_2
        cases a_2.elim_norm (by assumption))
      done)
    any_goals (
      focus
      try (
        expose_names
        cases heq
        cases e_f.hole_same e_f' (by assumption) (by assumption)
        cases heq_1
        dcc_simp at a_1
        cases a_1.elim_norm (by assumption)
        grind)
      done)
    · expose_names
      cases heq
      cases e_f.hole_same e_f_1 (by assumption) (by assumption)
      have hrt' := a_2.elim_norm (by dcc_simp; assumption)
      dcc_simp at hrt'
      cases hrt'
      rename_i left right
      cases left; cases right
    · expose_names
      cases heq
      cases e_f.hole_same e_f' (by assumption) (by assumption)
      simp [GenericExpr.to_eta_right_inv hn] at hr_τ
      cases hr_τ.elim_norm hn₂
      have h_mem' := GenericExpr.mem_imp_contains_hole (e_h.hole_mem_tm ⟨0, e_f.arity_pos⟩)
      simp [raw, Holes.v_elems, Vector.get] at h_mem'
      grind
  | eval =>
    expose_names
    cases h₂
    case eval =>
      expose_names
      cases hn₁.eq hn₁_1
      cases e_h.hole_same e_h_1
      cases heq
      simp [GenericExpr.expr_to_eta] at a_3
      cases a_3.unique ⟨.single .evalc, by
        dcc_simp
        assumption⟩
      cases e_f'.unique (by
        cases heq_1
        dcc_simp
        dcc_simp at e_f'_1
        exact e_f'_1)
      cases heq_1
      dcc_simp
    any_goals (
      focus
      try (
        expose_names
        cases hn₁.eq hn_α_1
        cases e_h.hole_same e_h_1
        cases a_2.unique ⟨.single .evalc, by
          dcc_simp
          cases heq.symm
          have heq : f' = (f'.eta_to_expr hn).expr_to_eta := by
            dcc_simp
          exact heq ▸ hn'⟩)
      done)
    case fstc | sndc =>
      expose_names
      cases hn₁.eq hn_coup
      cases e_h.hole_same e_h_1
      cases a_3.unique ⟨.single .evalc, by
        dcc_simp
        cases heq.symm
        have heq : f' = (f'.eta_to_expr hn).expr_to_eta := by
            dcc_simp
        exact heq ▸ hn'⟩
    case quot₁ =>
      expose_names
      cases hn₁.eq hn_α_1
      cases e_h.hole_same e_h_1
      cases hr_τ.unique ⟨.single .evalc, by
        dcc_simp
        cases heq.symm
        have heq : f' = (f'.eta_to_expr hn).expr_to_eta := by
            dcc_simp
        exact heq ▸ hn'⟩
      cases e_h with
      | tm₁ heq h =>
        have h_mem := GenericExpr.mem_imp_contains_hole h.sigl_hole_mem_tm
        grind
  | quot₁ =>
    cases h₂
    case quot₁ =>
      expose_names
      cases hn_α.eq hn_α_1
      cases e_h.hole_same e_h_1
      cases heq
      cases hr_τ_1.unique ⟨.single .quot, by
        dcc_simp
        assumption⟩
      cases heq_1
      dcc_simp
    · expose_names
      cases hn_α.eq hn_α_1
      cases e_h.hole_same e_h_1
      cases heq
      cases a.unique ⟨.single .quot, by
        dcc_simp
        assumption⟩
      have h_mem := e_h.hole_mem_tm ⟨0, e_f.arity_pos⟩
      simp [raw, Holes.v_elems, Vector.get] at h_mem
      dcc_simp at h_mem
      have h := GenericExpr.mem_imp_contains_hole h_mem
      grind
    case fstc | sndc =>
      expose_names
      cases hn_α.eq hn_coup
      cases e_h.hole_same e_h_1
      cases heq
      cases a_1.unique ⟨.single .quot, by
        dcc_simp
        assumption⟩
      have h_mem := e_h.hole_mem_tm ⟨0, e_f.arity_pos⟩
      simp [raw, Holes.v_elems, Vector.get] at h_mem
      dcc_simp at h_mem
      cases e_h with
      | tm₁ heq h =>
        have h_mem₁ := GenericExpr.mem_imp_contains_hole h.sigl_hole_mem_tm
        have h_mem₂ := GenericExpr.mem_imp_contains_hole h.sigr_hole_mem_tm
        dcc_simp at h_mem₁
        dcc_simp at h_mem₂
        grind
    · expose_names
      cases hn_coup.eq hn_α
      cases e_h.hole_same e_h_1
      cases heq
      cases a_1.unique ⟨.single .quot, by
        dcc_simp
        assumption⟩
      cases e_h with
      | tm₁ heq h =>
        have h_mem := h.sigl_hole_mem_tm_box
        dcc_simp at h_mem
        have h_mem := GenericExpr.mem_imp_contains_hole h_mem
        grind
    · expose_names
      cases hn_coup.eq hn_α
      cases e_h.hole_same e_h_1
      cases heq
      cases a_1.unique ⟨.single .quot, by
        dcc_simp
        assumption⟩
      cases e_h with
      | tm₁ heq h =>
        have h_mem := h.sigr_hole_mem_tm_box
        dcc_simp at h_mem
        have h_mem := GenericExpr.mem_imp_contains_hole h_mem
        grind
    · expose_names
      cases hn_α.eq hn_α_1
      cases e_h.hole_same e_h_1
      cases heq
      dcc_simp at a
      cases a.unique ⟨.single .quot, by
        dcc_simp
        assumption⟩
      cases e_h with
      | tm₁ heq h =>
        have h_mem := GenericExpr.mem_imp_contains_hole h.hole_mem_tm
        dcc_simp at h_mem
        grind
    · expose_names
      cases heq
      cases heq_1
      cases hn₁.eq hn_α_1
      dcc_simp at a_1
      cases a_1.unique ⟨.single .quot, hn_e'⟩
      cases e_h_1 with
      | tm₁ heq h =>
        have h_mem := h.sigl_hole_mem_tm
        dcc_simp at h_mem
        have h_mem := GenericExpr.mem_imp_contains_hole h_mem
        grind
  | id₂ =>
    cases h₂
    case id₂ => rfl
    · expose_names
      cases hnτ.eq hn_α
      cases e_h.hole_same e_h_1
      cases hr_τ_1.unique ⟨.single (.congrFun .id), by assumption⟩
      cases e_h with
      | tm₂ heq e_h₁ hrt e_h₂ =>
        have h_mem := e_h₁.hole_mem_tm
        grind
  | quot₂ =>
    cases h₂ <;> expose_names
    case quot₂ =>
      cases hn_quot.eq hn_quot_1
      cases heq
      cases heq_1
      cases e_h.hole_same e_h_1
      cases hr_τ_1.unique ⟨.trans (.single (.congrFun .quot)) (.single .quot), by
        dcc_simp
        assumption⟩
      cases hr_τ_1.unique ⟨.trans (.single (.congrFun .quot)) (.single .quot), by
        dcc_simp
        assumption⟩
      cases e_h with
      | tm₂ heq e_h₁ hrt e_h₂ =>
        have h_mem := GenericExpr.mem_imp_contains_hole e_h₁.hole_mem_tm
        dcc_simp at h_mem
        dcc_simp
    · cases hn_quot.eq hn_x
      cases heq
      simp [GenericExpr.expr_to_eta] at a
      simp [GenericExpr.to_eta_right_inv (e := e') hn] at a
      cases a.unique ⟨.trans (.single (.congrFun .quot)) (.single .quot), by
        dcc_simp
        assumption⟩
      cases e_h_1 with
      | tm₂ heq e_h₁ hrt e_h₂ =>
        have h_mem := e_h₁.hole_mem_tm
        dcc_simp at h_mem
        grind
  | quot_bang =>
    cases h₂
    case quot_bang =>
      expose_names
      cases hn_α.eq hn_α_1
      cases hn_β.eq hn_β_1
      dcc_simp at heq
      cases heq
      cases heq_1
      cases e_h.hole_same e_h_1
      cases e_h_1 with
      | tm₂ heq e_h₁ hrt e_h₂ =>
        cases e_h₁ with
        | coup =>
          expose_names
          cases heq
        | pure =>
          expose_names
          cases hr_τ_1.elim_norm (fun ⟨_, h⟩ => by
            cases h with
            | congrFun h =>
              cases h with
              | congrFun h => cases h
              | congrArg h => cases h
            | congrArg h => exact hn_hole₂_1 ⟨_, h⟩)
          cases e_h with
          | tm₂ heq e_h₁ hrt e_h₂ =>
            have h_mem := e_h₁.hole_mem_tm
            dcc_simp at h_mem
            have h_mem := GenericExpr.mem_imp_contains_hole h_mem
            grind
        | bang e_h₁ =>
          cases e_h₂ with
          | bang e_h₂ =>
            cases hr_τ_1.unique ⟨.trans (.single .curr') (.single (by constructor))
              , by dcc_simp; assumption⟩
            dcc_simp
          | pure =>
            expose_names
            cases hr_τ_1.elim_norm (fun ⟨_, h⟩ => by
              cases h with
              | congrFun h =>
                cases h with
                | congrFun h => cases h
                | congrArg h => cases h
              | congrArg h => cases h)
            cases e_h with
            | tm₂ heq e_h₁ hrt e_h₂ =>
              have h_mem := e_h₁.hole_mem_tm
              dcc_simp at h_mem
              have h_mem := GenericExpr.mem_imp_contains_hole h_mem
              grind
          | coup =>
            expose_names
            cases hr_τ_1.elim_norm (fun ⟨_, h⟩ => by
              cases h with
              | congrFun h =>
                cases h with
                | congrFun h => cases h
                | congrArg h => cases h
              | congrArg h =>
                cases h with
                | sigt h =>
                  cases e_h with
                  | tm₂ heq e_h₁ hrt e_h₂ =>
                    exact e_h₂.is_norm.sigl ⟨_, h⟩
                | sigl h =>
                  cases e_h with
                  | tm₂ heq e_h₁ hrt e_h₂ =>
                    exact e_h₂.is_norm.sigl ⟨_, h⟩
                | sigr h =>
                  cases e_h with
                  | tm₂ heq e_h₁ hrt e_h₂ =>
                    exact e_h₂.is_norm.sigr ⟨_, h⟩)
            cases e_h with
            | tm₂ heq e_h₁ hrt e_h₂ =>
              have h_mem := e_h₁.hole_mem_tm
              dcc_simp at h_mem
              have h_mem := GenericExpr.mem_imp_contains_hole h_mem
              grind

end Canonicalize

end EtaFn

end NormExpr
