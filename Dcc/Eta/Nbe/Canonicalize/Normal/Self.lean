import Dcc.Eta.Nbe.Normal

universe u

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

def box_norm : IsNorm RedAff (GenericExpr.box x) := fun ⟨_, h⟩ => nomatch h

end GenericExpr

namespace NormExpr

namespace EtaFn

namespace Holes

/-
(tm₂
        (Domain₂.curr' (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl (GenericExpr.IsNorm.bang hn_α))
          (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl (GenericExpr.IsNorm.map hn_β))
          (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl GenericExpr.quot_norm)
          (Domain.quot
            (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl
              (GenericExpr.mk_bang_norm (GenericExpr.mk_coup_norm (GenericExpr.IsNorm.map hn_β)))))))
-/

/-open GenericExpr in
def curr'_hole (e_f : EtaFn f [⟨DCC? !(α), hn_α⟩, ⟨DCC? !<β>, hn_β⟩]) : ((hole₁ : EtaExpr) × (hole₂ : EtaExpr) × (e_f.Holes level [⟨hole₁.box, box_norm⟩, ⟨hole₂.box, box_norm⟩])) := by
  cases e_f with
  | tm₂ =>
    expose_names
    cases h_dom with
    | eql =>
      expose_names
      exact ⟨_, _, .tm₂ rfl (by sorry) (by sorry) (by sorry)⟩-/

end Holes

/-theorem hole_shape (h : EtaFn f [⟨DCC? !(α), hn_α⟩, ⟨DCC? !<β>, hn_β⟩]) (e_h : h.Holes level [⟨hole₁, hn₁⟩, ⟨hole₂, hn₂⟩]) : ∃ (hole₁' : EtaExpr) (hole₂' : EtaExpr), hole₁ = hole₁'.box ∧ hole₂ = hole₂'.box := by
  cases h with
  | tm₂ =>
    expose_names
    cases e_h with
    | tm₂ =>
      expose_names
      cases heq₁
      cases a_1 with
      | pure =>
        cases a.elim_norm (fun ⟨_, h⟩ => by
          cases h with
          | congrArg h => cases h
          | congrFun h => exact h_n_β.to_eta ⟨_, h⟩)
        expose_names
        exact (h .bang).elim
      | bang h =>
        expose_names
        have h := a.push_head .map
        expose_names
        cases h_dom with
        | eql =>
          expose_names-/
          
        --generalize h_eq : α.expr_to_eta = α'
        /-cases a_2 with
        | pure =>
          sorry-/

/-def hole_shape (h : EtaFn f [⟨DCC? !(α), hn_α⟩, ⟨DCC? !<β>, hn_β⟩]) (e_h : h.Holes level [⟨hole₁, hn₁⟩, ⟨hole₂, hn₂⟩]) : ((hole₁' : EtaExpr) × (hole₂' : EtaExpr) × (PLift (hole₁ = hole₁'.box ∧ hole₂ = hole₂'.box))) := by
  cases h with
  | tm₂ =>
    expose_names
    cases e_h with
    | tm₂ =>
      expose_names
      cases heq₁
      cases a_1 with
      | pure =>
        sorry-/

namespace Canonicalize

def self_holes (h₁ : Canonicalize (τ_c := τ_c) e_f e_f') (e_h : e_f.Holes 0 hole_tms) : e_f'.Holes 0 hole_tms := by
  cases h₁
  any_goals (
    try (
      expose_names
      cases e_h_1.unique e_h
      constructor
      · rfl
      · cases e_h with
        | tm₁ heq h =>
          cases heq
          exact h)
    done)
  case id₂ | quot_bang | quot₂ =>
    expose_names
    cases e_h_1.unique e_h
    cases e_h with
    | tm₂ heq e_h_a hrt e_h_b =>
      cases heq
      try (cases heq)
      dcc_simp at hrt
      constructor
      · rfl
      any_goals (assumption)

set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
set_option maxHeartbeats 100000000000 in
def self (h₁ : Canonicalize (τ_c := τ_c) e_f e_f') : Canonicalize e_f' e_f' := by
  let h₁₀ := h₁
  cases h₁
  case id₁ =>
    expose_names
    constructor
    any_goals (assumption)
    · constructor
      rfl
      cases e_h with
      | tm₁ heq h =>
        cases heq
        assumption
    · exact ⟨.single .id, by
      cases e_h with
      | tm₁ heq h =>
        cases heq
        exact h.is_norm⟩
  case fstc =>
    expose_names
    apply Canonicalize.fstc (a := a) (b := b)
    any_goals (assumption)
    · constructor
      rfl
      cases e_h with
      | tm₁ heq h =>
        cases heq
        dcc_simp
        dcc_simp at h
        cases h with
        | coup =>
          constructor
          any_goals (assumption)
    · dcc_simp
      exact ⟨.single (by constructor), by
        have h := e_h.points_norm ⟨0, e_f.arity_pos⟩
          ⟨1, by simp [raw, GenericExpr.point_arity, Holes.v_elems, Vector.get]⟩
        simp [GenericExpr.points, Holes.v_elems, NormExpr.raw] at h
        aesop⟩
  case sndc =>
    expose_names
    apply Canonicalize.sndc (a := a) (b := b)
    any_goals (assumption)
    · constructor
      rfl
      cases e_h with
      | tm₁ heq h =>
        cases heq
        dcc_simp
        dcc_simp at h
        cases h with
        | coup =>
          constructor
          any_goals (assumption)
    · dcc_simp
      exact ⟨.single (by constructor), by
        have h := e_h.points_norm ⟨0, e_f.arity_pos⟩
          ⟨2, by simp [raw, GenericExpr.point_arity, Holes.v_elems, Vector.get]⟩
        simp [GenericExpr.points, Holes.v_elems, NormExpr.raw] at h
        aesop⟩
  case fstc' =>
    expose_names
    apply Canonicalize.fstc' (a := a) (b := b)
    any_goals (assumption)
    · constructor
      exact .trans (.single .unmap) (.single .fstc)
    · constructor
      rfl
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | bang h =>
          cases h with
          | coup =>
            constructor
            any_goals (assumption)
            · constructor <;> assumption
  case sndc' =>
    expose_names
    apply Canonicalize.sndc' (a := a) (b := b)
    any_goals (assumption)
    · constructor
      dcc_simp
      exact .trans (.single .unmap) (.single .sndc)
    · constructor
      rfl
      cases e_h with
      | tm₁ heq h =>
        cases heq
        cases h with
        | bang h =>
          cases h with
          | coup =>
            constructor
            any_goals (assumption)
            · constructor <;> assumption
  case par =>
    expose_names
    have h := h₁₀.self_holes e_h
    apply Canonicalize.par
    any_goals (assumption)
    · cases heq
      dcc_simp
      exact ⟨.refl, by assumption⟩
  case eval =>
    expose_names
    have h := h₁₀.self_holes e_h
    apply Canonicalize.eval
    any_goals (assumption)
    · cases heq
      dcc_simp
      exact ⟨.single .evalc, by assumption⟩
  case id₂ =>
    expose_names
    have h := h₁₀.self_holes e_h
    apply Canonicalize.id₂
    any_goals (assumption)
    · dcc_simp
      exact ⟨.single (.congrFun .id), by assumption⟩
  case quot₁ =>
    expose_names
    have h := h₁₀.self_holes e_h
    apply Canonicalize.quot₁
    any_goals (assumption)
    · dcc_simp
      cases heq
      simp [GenericExpr.to_eta_right_inv hn]
      exact ⟨.single .quot, by assumption⟩
  case quot₂ =>
    expose_names
    have h := h₁₀.self_holes e_h
    apply Canonicalize.quot₂
    any_goals (assumption)
    · dcc_simp
      cases heq
      simp [GenericExpr.to_eta_right_inv hn]
      have h := e_h.app_norm
      exact ⟨.trans (.single (.congrFun .quot)) (.single .quot), by assumption⟩
  case quot_bang =>
    expose_names
    have h := h₁₀.self_holes e_h
    let h₀ := h
    cases e_f.hole_same _ e_h h
    apply Canonicalize.quot_bang
    any_goals (assumption)
    · dcc_simp
      cases heq
      simp [GenericExpr.to_eta_right_inv hn]
      cases hole₁
      case box =>
        cases hole₂
        case box =>
          exact ⟨.trans (.single .curr') (.single .quot), by assumption⟩
        any_goals (
          focus
          try (
            cases h with
            | tm₂ a b c d => cases d)
          done)
        case mkc =>
          cases h with
          | tm₂ a b c d =>
            cases a
            
            sorry
        
    /-let h_dom := (Domain₂.curr' (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl (GenericExpr.IsNorm.bang hn_α))
      (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl (GenericExpr.IsNorm.map hn_β))
      (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl GenericExpr.quot_norm)
      (Domain.quot
        (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl
          (GenericExpr.mk_bang_norm (GenericExpr.mk_coup_norm (GenericExpr.IsNorm.map hn_β))))))
    let h₀ := h
    cases e_f.hole_same _ e_h h
    expose_names
    cases h with
    | tm₂ =>
      expose_names
      simp [NormExpr.to_eta, GenericExpr.expr_to_eta] at heq₁
      cases heq₁
      cases h₀ with
      | tm₂ =>
        expose_names
        cases heq₁
        simp [NormExpr.to_eta, GenericExpr.expr_to_eta] at a_4
        cases a_4 with
        | pure =>
          expose_names
          exact (h .bang).elim
        | bang h =>
          cases a_3.unique a
          apply Canonicalize.quot_bang
            (e_f := (tm₂
             (Domain₂.curr' (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl (GenericExpr.IsNorm.bang hn_α))
               (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl (GenericExpr.IsNorm.map hn_β))
               (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl GenericExpr.quot_norm)
               (Domain.quot
                 (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl
                   (GenericExpr.mk_bang_norm (GenericExpr.mk_coup_norm (GenericExpr.IsNorm.map hn_β))))))))
            (hn := hn)
            (e' := e')
            (hr_τ := by
              expose_names
              constructor
              simp [GenericExpr.expr_to_eta] at a_3
              cases a_3 with
              | mk hrt hn =>
                match hrt.cases_head with
                | .inl h =>
                  cases h
                  cases a_5 with
                  | pure =>
                    
                    sorry)
          any_goals (assumption)-/
        
      /-cases a_1 with
      | pure =>
        expose_names
        exact (h .bang).elim
      | bang h =>
        expose_names
        cases a_2 with
        | pure =>
          
          sorry-/
        
        /-apply Canonicalize.quot_bang
        any_goals (assumption)
        · exact ⟨by sorry, by sorry⟩
        --exact h₁₀.self_holes e_h
        sorry-/
      --apply Canonicalize.quot_bang
    /-have h' : (tm₂ (Domain₂.curr'
          (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl (GenericExpr.IsNorm.bang hn_α))
          (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl (GenericExpr.IsNorm.map hn_β))
          (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl GenericExpr.quot_norm)
          (Domain.quot
            (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl
              (GenericExpr.mk_bang_norm (GenericExpr.mk_coup_norm (GenericExpr.IsNorm.map hn_β))))))).Holes 0 (by sorry) := by sorry-/
    /-apply Canonicalize.quot_bang
    any_goals (assumption)
    · cases heq
      simp [GenericExpr.to_eta_right_inv hn, GenericExpr.expr_to_eta]
      expose_names
      /-cases e_f.hole_same
        (tm₂
          (Domain₂.curr' (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl (GenericExpr.IsNorm.bang hn_α))
            (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl (GenericExpr.IsNorm.map hn_β))
            (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl GenericExpr.quot_norm)
            (Domain.quot
              (GenericExpr.RedAffNorm.mk Relation.ReflTransGen.refl
                (GenericExpr.mk_bang_norm (GenericExpr.mk_coup_norm (GenericExpr.IsNorm.map hn_β)))))))
        e_h
        h-/
      cases e_f with
      | tm₂ =>
        expose_names
        cases e_h with
        | tm₂ =>
          expose_names
          cases heq₁
          simp [NormExpr.to_eta, GenericExpr.expr_to_eta] at a_1
          cases a_1 with
          | pure =>
            expose_names
            exact (h_2 .bang).elim
          | bang h =>
            cases h with
            | tm₂ =>
              expose_names
              cases heq₁
              cases a.unique a_3
              simp [GenericExpr.expr_to_eta] at a
              cases a.unique ⟨.single .map, by sorry⟩
              sorry-/
    /-· simp [GenericExpr.expr_to_eta]
      cases heq
      simp [GenericExpr.to_eta_right_inv hn]
      have h := e_h.app_norm
      expose_names
      cases h_2 with
      | tm₂ heq =>
        cases heq
        expose_names
        dcc_simp at a_1
        dcc_simp at a_2
        cases e_h with
        | tm₂ heq =>
          cases heq
          expose_names
          simp [NormExpr.to_eta, GenericExpr.expr_to_eta] at a_5
          cases a_2.unique a_5
          cases a_2 with
          | pure =>
            expose_names
            exact (h_2 .bang).elim
          | bang h =>
            expose_names
            simp [GenericExpr.expr_to_eta] at a_3
            cases a.unique a_3
            cases a_1.hole_same a_4
            cases e_f with
            | tm₂ =>
              expose_names
              cases a_1 with
              | pure =>
                simp [GenericExpr.expr_to_eta] at a
                
                sorry
        --exact ⟨.trans (.single .curr') (.single .quot), by sorry⟩-/

end Canonicalize

end EtaFn

end NormExpr
