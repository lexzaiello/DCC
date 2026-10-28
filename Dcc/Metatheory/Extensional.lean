import Dcc.Judge3
import Dcc.Metatheory.SubjectReduction
import Dcc.Metatheory.Progress

namespace Expr

namespace Value

def elim_eq (hv : Value e) (ht : Judge e (DCC (= A x y))) : x ≡ y := by
  cases ht with
  | app ht_f a_1 ht_x a_2 =>
    have hv_f := hv.congrFun
    have hv_x := hv.congrArg
    cases hv_f
    any_goals (
      focus
      cases ht_f
      done)
    case refl₁ =>
      cases ht_f with
      | app ht_f =>
        cases ht_f with
        | refl =>
          expose_names
          replace a_9 := a_9.push_head (.congrFun .quot)
          have heq := a_9.pi_eq
          simp [congr_reduce₁ (e := f_α'.map) (by grind), congr_reduce₁ (e := f_α'.eql) (by grind), congr_reduce₁ (e := x_2.box) (by grind), points, set_points] at heq
          cases heq.1.1; cases heq.1.2; cases heq.2
          clear heq
          clear a_9
          cases ((a_1.push_head .map).elim_normr ht_x.is_norm).unique ⟨aff_mk_point' (n := 0) (reduce_sound rfl), bang_is_norm (reduce_norm rfl)⟩
          cases hv
          any_goals (grind [point_arity])
          case refl₂ =>
            expose_names
            simp [set_points, points] at ht_x
            cases hv_x
            any_goals (grind [point_arity])
            expose_names
            have hn : IsNorm Red y_1 := fun ⟨_, h⟩ => a_12.is_norm ⟨_, h⟩
            replace a_2 := (a_2.push_head .eql).unique ⟨aff_mk_point' (n := 0) (reduce_sound rfl), eq_is_norm (reduce_norm rfl) (by assumption) (by assumption)⟩
            cases a_2
            exact ⟨⟨.refl, hn⟩, ⟨.refl, hn⟩⟩
    case refl₂ =>
      have h := Judge.inv_refl (by assumption)
      cases h
    case points₁ =>
      expose_names
      cases hv
      any_goals (grind [point_arity])
      any_goals (
        cases ht_f with
        | _ =>
          expose_names
          replace a_9 := RedNorm.push_head (by assumption) (.congrFun .quot)
          have heq := a_9.pi_eq
          simp at heq)
    case points₂ =>
      expose_names
      cases hv
      any_goals (grind [point_arity])
      case pi =>
        expose_names
        cases ht_f with
        | pi =>
          expose_names
          replace a_9 := RedNorm.push_head (by assumption) (.congrFun .quot)
          cases (a_9.push_head .quot).elim_norm (by grind)
    case points₃ =>
      expose_names
      cases hv
      any_goals (grind [point_arity])
      case curr₁ | curr'₁ | ind_bool₁ =>
        cases ht_f with
        | _ =>
          expose_names
          replace a_9 := RedNorm.push_head (by assumption) (.congrFun .quot)
          have heq := a_9.pi_eq
          simp at heq
    case points₄ =>
      expose_names
      cases hv
      any_goals (grind [point_arity])
    case eql₁ =>
      cases ht_f with
      | app ht_f =>
        cases ht_f with
        | _ =>
          cases hv
          any_goals (grind [point_arity])
    case eq'₁ =>
      cases ht_f with
      | app ht_f =>
        cases ht_f with
        | _ =>
          expose_names
          replace a_9 := RedNorm.push_head (by assumption) (.congrFun .quot)
          have heq := a_9.pi_eq
          simp [congr_reduce₃ (e := (δ.curr f_α'
              ((f_α'.comp f_α'.fstc).pi
                ((δ.sigma f_α').curr (f_α'.comp f_α'.fstc)
                  (((δ.sigma f_α').sigma (f_α'.comp f_α'.fstc)).quot (Expr.sort 0)))))) (by grind), points, set_points
              , congr_reduce₂ (e := ((f_α'.comp f_α'.fstc).pi
                ((δ.sigma f_α').curr (f_α'.comp f_α'.fstc)
                  (((δ.sigma f_α').sigma (f_α'.comp f_α'.fstc)).quot (Expr.sort 0))))) (by grind)
              , congr_reduce₂ (e := (f_α'.comp f_α'.fstc)) (by grind)] at heq
          cases heq.1.1; cases heq.1.2; cases heq.2
          clear heq
          clear a_9
          cases ((a_8.push_head .quot).elim_normr a_4.is_norm).elim_norm (Arrow.is_norm (by assumption) (Judge.is_norm (by assumption))).1
          clear a_8
          replace a_2 := (a_2.push_head .curr).pi_eq
          cases a_2
    case eq'₂ | curr₁ | curr'₁ | ind_bool₁ | ind_bot₁ | pi =>
      cases hv
      any_goals (grind [point_arity])

end Value

namespace Judge

def elim_eq (ht : Judge e (DCC (= A x y))) : x ≡ y := by
  have h := ht.progress
  match h with
  | .inl hv => exact hv.elim_eq ht
  | .inr ⟨e', hr⟩ =>
    have h_dec := hr.decreasing
    have ht' := preservation ht hr
    exact elim_eq ht'
termination_by e.size

#check elim_eq

end Judge

end Expr
