import Dcc.Red.Rel
import Dcc.Red.Run

/-
τ : Type u
inst : DecidableEq τ
n : ℕ
p' C a³ a² a¹ a : Expr
h₂ : (a³.unify a² a¹ a).Red C
A : Expr
heq : (a³.unify a² A A).point_arity = 4
hn : 2 < 4
h₁ : ((a³.unify a² A A).points.get ⟨2, hn⟩).Red p'
h :
  ∀ {C : Expr},
    ((a³.unify a² A A).points.get ⟨2, hn⟩).Red C → ∃ D, instRedRel.ReflTrans p' D ∧ instRedRel.ReflTrans C D
⊢ ∃ D,
    instRedRel.ReflTrans ((a³.unify a² A A).set_points ((a³.unify a² A A).points.set 2 p' hn)) D ∧
      instRedRel.ReflTrans (a³.unif_refl a² A) D
-/

namespace Expr

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
theorem Red.conf_point (h₁ : Red ((points e).get ⟨n, hn⟩) p') (h₂ : Red e C)
  (h : ∀ {C : Expr}, (e.points.get ⟨n, hn⟩).Red C → ∃ D, instRedRel.ReflTrans p' D ∧ instRedRel.ReflTrans C D) :
  ∃ D, Red.instRedRel.ReflTrans (e.set_points ((points e).set n p')) D ∧ Red.instRedRel.ReflTrans C D := by
  match cases_point_arity e with
  | .inl heq =>
    cases e
    any_goals (grind only [points, point_arity])
  | .inr (.inl heq) =>
    cases e
    any_goals (grind only [points, point_arity])
    any_goals (
      match n with
      | 0 =>
        match h₂ with
        | .point 0 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          exact ⟨_, aff_mk_point' h₁ (n := 0), aff_mk_point' h₂ (n := 0)⟩)
  | .inr (.inr (.inl heq)) =>
    cases e
    any_goals (grind only [points, point_arity])
    any_goals (
      match n with
      | 0 =>
        match h₂ with
        | .point 0 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, aff_mk_point' h₁ (n := 0) (hn := ?_) (heq := ?_), aff_mk_point' h₂ (n := 0) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 1 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 1 (by simp [point_arity]) hr), .single (.point 0 (by simp [point_arity]) h₁)⟩
      | 1 =>
        match h₂ with
        | .point 1 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, aff_mk_point' h₁ (n := 1) (hn := ?_) (heq := ?_), aff_mk_point' h₂ (n := 1) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 0 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 0 (by simp [point_arity]) hr), .single (.point 1 (by simp [point_arity]) h₁)⟩)
  | .inr (.inr (.inr (.inl heq))) =>
    cases e
    any_goals (grind only [points, point_arity])
    any_goals (
      match n with
      | 0 =>
        match h₂ with
        | .point 0 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, aff_mk_point' h₁ (n := 0) (hn := ?_) (heq := ?_), aff_mk_point' h₂ (n := 0) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 1 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 1 (by simp [point_arity]) hr), .single (.point 0 (by simp [point_arity]) h₁)⟩
        | .point 2 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 2 (by simp [point_arity]) hr), .single (.point 0 (by simp [point_arity]) h₁)⟩
      | 1 =>
        match h₂ with
        | .point 1 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, aff_mk_point' h₁ (n := 1) (hn := ?_) (heq := ?_), aff_mk_point' h₂ (n := 1) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 0 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 0 (by simp [point_arity]) hr), .single (.point 1 (by simp [point_arity]) h₁)⟩
        | .point 2 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 2 (by simp [point_arity]) hr), .single (.point 1 (by simp [point_arity]) h₁)⟩
      | 2 =>
        match h₂ with
        | .point 2 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, aff_mk_point' h₁ (n := 2) (hn := ?_) (heq := ?_), aff_mk_point' h₂ (n := 2) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 0 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 0 (by simp [point_arity]) hr), .single (.point 2 (by simp [point_arity]) h₁)⟩
        | .point 1 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 1 (by simp [point_arity]) hr), .single (.point 2 (by simp [point_arity]) h₁)⟩)
  | .inr (.inr (.inr (.inr heq))) =>
    cases e
    any_goals (grind only [points, point_arity])

#check Red.conf_point

set_option maxHeartbeats 10000000000 in
open Congruent' in
open Congruent in @[dcc_reduce, aesop safe apply (rule_sets := [DccReduce])]
theorem Red.conf (h₁ : Red A B) (h₂ : Red A C) : ∃ D, Red.instRedRel.ReflTrans B D ∧ Red.instRedRel.ReflTrans C D := by
  induction h₁ generalizing C
  -- Inner congruences:
  case point h => exact conf_point (by assumption) h₂ h
  /-case unif_refl =>
    exact conf_unif_refl h₂-/
  /-case unif_bot_sort =>
    exact conf_unif_bot_sort h₂
  case unif_bot_prop =>
    exact conf_unif_bot_prop h₂-/
  case ind_bool_true =>
    match h₂ with
    | .ind_bool_true => exact ⟨_, .refl, .refl⟩
    | .congrFun (.congrFun (.point 0 hn h)) =>
      exact ⟨_, .refl, .single (by constructor)⟩
    | .congrFun (.congrFun (.point 1 hn h)) =>
      exact ⟨_, .single (.congrFun (.congrFun h)), .single (by constructor)⟩
    | .congrFun (.congrFun (.point 2 hn h)) =>
      exact ⟨_, .refl, .single (by constructor)⟩
    | .congrFun (.congrArg h) =>
      exact ⟨_, .single (.congrFun (.congrArg h)), .single (by constructor)⟩
    | .congrArg h => nomatch h
  case ind_bool_false =>
    match h₂ with
    | .ind_bool_false => exact ⟨_, .refl, .refl⟩
    | .congrFun (.congrFun (.point 0 hn h)) =>
      exact ⟨_, .refl, .single (by constructor)⟩
    | .congrFun (.congrFun (.point 1 hn h)) =>
      exact ⟨_, .refl, .single (by constructor)⟩
    | .congrFun (.congrFun (.point 2 hn h)) =>
      exact ⟨_, .single (.congrFun (.congrFun h)), .single (by constructor)⟩
    | .congrFun (.congrArg h) =>
      exact ⟨_, .single (.congrFun (.congrArg h)), .single (by constructor)⟩
    | .congrArg h => nomatch h
  case sigma =>
    match h₂ with
    | .sigma => exact ⟨_, .refl, .refl⟩
    | .congrFun (.point 0 hn h) => exact ⟨_, .single (.point 0 (by point_arity) (.congrFun h)), .single .sigma⟩
    | .congrFun (.point 1 hn h) => exact ⟨_, .single (.point 1 (by point_arity) (.congrFun h)), .single .sigma⟩
    | .congrArg (.point 0 hn h) => exact ⟨_, .trans (.single (.point 0 (by point_arity) (.congrArg h))) (.single (.point 1 (by point_arity) (.congrArg h))), .single .sigma⟩
  case swap =>
    match h₂ with
    | .swap => exact ⟨_, .refl, .refl⟩
    | .congrFun (.point 1 hn h) => exact ⟨_, .single (.point 0 (by grind) (.point 0 (by simp [point_arity, points, Vector.get]) h)), .single .swap⟩
    | .congrFun (.point 0 hn h) => exact ⟨_, .single (.point 0 (by grind) (.point 1 (by simp [point_arity, points, Vector.get]) h)), .single .swap⟩
    | .congrArg h =>
      match h with
      | .point 0 hn h => exact ⟨_, .refl, .single .swap⟩
      | .point 1 hn h => exact ⟨_, .single (.point 2 (by grind) h), .single .swap⟩
      | .point 2 hn h => exact ⟨_, .single (.point 1 (by grind) h), .single .swap⟩
  -- Main reductions:
  case eql =>
    cases h₂ with
    | congrFun hr =>
      cases hr with
      | point =>
        expose_names
        simp [point_arity] at h
      | congrFun hr =>
        have ⟨_, h⟩ := hr.elim_point₁
        dcc_simp at h
        cases h.left
        exact ⟨_, .single (.point 0 (by grind) (.congrFun h.right)), .single (by constructor)⟩
      | congrArg hr =>
        match hr with
        | .point 0 hn h => exact ⟨_, .single (.point 0 (by grind) (.congrArg h)), .single (by constructor)⟩
    | congrArg hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .trans (.single (.point 1 (by grind) hr)) (.single (.point 2 (by grind) hr)), .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case fmap | map =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .single ((Red.congrFun h.right).mk_point (n := ⟨0, by grind⟩)), .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .single ((Red.congrArg h.right).mk_point (n := ⟨0, by grind⟩)), .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case unbox =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .refl, .single (by constructor)⟩
    | congrArg hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single hr, .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case pair =>
    cases h₂ with
    | congrFun hr =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (hr.congrFun.mk_point (n := ⟨0, by grind⟩)), .single (by constructor)⟩
      | .point 1 hn hr =>
        exact ⟨_, .trans (.single (hr.congrFun.mk_point (n := ⟨1, by grind⟩))) (.single (hr.congrFun.congrArg.mk_point (n := ⟨2, by grind⟩))), .single (by constructor)⟩
      | .point 2 hn hr =>
        exact ⟨_, .single (hr.congrFun.congrFun.mk_point (n := ⟨2, by grind⟩)), .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .trans (.trans (.trans (.single (h.right.congrArg.mk_point (n := ⟨0, by grind⟩)))
        (.single (h.right.congrArg.mk_point (n := ⟨1, by grind⟩))))
        (.single (h.right.congrArg.congrArg.mk_point (n := ⟨2, by grind⟩))))
        (.single (h.right.congrArg.congrFun.mk_point (n := ⟨2, by grind⟩))), .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case evalc =>
    cases h₂ with
    | congrFun hr =>
      match hr with
      | .point 2 hn hr =>
        exact ⟨_, .single hr.congrFun.congrFun, .single .evalc⟩
      | .point 0 hn hr | .point 1 hn hr => exact ⟨_, .refl, .single .evalc⟩
    | congrArg hr =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .refl, .single .evalc⟩
      | .point 1 hn hr =>
        exact ⟨_, .single hr.congrArg.congrFun, .single .evalc⟩
      | .point 2 hn hr => exact ⟨_, .single hr.congrArg, .single .evalc⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case quot =>
    cases h₂ with
    | congrFun h =>
      match h with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single hr, .single (by constructor)⟩
    | congrArg h => exact ⟨_, .refl, .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case id =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      cases h.left
      exact ⟨_, .refl, .single (by constructor)⟩
    | congrArg hr => exact ⟨_, .single hr, .single (by constructor)⟩
    | point =>
        expose_names
        simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case fstc | sndc =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      cases h.left
      exact ⟨_, .refl, .single (by constructor)⟩
    | congrArg hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 2 hn hr | .point 1 hn hr => first | exact ⟨_, .single hr, .single (by constructor)⟩ | exact ⟨_, .refl, .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case eq_mk =>
    match h₂ with
    | .congrFun (.congrFun (.congrFun (.point 0 hn h))) =>
      exact ⟨_, .single (.point 0 (by grind) (.congrFun h)), .single (by constructor)⟩
    | .congrFun (.congrFun (.congrArg h)) =>
      exact ⟨_, .single (.point 0 (by grind) (.congrArg h)), .single (by constructor)⟩
    | .congrFun (.congrArg h) =>
      exact ⟨_, .single (.point 1 (by grind) h), .single (by constructor)⟩
    | .congrArg h =>
      exact ⟨_, .single (.point 2 (by grind) h), .single (by constructor)⟩
    | .eq_mk => exact ⟨_, .refl, .refl⟩
  case comp =>
    cases h₂ with
    | congrFun hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single hr.congrFun, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single hr.congrFun.congrArg, .single (by constructor)⟩
    | congrArg hr =>
      exact ⟨_, .single hr.congrArg.congrArg, .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case curr =>
    cases h₂ with
    | congrFun hr =>
      cases hr with
      | congrFun hr =>
        match hr with
        | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
        | .point 1 hn hr => exact ⟨_, .single (Red.point 0 (by grind) hr).congrArg, .single (by constructor)⟩
        | .point 2 hn hr => exact ⟨_, .single hr.congrFun, .single (by constructor)⟩
      | point =>
        expose_names
        simp [point_arity] at h
      | congrArg hr =>
        exact ⟨_, .single (.congrArg (Red.point 1 (by grind) hr)), .single (by constructor)⟩
    | congrArg hr =>
      exact ⟨_, .single (.congrArg (Red.point 2 (by grind) hr)), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case curr' =>
    cases h₂ with
    | congrFun hr =>
      cases hr with
      | point =>
        expose_names
        simp [point_arity] at h
      | congrFun hr =>
        match hr with
        | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
        | .point 1 hn hr => exact ⟨_, .single (.congrArg (.point 0 (by grind) (.point 0 (by simp [points, Vector.get, point_arity]) hr))), .single (by constructor)⟩
        | .point 2 hn hr => exact ⟨_, .single hr.congrFun, .single (by constructor)⟩
      | congrArg hr =>
        have ⟨_, h⟩ := hr.elim_point₁
        cases h.left
        exact ⟨_, .single (.congrArg (.point 0 (by grind) (.point 1 (by simp [points, Vector.get, point_arity]) h.right))), .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      cases h.left
      exact ⟨_, .single (.congrArg (.point 0 (by grind) (.point 2 (by simp [points, Vector.get, point_arity]) h.right))), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case congrArg hr ih =>
    rename_i x x' f
    cases h₂
    <;> (try (
      have ⟨p', heq, hrp⟩ := hr.elim_point₁
      dcc_simp at heq; dcc_simp at hrp
      cases heq))
    case eq_mk =>
      exact ⟨_, .single (by constructor), .single (.point 2 (by grind) (by assumption))⟩
    case sigma =>
      exact ⟨_, .single .sigma, .trans (.single (.point 0 (by point_arity) (.congrArg hrp))) (.single (.point 1 (by point_arity) (.congrArg hrp)))⟩
    case ind_bool_true | ind_bool_false =>
      nomatch hr
    case point h => grind only [point_arity]
    /-case unif_bot_sort => nomatch hr
    case unif_bot_prop => nomatch hr-/
    case swap =>
      match hr with
      | .point 0 hn h =>
        exact ⟨_, .single (by constructor), .refl⟩
      | .point 1 hn h =>
        exact ⟨_, .single (by constructor), .single (.point 2 (by grind) h)⟩
      | .point 2 hn h =>
        exact ⟨_, .single (by constructor), .single (.point 1 (by grind) h)⟩
    case eql =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .trans (.single (.point 1 (by grind) hr)) (.single (.point 2 (by grind) hr))⟩
    case fmap | map =>
      exact ⟨_, .single (by constructor), aff_mk_point'' 0 hrp.congrArg⟩
    case unbox =>
      exact ⟨_, .single (by constructor), .single hrp⟩
    case pair =>
      exact ⟨_, .single (by constructor), .trans (.trans (aff_mk_point'' 0 hrp.congrArg) (aff_mk_point'' 1 hrp.congrArg))
        ((aff_mk_point'' 2 hrp.congrArg.congrArg).trans (aff_mk_point'' 2 hrp.congrArg.congrFun))⟩
    case evalc =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 1 hn hr => exact ⟨_, .single (by constructor), .single hr.congrArg.congrFun⟩
      | .point 2 hn hr => exact ⟨_, .single (by constructor), .single hr.congrArg⟩
    case quot => exact ⟨_, .single (by constructor), .refl⟩
    case id => exact ⟨_, .single (by constructor), .single (by assumption)⟩
    case sndc | fstc =>
      match hr with
      | .point 0 hn hr | .point 1 hn hr | .point 2 hn hr =>
        first
        | exact ⟨_, .single (by constructor), .refl⟩
        | exact ⟨_, .single (by constructor), .single (by assumption)⟩
    case comp =>
      exact ⟨_, .single (by constructor), .single hr.congrArg.congrArg⟩
    case curr => exact ⟨_, .single (by constructor), .single (.congrArg (.point 2 (by grind) (by assumption)))⟩
    case curr' hr => exact ⟨_, .single (by constructor), .single (.congrArg (.point 0 (by grind) (.point 2 (by simp [points, Vector.get, point_arity]) (by assumption))))⟩
    case congrFun hr => exact ⟨_, .single (.congrFun hr), .single (.congrArg (by assumption))⟩
    case congrArg hr =>
      have ⟨_, h₁, h₂⟩ := ih hr
      exact ⟨_, congrArg' h₁, congrArg' h₂⟩
  case congrFun hr ih =>
    rename_i f f' x
    cases h₂
    <;> (try (
      have ⟨p', heq, hrp⟩ := hr.elim_point₁
      dcc_simp at heq; dcc_simp at hrp
      cases heq))
    case sigma =>
      match hr with
      | (.point 0 hn h) => exact ⟨_, .single .sigma, .single (.point 0 (by point_arity) (.congrFun h))⟩
      | (.point 1 hn h) => exact ⟨_, .single .sigma, .single (.point 1 (by point_arity) (.congrFun h))⟩
    case eq_mk =>
      match hr with
      | (.congrFun (.congrFun (.point 0 hn h))) =>
        exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (.congrFun h))⟩
      | (.congrFun (.congrArg h)) =>
        exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (.congrArg h))⟩
      | (.congrArg h) =>
        exact ⟨_, .single (by constructor), .single (.point 1 (by grind) h)⟩
    case point => grind only [point_arity]
    case ind_bool_true =>
      match hr with
      | .congrArg hr =>
        exact ⟨_, .single .ind_bool_true, .single (.congrFun (.congrArg hr))⟩
      | .congrFun (.point 0 hn hr) =>
        exact ⟨_, .single .ind_bool_true, .refl⟩
      | .congrFun (.point 1 hn hr) =>
        exact ⟨_, .single .ind_bool_true, .single (.congrFun (.congrFun hr))⟩
      | .congrFun (.point 2 hn hr) =>
        exact ⟨_, .single .ind_bool_true, .refl⟩
    case ind_bool_false =>
      match hr with
      | .congrArg hr =>
        exact ⟨_, .single .ind_bool_false, .single (.congrFun (.congrArg hr))⟩
      | .congrFun (.point 0 hn hr) =>
        exact ⟨_, .single .ind_bool_false, .refl⟩
      | .congrFun (.point 2 hn hr) =>
        exact ⟨_, .single .ind_bool_false, .single (.congrFun (.congrFun hr))⟩
      | .congrFun (.point 1 hn hr) =>
        exact ⟨_, .single .ind_bool_false, .refl⟩
    case swap =>
      match hr with
      | .point 0 hn h =>
        exact ⟨_, .single .swap, (.single (.point 0 (by grind) (.point 1 (by simp [points, point_arity, Vector.get]) h)))⟩
      | .point 1 hn h =>
        exact ⟨_, .single .swap, (.single (.point 0 (by grind) (.point 0 (by simp [points, point_arity, Vector.get]) h)))⟩
    case eql =>
      match hr with
      | .point n hn hr =>
        grind only [point_arity]
      | .congrFun (.point 0 hn hr) => exact ⟨_, .single .eql, .single (.point 0 (by grind) (.congrFun hr))⟩
      | .congrArg (.point 0 hn hr) => exact ⟨_, .single .eql, .single (.point 0 (by grind) (.congrArg hr))⟩
    case map | fmap =>
      exact ⟨_, .single (by constructor), aff_mk_point'' 0 hrp.congrFun⟩
    case unbox => exact ⟨_, .single (by constructor), .refl⟩
    case pair =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (by constructor), aff_mk_point'' 0 hr.congrFun⟩
      | .point 1 hn hr =>
        exact ⟨_, .single (by constructor), .trans (aff_mk_point'' 1 hr.congrFun) (aff_mk_point'' 2 hr.congrFun.congrArg)⟩
      | .point 2 hn hr =>
        exact ⟨_, .single (by constructor), aff_mk_point'' 2 hr.congrFun.congrFun⟩
    case evalc =>
      match hr with
      | .point 2 hn hr =>
        exact ⟨_, .single (by constructor), .single hr.congrFun.congrFun⟩
      | .point 0 hn hr | .point 1 hn hr =>
        exact ⟨_, .single (by constructor), .refl⟩
    case quot =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (by constructor), .refl⟩
      | .point 1 hn hr =>
        exact ⟨_, .single (by constructor), .single (by assumption)⟩
    case id | fstc | sndc =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .refl⟩
    case comp =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (by constructor), .single hr.congrFun⟩
      | .point 1 hn hr =>
        exact ⟨_, .single (by constructor), .single hr.congrFun.congrArg⟩
    case curr =>
      cases hr with
      | point _ hn _ => grind only [point_arity]
      | congrFun hr =>
        match hr with
        | .point 0 hn hr =>
          exact ⟨_, .single (by constructor), .refl⟩
        | .point 1 hn hr =>
          exact ⟨_, .single (by constructor), (congrArg' (aff_mk_point'' 0))⟩
        | .point 2 hn hr =>
          exact ⟨_, .single (by constructor), .single (.congrFun (by assumption))⟩
      | congrArg hr => exact ⟨_, .single (by constructor), (congrArg' (aff_mk_point'' 1))⟩
    case curr' =>
      cases hr with
      | point _ hn _ => grind only [point_arity]
      | congrFun hr =>
        match hr with
        | .point 0 hn hr =>
          exact ⟨_, .single (by constructor), .refl⟩
        | .point 1 hn hr => exact ⟨_, .single (by constructor), .single (.congrArg (.point 0 (by grind) (.point 0 (by simp [points, Vector.get, point_arity]) (by assumption))))⟩
        | .point 2 hn hr => exact ⟨_, .single (by constructor), .single (.congrFun (by assumption))⟩
      | congrArg hr =>
        match hr with
        | .point 0 hn hr => exact ⟨_, .single (by constructor), .single (.congrArg (.point 0 (by grind) (.point 1 (by simp [points, Vector.get, point_arity]) (by assumption))))⟩
    case congrFun hr₂ =>
      have ⟨_, ha, hb⟩ := ih hr₂
      exact ⟨_, congrFun' ha, congrFun' hb⟩
    case congrArg hr => exact ⟨_, .single (.congrArg (by assumption)), .single (.congrFun (by assumption))⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance Red.instConf : Confluent Red := ⟨Red.conf⟩

theorem red_aff_globally_conf {A B C : Expr} : Relation.ReflTransGen Red A B → Relation.ReflTransGen Red A C → ∃ D,
  Relation.ReflTransGen Red B D ∧ Relation.ReflTransGen Red C D :=
  Red.instRedRel.globally_confluent.conf

#check Relation.ReflTransGen.head_induction_on

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance instConfRedTrans : Confluent Red (m := Relation.ReflTransGen) := Red.instRedRel.globally_confluent

end Expr
