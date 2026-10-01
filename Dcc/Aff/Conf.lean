import Dcc.Aff.Rel
import Dcc.Aff.Run

/-
τ : Type u
inst : DecidableEq τ
n : ℕ
p' C a³ a² a¹ a : GenericExpr τ
h₂ : (a³.unify a² a¹ a).RedAff C
A : GenericExpr τ
heq : (a³.unify a² A A).point_arity = 4
hn : 2 < 4
h₁ : ((a³.unify a² A A).points.get ⟨2, hn⟩).RedAff p'
h :
  ∀ {C : GenericExpr τ},
    ((a³.unify a² A A).points.get ⟨2, hn⟩).RedAff C → ∃ D, instRedRel.ReflTrans p' D ∧ instRedRel.ReflTrans C D
⊢ ∃ D,
    instRedRel.ReflTrans ((a³.unify a² A A).set_points ((a³.unify a² A A).points.set 2 p' hn)) D ∧
      instRedRel.ReflTrans (a³.unif_refl a² A) D
-/

universe u
variable {τ : Type u}

namespace GenericExpr

open Dsl in
theorem RedAff.conf_dup_congr_arg (h₁ : RedAff (DCC? (& y)) x') : ∃ D,
  instRedRel.ReflTrans (DCC? ((Dup B x) (& env) x')) D ∧
  instRedRel.ReflTrans (DCC? (x env (,(`(B env) (B env)) y y))) D :=
  match h₁ with
  | .point 0 hn hr => by
    simp [points, Vector.get] at hr
    rename_i p'
    have h' := (RedAff.point (e := DCC? (,(`(B env) (B env)) p' y)) (p' := p') 2 (by point_arity)
        (by
          simp [points, Vector.get]
          exact hr))
    simp [set_points, points] at h'
    exact ⟨_, .single .dup, .trans (.single (.congrArg (.point 1 (by grind) hr))) (by
      simp [points, set_points]
      exact (.single (.congrArg h')))⟩

open Dsl in
theorem RedAff.conf_dup_congr_fun (h₁ : RedAff (DCC? ((Dup B x) (& env))) f') : ∃ D,
  instRedRel.ReflTrans (DCC? (f' (& y))) D ∧
  instRedRel.ReflTrans (DCC? (x env (,(`(B env) (B env)) y y))) D :=
  match h₁ with
  | .congrFun (.point 0 hn h) =>
    ⟨_, .single .dup, .trans (.single (.congrArg (.point 0 (by grind) (.point 0 (by point_arity) (.congrFun h)))))
                             (.single (.congrArg (.point 0 (by grind) (.point 1 (by point_arity) (.congrFun h)))))⟩
  | .congrFun (.point 1 hn h) =>
    ⟨_, .single .dup, .single (.congrFun (.congrFun h))⟩
  | .congrArg (.point 0 hn h) =>
    ⟨_, .single .dup, .trans (.single (.congrFun (.congrArg h)))
                             (.trans (.single (.congrArg (.point 0 (by grind) (.point 0 (by point_arity) (.congrArg h)))))
                                     (.single (.congrArg (.point 0 (by grind) (.point 1 (by point_arity) (.congrArg h))))))⟩

open Dsl in
theorem RedAff.conf_dup (h₂ : RedAff (DCC? ((Dup B x) (& env) (& y))) C) : ∃ D,
  instRedRel.ReflTrans (DCC? (x env (,(`(B env) (B env)) y y))) D ∧
  instRedRel.ReflTrans C D :=
  match h₂ with
  | .congrFun h =>
    have ⟨_, h₁, h₂⟩ := h.conf_dup_congr_fun
    ⟨_, h₂, h₁⟩
  | .congrArg h =>
    have ⟨_, h₁, h₂⟩ := h.conf_dup_congr_arg
    ⟨_, h₂, h₁⟩
  | .dup => ⟨_, .refl, .refl⟩

open Dsl in
theorem RedAff.conf_bimap_point₁ (h₁ : RedAff ((points (DCC? (Map A B f g))).get ⟨0, hn⟩) p') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (set_points (DCC? (Map A B f g)) ((points (DCC? (Map A B f g))).set 0 p' hn)) (DCC? (,_B x y))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A B) (f x) (g y))) D :=
  ⟨_, .single .bimap, .single (.point 0 (by grind) (.point 0 (by point_arity) h₁))⟩

open Dsl in
theorem RedAff.conf_bimap_point₂ (h₁ : RedAff ((points (DCC? (Map A B f g))).get ⟨1, hn⟩) p') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (set_points (DCC? (Map A B f g)) ((points (DCC? (Map A B f g))).set 1 p' hn)) (DCC? (,_B x y))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A B) (f x) (g y))) D :=
  ⟨_, .single .bimap, .single (.point 0 (by grind) (.point 1 (by point_arity) h₁))⟩

open Dsl in
theorem RedAff.conf_bimap_point₃ (h₁ : RedAff ((points (DCC? (Map A B f g))).get ⟨2, hn⟩) p') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (set_points (DCC? (Map A B f g)) ((points (DCC? (Map A B f g))).set 2 p' hn)) (DCC? (,_B x y))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A B) (f x) (g y))) D :=
  ⟨_, .single .bimap, .single (.point 1 (by grind) (.congrFun h₁))⟩

open Dsl in
theorem RedAff.conf_bimap_point₄ (h₁ : RedAff ((points (DCC? (Map A B f g))).get ⟨3, hn⟩) p') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (set_points (DCC? (Map A B f g)) ((points (DCC? (Map A B f g))).set 3 p' hn)) (DCC? (,_B x y))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A B) (f x) (g y))) D :=
  ⟨_, .single .bimap, .single (.point 2 (by grind) (.congrFun h₁))⟩

open Dsl in
theorem RedAff.conf_bimap_point₁_arg (_h₁ : RedAff ((points (DCC? (,_B x y))).get ⟨0, hn⟩) p') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (DCC? (Map A B f g)) (set_points (DCC? (,_B x y)) ((points (DCC? (,_B x y))).set 0 p' hn))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A B) (f x) (g y))) D :=
  ⟨_, .single .bimap, .refl⟩

open Dsl in
theorem RedAff.conf_bimap_point₂_arg (h₁ : RedAff ((points (DCC? (,_B x y))).get ⟨1, hn⟩) p') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (DCC? (Map A B f g)) (set_points (DCC? (,_B x y)) ((points (DCC? (,_B x y))).set 1 p' hn))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A B) (f x) (g y))) D :=
  ⟨_, .single .bimap, .single (.point 1 (by grind) (.congrArg h₁))⟩

open Dsl in
theorem RedAff.conf_bimap_point₃_arg (h₁ : RedAff ((points (DCC? (,_B x y))).get ⟨2, hn⟩) p') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (DCC? (Map A B f g)) (set_points (DCC? (,_B x y)) ((points (DCC? (,_B x y))).set 2 p' hn))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A B) (f x) (g y))) D :=
  ⟨_, .single .bimap, .single (.point 2 (by grind) (.congrArg h₁))⟩

open Dsl in
theorem RedAff.conf_assoc_point₁ (h₁ : RedAff ((points (DCC? (Assoc A B C))).get ⟨0, hn⟩) p') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (set_points (DCC? (Assoc A B C)) ((points (DCC? (Assoc A B C))).set 0 p' hn)) (DCC? (,_B₁ (,_B₂ x y) z))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A (Σ (`B C))) x (,(`B C) y z))) D :=
  ⟨_, .single .assoc, .single (.point 0 (by grind) (.point 0 (by point_arity) h₁))⟩

set_option maxHeartbeats 20000000000 in
open Dsl in
theorem RedAff.conf_assoc_point₂ (h₁ : RedAff ((points (DCC? (Assoc A B C))).get ⟨1, hn⟩) p') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (set_points (DCC? (Assoc A B C)) ((points (DCC? (Assoc A B C))).set 1 p' hn)) (DCC? (,_B₁ (,_B₂ x y) z))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A (Σ (`B C))) x (,(`B C) y z))) D := by
  refine ⟨_, .single .assoc, .trans (.single (.point 0 (by grind) (.point 1 (by point_arity) (.point 0 (by point_arity) (.point 0 ?_ h₁))))) (.single (.point 2 (by point_arity) (.point 0 (by point_arity) (.point 0 ?_ h₁))))⟩
  · have heq₁ : ((A.quot (B.quot C).coup).mkc x ((B.quot C).mkc y z)).points.get ⟨0, by grind⟩ = (A.quot (B.quot C).coup) := by
      simp [points, Vector.get]
    have heq₂ : (((A.quot (B.quot C).coup).mkc x ((B.quot C).mkc y z)).points.get ⟨0, by grind⟩).points.get ⟨1, by point_arity⟩ = (B.quot C).coup := by
      simp [points, Vector.get]
    have heq₃ : ((((A.quot (B.quot C).coup).mkc x ((B.quot C).mkc y z)).points.get ⟨0, by grind⟩).points.get ⟨1, by point_arity⟩).points.get ⟨0, by point_arity⟩ = (B.quot C) := by
      rfl
    change 0 < point_arity (B.quot C)
    grind
  · change 0 < point_arity (B.quot C)
    grind

set_option maxHeartbeats 20000000000 in
open Dsl in
theorem RedAff.conf_assoc_point₃ (h₁ : RedAff ((points (DCC? (Assoc A B C))).get ⟨2, hn⟩) p') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (set_points (DCC? (Assoc A B C)) ((points (DCC? (Assoc A B C))).set 2 p' hn)) (DCC? (,_B₁ (,_B₂ x y) z))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A (Σ (`B C))) x (,(`B C) y z))) D := by
  refine ⟨_, .single .assoc, .trans (.single (.point 0 (by grind) (.point 1 (by point_arity) (.point 0 (by point_arity) (.point 1 ?_ h₁))))) (.single (.point 2 (by point_arity) (.point 0 (by point_arity) (.point 1 ?_ h₁))))⟩
  · change 1 < point_arity (B.quot C)
    grind
  · change 1 < point_arity (B.quot C)
    grind

open Dsl in
theorem RedAff.conf_assoc_point₁_arg (h₁ : RedAff x x') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (DCC? (Assoc A B C)) (DCC? (,_B₁ (,_B₂ x' y) z))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A (Σ (`B C))) x (,(`B C) y z))) D :=
  ⟨_, .single .assoc, .single (.point 1 (by grind) h₁)⟩

open Dsl in
theorem RedAff.conf_assoc_point₂_arg (h₁ : RedAff y y') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (DCC? (Assoc A B C)) (DCC? (,_B₁ (,_B₂ x y') z))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A (Σ (`B C))) x (,(`B C) y z))) D :=
  ⟨_, .single .assoc, .single (.point 2 (by grind) (.point 1 (by point_arity) h₁))⟩

open Dsl in
theorem RedAff.conf_assoc_point₃_arg (h₁ : RedAff z z') : ∃ D,
  instRedRel.ReflTrans (GenericExpr.app (DCC? (Assoc A B C)) (DCC? (,_B₁ (,_B₂ x y) z'))) D ∧
    instRedRel.ReflTrans (DCC? (,(`A (Σ (`B C))) x (,(`B C) y z))) D :=
  ⟨_, .single .assoc, .single (.point 2 (by grind) (.point 2 (by point_arity) h₁))⟩

/-set_option maxHeartbeats 20000000000 in
theorem RedAff.conf_unif_refl_point₂
  {a₃ : GenericExpr τ}
  {hn : 2 < point_arity (a₃.unify a₂ A A)}
  (h₁ : ((unify a₃ a₂ A A).points.get ⟨2, hn⟩).RedAff p') : ∃ D,
    instRedRel.ReflTrans ((a₃.unify a₂ A A).set_points ((a₃.unify a₂ A A).points.set 2 p' hn)) D ∧
      instRedRel.ReflTrans (a₃.unif_refl a₂ A) D := by
  simp [set_points, points]
  simp [points, Vector.get] at h₁
  refine ⟨_, .trans (aff_mk_point' (.single h₁)
                     (n := 3)
                     (hn := (by simp [point_arity]))
                     (heq := (by simp [points]))) (.single .unif_refl), .trans (.trans (.trans (.trans
    (.trans (.single (.point 0 (by grind) (.point 1 (by point_arity) (.point 0 (by point_arity) h₁)))) (.single (.point 0 (by grind) (.point 1 (by point_arity) (.point 1 ?_ h₁)))))
    (.single (.point 2 (by grind) (.congrFun (.point 0 (by point_arity) (.point 1 (by point_arity) (.point 0 (by point_arity) h₁)))))))
    (.single (.point 2 ?_ (.congrFun (.point 1 ?_ (.point 1 ?_ (.point 0 ?_ h₁)))))))
    (.single (.point 2 ?_ (.congrFun (.point 2 ?_ (.point 1 ?_ (.congrArg (.point 0 ?_ h₁))))))))
    ?_⟩
  · simp [set_points, points, Vector.get]
    grind
  · simp [set_points, points, Vector.get]
    grind
  · simp [set_points, points, Vector.get]
    grind
  · simp [set_points, points, Vector.get]
    grind
  · have heq'' : (((((top.quot A.id).cong_mk (top.quot A.id) (top.quot (a₃.id.refl.app A.box))
                        (top.quot (a₂.id.refl.app A.box))).set_points
                    (((top.quot A.id).cong_mk (top.quot A.id) (top.quot (a₃.id.refl.app A.box))
                            (top.quot (a₂.id.refl.app A.box))).points.set
                      0
                      ((((top.quot A.id).cong_mk (top.quot A.id) (top.quot (a₃.id.refl.app A.box))
                                  (top.quot (a₂.id.refl.app A.box))).points.get
                            ⟨0, (by simp [point_arity])⟩).set_points
                        ((((top.quot A.id).cong_mk (top.quot A.id) (top.quot (a₃.id.refl.app A.box))
                                      (top.quot (a₂.id.refl.app A.box))).points.get
                                ⟨0, (by simp [point_arity])⟩).points.set
                          1
                          (((((top.quot A.id).cong_mk (top.quot A.id) (top.quot (a₃.id.refl.app A.box))
                                            (top.quot (a₂.id.refl.app A.box))).points.get
                                      ⟨0, (by simp [point_arity])⟩).points.get
                                ⟨1, (by simp [point_arity, points, Vector.get])⟩).set_points
                            (((((top.quot A.id).cong_mk (top.quot A.id) (top.quot (a₃.id.refl.app A.box))
                                                (top.quot (a₂.id.refl.app A.box))).points.get
                                          ⟨0, (by simp [point_arity])⟩).points.get
                                    ⟨1, (by simp [point_arity, points, Vector.get])⟩).points.set
                              0 p' (by simp [point_arity, points, Vector.get])))
                          (by simp [point_arity, points, Vector.get])))
                      (by simp [point_arity]))).points.get
              ⟨1, (by simp [point_arity, points, Vector.get, set_points])⟩).points.get
        ⟨1, (by simp [point_arity, points, Vector.get, set_points])⟩).point_arity = 1 := by
        rfl
    simp [heq'']
  · simp [set_points, points, Vector.get]
    grind
  · simp [set_points, points, Vector.get]
    grind
  · simp [set_points, points, Vector.get]
    grind
  · simp [point_arity]
  · refine (.single (.point 2 ?_ (.congrFun (.point 3 ?_ (.point 1 ?_ (.congrArg (.point 0 ?_ h₁)))))))
    · simp [set_points, points, Vector.get]
      grind
    · simp [set_points, points, Vector.get]
      grind
    · simp [set_points, points, Vector.get]
      grind
    · simp [point_arity]

set_option maxHeartbeats 20000000000 in
theorem RedAff.conf_unif_refl_point₃
  {a₃ : GenericExpr τ}
  {hn : 3 < point_arity (a₃.unify a₂ A A)}
  (h₁ : ((unify a₃ a₂ A A).points.get ⟨3, hn⟩).RedAff p') : ∃ D,
    instRedRel.ReflTrans ((a₃.unify a₂ A A).set_points ((a₃.unify a₂ A A).points.set 3 p' hn)) D ∧
      instRedRel.ReflTrans (a₃.unif_refl a₂ A) D := by
  simp [set_points, points]
  simp [points, Vector.get] at h₁
  refine ⟨_, .trans (aff_mk_point' (.single h₁)
                     (n := 2)
                     (hn := (by simp [point_arity]))
                     (heq := (by simp [points]))) (.single .unif_refl), .trans (.trans (.trans (.trans
    (.trans (.single (.point 0 (by grind) (.point 1 (by point_arity) (.point 0 (by point_arity) h₁)))) (.single (.point 0 (by grind) (.point 1 (by point_arity) (.point 1 ?_ h₁)))))
    (.single (.point 2 (by grind) (.congrFun (.point 0 (by point_arity) (.point 1 (by point_arity) (.point 0 (by point_arity) h₁)))))))
    (.single (.point 2 ?_ (.congrFun (.point 1 ?_ (.point 1 ?_ (.point 0 ?_ h₁)))))))
    (.single (.point 2 ?_ (.congrFun (.point 2 ?_ (.point 1 ?_ (.congrArg (.point 0 ?_ h₁))))))))
    ?_⟩
  · simp [set_points, points, Vector.get]
    grind
  · simp [set_points, points, Vector.get]
    grind
  · simp [set_points, points, Vector.get]
    grind
  · simp [set_points, points, Vector.get]
    grind
  · have heq'' : (((((top.quot A.id).cong_mk (top.quot A.id) (top.quot (a₃.id.refl.app A.box))
                        (top.quot (a₂.id.refl.app A.box))).set_points
                    (((top.quot A.id).cong_mk (top.quot A.id) (top.quot (a₃.id.refl.app A.box))
                            (top.quot (a₂.id.refl.app A.box))).points.set
                      0
                      ((((top.quot A.id).cong_mk (top.quot A.id) (top.quot (a₃.id.refl.app A.box))
                                  (top.quot (a₂.id.refl.app A.box))).points.get
                            ⟨0, (by simp [point_arity])⟩).set_points
                        ((((top.quot A.id).cong_mk (top.quot A.id) (top.quot (a₃.id.refl.app A.box))
                                      (top.quot (a₂.id.refl.app A.box))).points.get
                                ⟨0, (by simp [point_arity])⟩).points.set
                          1
                          (((((top.quot A.id).cong_mk (top.quot A.id) (top.quot (a₃.id.refl.app A.box))
                                            (top.quot (a₂.id.refl.app A.box))).points.get
                                      ⟨0, (by simp [point_arity])⟩).points.get
                                ⟨1, (by simp [point_arity, points, Vector.get])⟩).set_points
                            (((((top.quot A.id).cong_mk (top.quot A.id) (top.quot (a₃.id.refl.app A.box))
                                                (top.quot (a₂.id.refl.app A.box))).points.get
                                          ⟨0, (by simp [point_arity])⟩).points.get
                                    ⟨1, (by simp [point_arity, points, Vector.get])⟩).points.set
                              0 p' (by simp [point_arity, points, Vector.get])))
                          (by simp [point_arity, points, Vector.get])))
                      (by simp [point_arity]))).points.get
              ⟨1, (by simp [point_arity, points, Vector.get, set_points])⟩).points.get
        ⟨1, (by simp [point_arity, points, Vector.get, set_points])⟩).point_arity = 1 := by
        rfl
    simp [heq'']
  · simp [set_points, points, Vector.get]
    grind
  · simp [set_points, points, Vector.get]
    grind
  · simp [set_points, points, Vector.get]
    grind
  · simp [point_arity]
  · refine (.single (.point 2 ?_ (.congrFun (.point 3 ?_ (.point 1 ?_ (.congrArg (.point 0 ?_ h₁)))))))
    · simp [set_points, points, Vector.get]
      grind
    · simp [set_points, points, Vector.get]
      grind
    · simp [set_points, points, Vector.get]
      grind
    · simp [point_arity]-/

open Dsl in
theorem RedAff.conf_bimap_congr_arg (h : RedAff (DCC? (,_B x y)) x') : ∃ D, Relation.ReflTransGen RedAff (DCC? ((Map A B f g) x')) D
  ∧ Relation.ReflTransGen RedAff (DCC? (,(`A B) (f x) (g y))) D := by
  match h with
  | .point 0 hn h =>
    exact h.conf_bimap_point₁_arg (A := A) (B := B) (f := f) (g := g)
  | .point 1 hn h =>
    exact h.conf_bimap_point₂_arg (A := A) (B := B) (f := f) (g := g)
  | .point 2 hn h =>
    exact h.conf_bimap_point₃_arg (A := A) (B := B) (f := f) (g := g)

open Dsl in
theorem RedAff.conf_bimap_congr_fun (h : RedAff (DCC? (Map A B f g)) f') : ∃ D, Relation.ReflTransGen RedAff (DCC? (f' (,_B x y))) D
  ∧ Relation.ReflTransGen RedAff (DCC? (,(`A B) (f x) (g y))) D := by
  match h with
  | .point 0 hn h =>
    exact h.conf_bimap_point₁ (A := A) (B := B) (f := f) (g := g) (_B := _B) (x := x) (y := y)
  | .point 1 hn h =>
    exact h.conf_bimap_point₂ (A := A) (B := B) (f := f) (g := g) (_B := _B) (x := x) (y := y)
  | .point 2 hn h =>
    exact h.conf_bimap_point₃ (A := A) (B := B) (f := f) (g := g) (_B := _B) (x := x) (y := y)
  | .point 3 hn h =>
    exact h.conf_bimap_point₄ (A := A) (B := B) (f := f) (g := g) (_B := _B) (x := x) (y := y)

open Dsl in
theorem RedAff.conf_bimap (h₂ : RedAff (DCC? ((Map A B f g) (,_B x y))) C) : ∃ D, Relation.ReflTransGen RedAff (DCC? (,(`A B) (f x) (g y))) D 
  ∧ Relation.ReflTransGen RedAff C D := by
  cases h₂ with
  | bimap => exact ⟨_, .refl, .refl⟩
  | point => grind
  | congrFun h =>
    have ⟨_, h₁, h₂⟩ := h.conf_bimap_congr_fun (A := A) (B := B) (f := f) (g := g) (_B := _B) (x := x) (y := y)
    exact ⟨_, h₂, h₁⟩
  | congrArg h =>
    have ⟨_, h₁, h₂⟩ := h.conf_bimap_congr_arg (A := A) (B := B) (f := f) (g := g) (_B := _B) (x := x) (y := y)
    exact ⟨_, h₂, h₁⟩

open Dsl in
theorem RedAff.conf_assoc_congr_arg (h : RedAff (DCC? (,_B₁ (,_B₂ x y) z)) x') : ∃ D, Relation.ReflTransGen RedAff (DCC? ((Assoc A B C) x')) D
  ∧ Relation.ReflTransGen RedAff  (DCC? (,(`A (Σ (`B C))) x (,(`B C) y z))) D := by
  match h with
  | .point 0 hn hr => exact ⟨_, .single .assoc, .refl⟩
  | .point 1 hn hr =>
    simp [points, Vector.get] at hr
    match hr with
    | .point 0 hn hr => exact ⟨_, .single .assoc, .refl⟩
    | .point 1 hn hr =>
      exact hr.conf_assoc_point₁_arg (A := A) (B := B) (C := C) (x := x) (y := y) (z := z) (_B₁ := _B₁) (_B₂ := _B₂)
    | .point 2 hn hr =>
      exact hr.conf_assoc_point₂_arg (A := A) (B := B) (C := C) (x := x) (y := y) (z := z) (_B₁ := _B₁) (_B₂ := _B₂)
  | .point 2 hn hr =>
    exact hr.conf_assoc_point₃_arg (A := A) (B := B) (C := C) (x := x) (y := y) (z := z) (_B₁ := _B₁) (_B₂ := _B₂)

open Dsl in
theorem RedAff.conf_assoc_congr_fun (h : RedAff (DCC? (Assoc A B C)) f') : ∃ D, Relation.ReflTransGen RedAff (DCC? (f' (,_B₁ (,_B₂ x y) z))) D
  ∧ Relation.ReflTransGen RedAff  (DCC? (,(`A (Σ (`B C))) x (,(`B C) y z))) D := by
  match h with
  | .point 0 hn hr =>
    exact hr.conf_assoc_point₁ (A := A) (B := B) (C := C) (x := x) (y := y) (z := z) (_B₁ := _B₁) (_B₂ := _B₂)
  | .point 1 hn hr =>
    exact hr.conf_assoc_point₂ (A := A) (B := B) (C := C) (x := x) (y := y) (z := z) (_B₁ := _B₁) (_B₂ := _B₂)
  | .point 2 hn hr =>
    exact hr.conf_assoc_point₃ (A := A) (B := B) (C := C) (x := x) (y := y) (z := z) (_B₁ := _B₁) (_B₂ := _B₂)

open Dsl in
theorem RedAff.conf_assoc (h₂ : RedAff (DCC? ((Assoc A B C) (,_B₁ (,_B₂ x y) z))) C') : ∃ D, Relation.ReflTransGen RedAff (DCC? (,(`A (Σ (`B C))) x (,(`B C) y z))) D
  ∧ Relation.ReflTransGen RedAff C' D := by
  cases h₂ with
  | point => grind
  | assoc => exact ⟨_, .refl, .refl⟩
  | congrFun h =>
    have ⟨_, h₁, h₂⟩ := h.conf_assoc_congr_fun (A := A) (B := B) (C := C) (x := x) (y := y) (z := z) (_B₁ := _B₁) (_B₂ := _B₂)
    exact ⟨_, h₂, h₁⟩
    /-match h with
    | .point 0 hn hr =>
      have ⟨_, h₁, h₂⟩ := hr.conf_assoc_point₁ (A := A) (B := B) (C := C) (x := x) (y := y) (z := z) (_B₁ := _B₁) (_B₂ := _B₂)
      exact ⟨_, h₂, h₁⟩
    | .point 1 hn hr =>
      have ⟨_, h₁, h₂⟩ := hr.conf_assoc_point₂ (A := A) (B := B) (C := C) (x := x) (y := y) (z := z) (_B₁ := _B₁) (_B₂ := _B₂)
      exact ⟨_, h₂, h₁⟩
    | .point 2 hn hr =>
      have ⟨_, h₁, h₂⟩ := hr.conf_assoc_point₃ (A := A) (B := B) (C := C) (x := x) (y := y) (z := z) (_B₁ := _B₁) (_B₂ := _B₂)
      exact ⟨_, h₂, h₁⟩-/
  | congrArg h =>
    have ⟨_, h₁, h₂⟩ := h.conf_assoc_congr_arg (A := A) (B := B) (C := C) (x := x) (y := y) (z := z) (_B₁ := _B₁) (_B₂ := _B₂)
    exact ⟨_, h₂, h₁⟩
    /-match h with
    | .point 0 hn hr => exact ⟨_, .refl, .single .assoc⟩
    | .point 1 hn hr =>
      simp [points, Vector.get] at hr
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single .assoc⟩
      | .point 1 hn hr =>
        have ⟨_, h₁, h₂⟩ := hr.conf_assoc_point₁_arg
        exact ⟨_, h₂, h₁⟩
      | .point 2 hn hr =>
        have ⟨_, h₁, h₂⟩ := hr.conf_assoc_point₂_arg
        exact ⟨_, h₂, h₁⟩
    | .point 2 hn hr =>
      have ⟨_, h₁, h₂⟩ := hr.conf_assoc_point₃_arg
      exact ⟨_, h₂, h₁⟩-/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
theorem RedAff.conf_point (h₁ : RedAff ((points e).get ⟨n, hn⟩) p') (h₂ : RedAff e C)
  (h : ∀ {C : GenericExpr τ}, (e.points.get ⟨n, hn⟩).RedAff C → ∃ D, instRedRel.ReflTrans p' D ∧ instRedRel.ReflTrans C D) :
  ∃ D, RedAff.instRedRel.ReflTrans (e.set_points ((points e).set n p')) D ∧ RedAff.instRedRel.ReflTrans C D := by
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
    case unify =>
      simp [point_arity] at hn
      match h₂ with
      | .point 0 hn hr =>
        match n with
        | 0 =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, aff_mk_point' h₁ (n := 0) (hn := ?_) (heq := ?_), aff_mk_point' h₂ (n := 0) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | 1 =>
          simp [points, set_points]
          exact ⟨_, .single (.point 0 (by simp [point_arity]) hr), .single (.point 1 (by simp [point_arity]) h₁)⟩
        /-| 2 =>
          simp [points, set_points]
          exact ⟨_, .single (.point 0 (by simp [point_arity]) hr), .single (.point 2 (by simp [point_arity]) h₁)⟩
        | 3 =>
          simp [points, set_points]
          exact ⟨_, .single (.point 0 (by simp [point_arity]) hr), .single (.point 3 (by simp [point_arity]) h₁)⟩-/
      | .point 1 hn hr =>
        match n with
        | 1 =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, aff_mk_point' h₁ (n := 1) (hn := ?_) (heq := ?_), aff_mk_point' h₂ (n := 1) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | 0 =>
          simp [points, set_points]
          exact ⟨_, .single (.point 1 (by simp [point_arity]) hr), .single (.point 0 (by simp [point_arity]) h₁)⟩
        /-| 2 =>
          simp [points, set_points]
          exact ⟨_, .single (.point 1 (by simp [point_arity]) hr), .single (.point 2 (by simp [point_arity]) h₁)⟩
        | 3 =>
          simp [points, set_points]
          exact ⟨_, .single (.point 1 (by simp [point_arity]) hr), .single (.point 3 (by simp [point_arity]) h₁)⟩-/
      /-| .point 2 hn hr =>
        match n with
        | 2 =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, aff_mk_point' h₁ (n := 2) (hn := ?_) (heq := ?_), aff_mk_point' h₂ (n := 2) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | 0 =>
          simp [points, set_points]
          exact ⟨_, .single (.point 2 (by simp [point_arity]) hr), .single (.point 0 (by simp [point_arity]) h₁)⟩
        | 1 =>
          simp [points, set_points]
          exact ⟨_, .single (.point 2 (by simp [point_arity]) hr), .single (.point 1 (by simp [point_arity]) h₁)⟩
        | 3 =>
          simp [points, set_points]
          exact ⟨_, .single (.point 2 (by simp [point_arity]) hr), .single (.point 3 (by simp [point_arity]) h₁)⟩
      | .point 3 hn hr =>
        match n with
        | 3 =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, aff_mk_point' h₁ (n := 3) (hn := ?_) (heq := ?_), aff_mk_point' h₂ (n := 3) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | 0 =>
          simp [points, set_points]
          exact ⟨_, .single (.point 3 (by simp [point_arity]) hr), .single (.point 0 (by simp [point_arity]) h₁)⟩
        | 1 =>
          simp [points, set_points]
          exact ⟨_, .single (.point 3 (by simp [point_arity]) hr), .single (.point 1 (by simp [point_arity]) h₁)⟩
        | 2 =>
          simp [points, set_points]
          exact ⟨_, .single (.point 3 (by simp [point_arity]) hr), .single (.point 2 (by simp [point_arity]) h₁)⟩-/
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
        | .point 3 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 3 (by simp [point_arity]) hr), .single (.point 0 (by simp [point_arity]) h₁)⟩
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
        | .point 3 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 3 (by simp [point_arity]) hr), .single (.point 1 (by simp [point_arity]) h₁)⟩
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
          exact ⟨_, .single (.point 1 (by simp [point_arity]) hr), .single (.point 2 (by simp [point_arity]) h₁)⟩
        | .point 3 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 3 (by simp [point_arity]) hr), .single (.point 2 (by simp [point_arity]) h₁)⟩
      | 3 =>
        match h₂ with
        | .point 3 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, aff_mk_point' h₁ (n := 3) (hn := ?_) (heq := ?_), aff_mk_point' h₂ (n := 3) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 0 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 0 (by simp [point_arity]) hr), .single (.point 3 (by simp [point_arity]) h₁)⟩
        | .point 1 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 1 (by simp [point_arity]) hr), .single (.point 3 (by simp [point_arity]) h₁)⟩
        | .point 2 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 2 (by simp [point_arity]) hr), .single (.point 3 (by simp [point_arity]) h₁)⟩)

#check RedAff.conf_point

/-
Messages here:
447:143:
unsolved goals
case unif_refl
τ : Type u
inst : DecidableEq τ
A B τ_A₁ τ_A₂ A C : GenericExpr τ
h₂ : (τ_A₁.unify τ_A₂ A A).RedAff C
⊢ ∃ D, instRedRel.ReflTrans (τ_A₁.unif_refl τ_A₂ A) D ∧ instRedRel.ReflTrans C D

case unif_bot_sort
τ : Type u
inst : DecidableEq τ
A B τ_A τ_B : GenericExpr τ
u : Level
C : GenericExpr τ
h₂ : (τ_A.unify τ_B (sort (u + 1)) bot).RedAff C
⊢ ∃ D, instRedRel.ReflTrans (unif_bot_type u τ_A τ_B) D ∧ instRedRel.ReflTrans C D

case unif_bot_prop
τ : Type u
inst : DecidableEq τ
A B τ_A τ_B C : GenericExpr τ
h₂ : (τ_A.unify τ_B (sort 0) bot).RedAff C
⊢ ∃ D, instRedRel.ReflTrans (τ_A.unif_bot_prop τ_B) D ∧ instRedRel.ReflTrans C D
-/

/-open Dsl in
theorem RedAff.conf_unif_refl (h₂ : (DCC? (Unify τ_A₁ τ_A₂ A A)).RedAff (τ := τ) C) : ∃ D, instRedRel.ReflTrans (τ_A₁.unif_refl τ_A₂ A) D ∧ instRedRel.ReflTrans C D :=
  match h₂ with
  | .unif_refl => ⟨_, .refl, .refl⟩
  | .point 0 hn hr => by
    simp [set_points, points, GenericExpr.unif_refl]
    simp [Vector.get, points] at hr
    refine ⟨_, .single (.point 2 (by grind) (.congrFun (.point 2 (by grind) ?_))), .single .unif_refl⟩
    simp [points, Vector.get]
    apply RedAff.point 1 ?_
    · simp [points, Vector.get]
      refine (.congrFun (.point 0 ?_ ?_))
      · simp [point_arity]
      · simp [points, Vector.get]
        · exact .point 0 (by grind) (by assumption)
    · grind
  | .point 1 hn hr => by
    simp [set_points, points, GenericExpr.unif_refl]
    simp [Vector.get, points] at hr
    refine ⟨_, .single (.point 2 (by grind) (.congrFun (.point 3 (by grind) ?_))), .single .unif_refl⟩
    simp [points, Vector.get]
    apply RedAff.point 1 ?_
    · simp [points, Vector.get]
      refine (.congrFun (.point 0 ?_ ?_))
      · simp [point_arity]
      · simp [points, Vector.get]
        · exact .point 0 (by grind) (by assumption)
    · grind
  | .point 2 hn hr => by
    simp [set_points, points, GenericExpr.unif_refl]
    have ⟨_, h₁, h₂⟩ := conf_unif_refl_point₂ hr
    simp [points, set_points] at h₁
    exact ⟨_, h₂, h₁⟩
  | .point 3 hn hr => by
    simp [set_points, points, GenericExpr.unif_refl]
    have ⟨_, h₁, h₂⟩ := conf_unif_refl_point₃ hr
    simp [points, set_points] at h₁
    exact ⟨_, h₂, h₁⟩-/

/-open Dsl in
theorem RedAff.conf_unif_bot_sort (h₂ : (DCC? ((Unify (Sort (u + 2)) (Sort 0)) ((Sort u + 1) ≃ ⊥) ⊥)).RedAff (τ := τ) C) : ∃ D, instRedRel.ReflTrans (unif_bot_type u) D ∧ instRedRel.ReflTrans C D := by
  cases h₂ with
  | point => grind
  | unif_bot_sort => exact ⟨_, .refl, .refl⟩
  | congrArg h => nomatch h
  | congrFun h =>
    cases h with
    | point => grind
    | congrArg h =>
      match h with
      | .point 0 hn h =>
        nomatch h
      | .point 1 hn h =>
        nomatch h
    | congrFun h =>
      cases h with
      | point n hn hr =>
        match n with
        | 0 => nomatch hr
        | 1 => nomatch hr

open Dsl in
theorem RedAff.conf_unif_bot_prop (h₂ : (DCC? ((Unify (Sort 1) (Sort 0)) ((Sort 0) ≃ ⊥) ⊥)).RedAff (τ := τ) C) : ∃ D, instRedRel.ReflTrans GenericExpr.unif_bot_prop D ∧ instRedRel.ReflTrans C D := by
  cases h₂ with
  | point => grind
  | unif_bot_prop => exact ⟨_, .refl, .refl⟩
  | congrArg h => nomatch h
  | congrFun h =>
    cases h with
    | point => grind
    | congrArg h =>
      match h with
      | .point 0 hn h =>
        nomatch h
      | .point 1 hn h =>
        nomatch h
    | congrFun h =>
      cases h with
      | point n hn hr =>
        match n with
        | 0 => nomatch hr
        | 1 => nomatch hr
-/
set_option maxHeartbeats 10000000000 in
open Congruent' in
open Congruent in @[dcc_reduce, aesop safe apply (rule_sets := [DccReduce])]
theorem RedAff.conf (h₁ : (RedAff (τ := τ)) A B) (h₂ : RedAff A C) : ∃ D, RedAff.instRedRel.ReflTrans B D ∧ RedAff.instRedRel.ReflTrans C D := by
  induction h₁ generalizing C
  -- Inner congruences:
  case point h => exact conf_point (by assumption) h₂ h
  /-case unif_refl =>
    exact conf_unif_refl h₂-/
  /-case unif_bot_sort =>
    exact conf_unif_bot_sort h₂
  case unif_bot_prop =>
    exact conf_unif_bot_prop h₂-/
  case assoc => exact h₂.conf_assoc
  case bimap => exact h₂.conf_bimap
  case dup => exact h₂.conf_dup
  case cong_1 =>
    match h₂ with
    | .cong_1 => exact ⟨_, .refl, .refl⟩
    | .congrFun (.point 0 hn h) =>
      exact ⟨_, .refl, .single .cong_1⟩
    | .congrFun (.point 1 hn h) =>
      exact ⟨_, .refl, .single .cong_1⟩
    | .congrArg (.congrFun (.point 0 hn hr)) =>
      exact ⟨_, .single (.congrFun hr), .single .cong_1⟩
    | .congrArg (.congrFun (.point 1 hn hr)) =>
      exact ⟨_, .refl, .single .cong_1⟩
    | .congrArg (.congrFun (.point 2 hn hr)) =>
      exact ⟨_, .refl, .single .cong_1⟩
    | .congrArg (.congrFun (.point 3 hn hr)) =>
      exact ⟨_, .refl, .single .cong_1⟩
    | .congrArg (.congrArg hr) =>
      exact ⟨_, .single (.congrArg hr), .single .cong_1⟩
  case cong_3 =>
    match h₂ with
    | .cong_3 => exact ⟨_, .refl, .refl⟩
    | .congrFun (.point 0 hn h) =>
      exact ⟨_, .refl, .single .cong_3⟩
    | .congrFun (.point 1 hn h) =>
      exact ⟨_, .refl, .single .cong_3⟩
    | .congrArg (.point 0 hn₀ hr) =>
      simp [point_arity] at hn₀
      simp [points, Vector.get] at hr
      match hr with
      | (.congrFun (.point 0 hn hr)) =>
        exact ⟨_, .refl, .single .cong_3⟩
      | (.congrFun (.point 1 hn hr)) =>
        exact ⟨_, .refl, .single .cong_3⟩
      | (.congrFun (.point 2 hn hr)) =>
        exact ⟨_, .single (.congrFun hr), .single .cong_3⟩
      | (.congrFun (.point 3 hn hr)) =>
        exact ⟨_, .refl, .single .cong_3⟩
      | (.congrArg hr) =>
        exact ⟨_, .single (.congrArg hr), .single .cong_3⟩
  case cong_2 =>
    match h₂ with
    | .cong_2 => exact ⟨_, .refl, .refl⟩
    | .congrFun (.point 1 hn h) =>
      exact ⟨_, .refl, .single .cong_2⟩
    | .congrFun (.point 0 hn h) =>
      exact ⟨_, .refl, .single .cong_2⟩
    | .congrArg (.congrFun (.point 0 hn hr)) =>
      exact ⟨_, .refl, .single .cong_2⟩
    | .congrArg (.congrFun (.point 1 hn hr)) =>
      exact ⟨_, .single (.congrFun hr), .single .cong_2⟩
    | .congrArg (.congrFun (.point 2 hn hr)) =>
      exact ⟨_, .refl, .single .cong_2⟩
    | .congrArg (.congrFun (.point 3 hn hr)) =>
      exact ⟨_, .refl, .single .cong_2⟩
    | .congrArg (.congrArg hr) =>
      exact ⟨_, .single (.congrArg hr), .single .cong_2⟩
  case cong_4 =>
    match h₂ with
    | .cong_4 => exact ⟨_, .refl, .refl⟩
    | .congrFun (.point 1 hn h) =>
      exact ⟨_, .refl, .single .cong_4⟩
    | .congrFun (.point 0 hn h) =>
      exact ⟨_, .refl, .single .cong_4⟩
    | .congrArg (.point 0 hn₀ hr) =>
      simp [point_arity] at hn₀
      simp [points, Vector.get] at hr
      match hr with
      | (.congrFun (.point 0 hn hr)) =>
        exact ⟨_, .refl, .single .cong_4⟩
      | (.congrFun (.point 1 hn hr)) =>
        exact ⟨_, .refl, .single .cong_4⟩
      | (.congrFun (.point 3 hn hr)) =>
        exact ⟨_, .single (.congrFun hr), .single .cong_4⟩
      | (.congrFun (.point 2 hn hr)) =>
        exact ⟨_, .refl, .single .cong_4⟩
      | (.congrArg hr) =>
        exact ⟨_, .single (.congrArg hr), .single .cong_4⟩
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
  case eqlτ₃ =>
    cases h₂ with
    | dom₂₀ h =>
      cases h with
      | point n hn h =>
        simp [point_arity] at hn
        match n with
        | 0 => exact ⟨_, .single (by assumption), .single (by constructor)⟩
    | point =>
      dcc_simp_all
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case reflτ₃ =>
    cases h₂ with
    | dom₂₀ h =>
      cases h
      case _ h => exact ⟨_, .single (by constructor; assumption), .single (by constructor)⟩
    | point =>
      dcc_simp_all
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case currτ₃ =>
    cases h₂ with
    | dom₂₀ h =>
      cases h
      expose_names
      match n with
      | 0 => exact ⟨_, .refl, .single (by constructor)⟩
      | 1 => exact ⟨_, .single (by assumption), .single (by constructor)⟩
      | 2 => exact ⟨_, .refl, .single (by constructor)⟩
    | point =>
      dcc_simp_all
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case curr'τ₃ =>
    cases h₂ with
    | dom₂₀ h =>
      cases h
      expose_names
      match n with
      | 0 => exact ⟨_, .refl, .single (by constructor)⟩
      | 1 => exact ⟨_, .single (.point 0 (by grind) (by assumption)), .single (by constructor)⟩
      | 2 => exact ⟨_, .refl, .single (by constructor)⟩
    | point =>
      dcc_simp_all
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case dom₂₀ ih =>
    match h₂ with
    | .eqlτ₃ =>
      rename_i hr
      cases hr
      expose_names
      match n with
      | 0 => exact ⟨_, .single .eqlτ₃, .single h_1⟩
    | .reflτ₃ =>
      rename_i hr
      cases hr
      expose_names
      match n with
      | 0 => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (by assumption))⟩
    | .dom₂₀ h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, dom₂' h₁, dom₂' h₂⟩
    | .currτ₃ =>
      rename_i hr
      cases hr
      expose_names
      match n with
      | 0 => exact ⟨_, .single (by constructor), .refl⟩
      | 1 => exact ⟨_, .single .currτ₃, .single (by assumption)⟩
      | 2 => exact ⟨_, .single .currτ₃, .refl⟩
    | .curr'τ₃ =>
      rename_i hr
      cases hr
      expose_names
      match n with
      | 0 => exact ⟨_, .single (by constructor), .refl⟩
      | 1 => exact ⟨_, .single .curr'τ₃, .single (.point 0 (by grind) (by assumption))⟩
      | 2 => exact ⟨_, .single .curr'τ₃, .refl⟩
  /-case swap₁ ih =>
    match h₂ with
    | .swap₀ h =>
      exact ⟨_, .single (.swap₀ h), .single (.swap₁ (by assumption))⟩
    | .swap₁ h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, swap₁' h₁, swap₁' h₂⟩
  case swap₀ ih =>
    match h₂ with
    | .swap₁ h =>
      exact ⟨_, .single (.swap₁ h), .single (.swap₀ (by assumption))⟩
    | .swap₀ h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, swap₀' h₁, swap₀' h₂⟩-/
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
  case uncoup =>
    match h₂ with
    | .uncoup₀ (.point 0 hn h) => exact ⟨_, .single h, .single .uncoup⟩
    | .uncoup => exact ⟨_, .refl, .refl⟩
  case unbang =>
    match h₂ with
    | .unbang₀ (.point 0 hn h) => exact ⟨_, .single h, .single .unbang⟩
    | .unbang => exact ⟨_, .refl, .refl⟩
  case uncoup₀ =>
    match h₂ with
    | .uncoup₀ h =>
      rename_i h₀ ih
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, uncoup' h₁, uncoup' h₂⟩
    | .uncoup =>
      rename_i h ih
      match h with
      | .point 0 hn h => exact ⟨_, .single (by constructor), .single h⟩
  case unbang₀ =>
    match h₂ with
    | .unbang₀ h =>
      rename_i h₀ ih
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, unbang' h₁, unbang' h₂⟩
    | .unbang =>
      rename_i h ih
      match h with
      | .point 0 hn h => exact ⟨_, .single (by constructor), .single h⟩
  /-
    Domain reductions
  -/
  case bimapτ₀ =>
    match h₂ with
    | .dom₀ (.point 0 hn hr) => exact ⟨_, .refl, .single (by constructor)⟩
    | .dom₀ (.point 1 hn hr) => exact ⟨_, .refl, .single (by constructor)⟩
    | .dom₀ (.point 2 hn hr) => exact ⟨_, .single (.point 0 (by grind) (.point 0 (by point_arity) (.dom₀ hr))), .single (by constructor)⟩
    | .dom₀ (.point 3 hn hr) => exact ⟨_, .single (.point 0 (by grind) (.point 1 (by point_arity) (.dom₀ hr))), .single (by constructor)⟩
    | .bimapτ₀ => exact ⟨_, .refl, .refl⟩
  case assocτ₀ =>
    match h₂ with
    | .dom₀ (.point 0 hn hr) =>
      exact ⟨_, .single (.point 0 (by grind) (.point 0 (by point_arity) (.point 0 (by point_arity) (.point 0 (by point_arity) hr)))), .single (by constructor)⟩
    | .dom₀ (.point 1 hn hr) =>
      exact ⟨_, .single (.point 0 (by grind) (.point 0 (by point_arity) (.point 0 (by point_arity) (.point 1 (by point_arity) hr)))), .single (by constructor)⟩
    | .dom₀ (.point 2 hn hr) =>
      exact ⟨_, .single (.point 0 (by grind) (.point 1 (by point_arity) hr)), .single (by constructor)⟩
    | .assocτ₀ => exact ⟨_, .refl, .refl⟩
  case bool_indτ₀ =>
    match h₂ with
    | .bool_indτ₀ => exact ⟨_, .refl, .refl⟩
    | .dom₀ (.point 0 hn hr) => exact ⟨_, .single (.dom₀ hr), .single (by constructor)⟩
    | .dom₀ (.point 1 hn hr) => exact ⟨_, .refl, .single (by constructor)⟩
    | .dom₀ (.point 2 hn hr) => exact ⟨_, .refl, .single (by constructor)⟩
  case cong_2τ₀ | cong_1τ₀ =>
    cases h₂
    case dom₀ hr =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (.point 0 (by grind) hr), .single (by constructor)⟩
      | .point 1 hn hr =>
        exact ⟨_, .single (.point 1 (by grind) hr), .single (by constructor)⟩
    case _ => grind only [point_arity]
    case _ => exact ⟨_, .refl, .refl⟩
  case cong_3τ₀ | cong_4τ₀ =>
    cases h₂
    case dom₀ hr =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (.point 0 (by grind) (.point 0 (by point_arity) hr)), .single (by constructor)⟩
      | .point 1 hn hr =>
        exact ⟨_, .single (.point 0 (by grind) (.point 1 (by point_arity) hr)), .single (by constructor)⟩
    case _ => grind only [point_arity]
    case _ => exact ⟨_, .refl, .refl⟩
  case unboxτ₀ =>
    match h₂ with
    | .dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (.point 0 (by grind) hr), .single (by constructor)⟩
    | .unboxτ₀ => exact ⟨_, .refl, .refl⟩
  case swapτ₀ =>
    match h₂ with
    | .dom₀ (.point 0 hn hr) =>
      exact ⟨_, .single (.point 0 (by grind) (.point 0 (by simp [point_arity, points, Vector.get]) hr)), .single (by constructor)⟩
    | .dom₀ (.point 1 hn hr) =>
      exact ⟨_, .single (.point 0 (by grind) (.point 1 (by simp [point_arity, points, Vector.get]) hr)), .single (by constructor)⟩
    | .swapτ₀ => exact ⟨_, .refl, .refl⟩
  case eqlτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (.dom₀ hr), .single (by constructor)⟩
    | _ =>
      expose_names
      try (simp [point_arity] at h)
      try (exact ⟨_, .refl, .refl⟩)
  case reflτ₀ | mapτ₀ | fmapτ₀ =>
    cases h₂ with
    | dom₀ hr =>
     match hr with
     | (.point 0 hn hr) => exact ⟨_, .single (.point 0 (by grind) (.dom₀ hr)), .single (by constructor)⟩
    | _ =>
      expose_names
      try (simp [point_arity] at h)
      try (exact ⟨_, .refl, .refl⟩)
  case pairτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single (.point 0 (by grind) hr.dom₀), .single (by constructor)⟩
      | .point 2 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
    | pairτ₀ => exact ⟨_, .refl, .refl⟩
    | point =>
      expose_names
      simp [point_arity] at h
  case evalcτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single (.point 0 (by grind) hr), .single (by constructor)⟩
      | .point 2 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
    | evalcτ₀ => exact ⟨_, .refl, .refl⟩
    | point =>
      expose_names
      simp [point_arity] at h
  case curr'τ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 2 hn h => exact ⟨_, .single (.point 0 (by grind) (h.dom₀.unbang₀.uncoup₀.dom₀)), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case currτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 2 hn h => exact ⟨_, .single h.dom₀.uncoup₀.dom₀, .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case sndcτ₀ | fstcτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (.point 0 (by grind) hr), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case idτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single hr, .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case quotτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by assumption), .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case compτ₀ | sigmaτ₀ | piτ₀ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single hr.dom₀, .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case eqlτ₁ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .congrArg h => exact ⟨_, .trans (.single (.point 0 (by grind) (.point 0 (by point_arity) (.congrArg (by assumption)))))
                                        (.single (.point 0 (by grind) (.point 1 (by point_arity) (.congrArg (by assumption)))))
                               , .single (by constructor)⟩
      | .congrFun h =>
        match h with
        | .point 0 hn h =>
          exact ⟨_, .trans (.single (.point 0 (by grind) (.point 0 (by point_arity) (.congrFun (by assumption)))))
                           (.single (.point 0 (by grind) (.point 1 (by point_arity) (.congrFun (by assumption)))))
                  , .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case reflτ₁ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .congrArg (.point 0 hn h) => exact ⟨_, .single (.point 0 (by grind) h.congrArg), .single (by constructor)⟩
      | .congrFun h =>
        match h with
        | .point 0 hn h => exact ⟨_, .single (.point 0 (by grind) h.congrFun), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case currτ₁ =>
    cases h₂ with
    | dom₀ hr =>
      cases hr with
      | congrFun h =>
        match h with
        | .point 1 hn h | .point 0 hn h => exact ⟨_, .refl, .single (by constructor)⟩
        | .point 2 hn h => exact ⟨_, .single h.dom₀.uncoup₀.congrFun, .single (by constructor)⟩
      | congrArg h => exact ⟨_, .single h.congrArg, .single (by constructor)⟩
      | point =>
        expose_names
        simp [point_arity] at h
    | point =>
        expose_names
        simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case curr'τ₁ =>
    cases h₂ with
    | dom₀ hr =>
      match hr with
      | .congrFun h =>
        match h with
        | .point 2 hn h =>
          exact ⟨_, .single (.point 0 (by grind) (h.dom₀.unbang₀.uncoup₀.congrFun)), .single (by constructor)⟩
        | .point 1 hn h | .point 0 hn h => exact ⟨_, .refl, .single (by constructor)⟩
      | .congrArg (.point 0 hn h) => exact ⟨_, .single (.point 0 (by grind) h.congrArg), .single (by constructor)⟩
    | point =>
      expose_names
      simp [point_arity] at h
    | _ => exact ⟨_, .refl, .refl⟩
  case dom₀ ih =>
    cases h₂
    case point hn hr => simp [point_arity] at hn
    case bimapτ₀ hr =>
      match hr with
      | (.point 0 hn hr) => exact ⟨_, .single (by constructor), .refl⟩
      | (.point 1 hn hr) => exact ⟨_, .single (by constructor), .refl⟩
      | (.point 2 hn hr) => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (.point 0 (by point_arity) (.dom₀ hr)))⟩
      | (.point 3 hn hr) => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (.point 1 (by point_arity) (.dom₀ hr)))⟩
    case bool_indτ₀ hr =>
      match hr with
      | (.point 0 hn hr) => exact ⟨_, .single (by constructor), .single (.dom₀ hr)⟩
      | (.point 1 hn hr) => exact ⟨_, .single (by constructor), .refl⟩
      | (.point 2 hn hr) => exact ⟨_, .single (by constructor), .refl⟩
    case cong_2τ₀ hr | cong_1τ₀ hr =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr)⟩
      | .point 1 hn hr =>
        exact ⟨_, .single (by constructor), .single (.point 1 (by grind) hr)⟩
    case cong_3τ₀ hr | cong_4τ₀ hr =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (.point 0 (by point_arity) hr))⟩
      | .point 1 hn hr =>
        exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (.point 1 (by point_arity) hr))⟩
    case assocτ₀ hr =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (.point 0 (by point_arity) (.point 0 (by point_arity) (.point 0 (by point_arity) hr))))⟩
      | .point 1 hn hr =>
        exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (.point 0 (by point_arity) (.point 0 (by point_arity) (.point 1 (by point_arity) hr))))⟩
      | .point 2 hn hr =>
        exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (.point 1 (by point_arity) hr))⟩
    case swapτ₀ hr =>
      match hr with
      | .point 0 hn h =>
        exact ⟨_, .single .swapτ₀, .single (.point 0 (by grind) (.point 0 (by simp [point_arity, points, Vector.get]) h))⟩
      | .point 1 hn h =>
        exact ⟨_, .single .swapτ₀, .single (.point 0 (by grind) (.point 1 (by simp [point_arity, points, Vector.get]) h))⟩
    case unboxτ₀ hr =>
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr)⟩
    case eqlτ₀ =>
      rename_i hr
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (by constructor), .single (.dom₀ hr)⟩
    case reflτ₀ | mapτ₀ | fmapτ₀ =>
      rename_i hr
      match hr with
      | .point 0 hn hr =>
        exact ⟨_, .single (by constructor), .single (.point 0 (by grind) (.dom₀ hr))⟩
    case pairτ₀ =>
      rename_i hr
      match hr with
      | .point 0 hn hr | .point 2 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 1 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr.dom₀)⟩
    case evalcτ₀ =>
      rename_i hr
      match hr with
      | .point 0 hn hr | .point 2 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 1 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr)⟩
    case idτ₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .single hr⟩
    case quotτ₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .single hr⟩
      | .point 1 hn hr => exact ⟨_, .single (by constructor), .refl⟩
    case fstcτ₀ hr | sndcτ₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr)⟩
    case compτ₀ hr | sigmaτ₀ hr | piτ₀ hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 1 hn hr => exact ⟨_, .single (by constructor), .single hr.dom₀⟩
    case currτ₀ =>
      rename_i hr
      match hr with
      | .point 1 hn hr | .point 0 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 2 hn h => exact ⟨_, .single (by constructor), .single h.dom₀.uncoup₀.dom₀⟩
    case curr'τ₀ =>
      rename_i hr
      match hr with
      | .point 1 hn hr | .point 0 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 2 hn h => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) h.dom₀.unbang₀.uncoup₀.dom₀)⟩
    case eqlτ₁ hr =>
      cases hr with
      | congrFun h =>
        match h with
        | .point 0 hn hr => exact ⟨_, .single (by constructor),
                                       .trans (.single (.point 0 (by grind) (.point 0 (by point_arity) (.congrFun (by assumption)))))
                                              (.single (.point 0 (by grind) (.point 1 (by point_arity) (.congrFun (by assumption)))))⟩
      | congrArg h =>
        exact ⟨_, .single (by constructor),
                  .trans (.single (.point 0 (by grind) (.point 0 (by point_arity) (.congrArg (by assumption)))))
                         (.single (.point 0 (by grind) (.point 1 (by point_arity) (.congrArg (by assumption)))))⟩
      | point =>
        expose_names
        simp [point_arity] at h
    case reflτ₁ hr =>
      cases hr with
      | congrFun h =>
        match h with
        | .point 0 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr.congrFun)⟩
      | congrArg h =>
        match h with
        | .point 0 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr.congrArg)⟩
      | point =>
        expose_names
        simp [point_arity] at h
    case currτ₁ hr =>
      cases hr with
      | congrFun hr =>
        match hr with
        | .point 0 hn hr | .point 1 hn hr =>
          exact ⟨_, .single (by constructor), .refl⟩
        | .point 2 hn hr =>
          exact ⟨_, .single (by constructor), .single hr.dom₀.uncoup₀.congrFun⟩
      | congrArg hr =>
        exact ⟨_, .single (by constructor), .single hr.congrArg⟩
      | point =>
        expose_names
        simp [point_arity] at h
    case curr'τ₁ hr =>
      cases hr with
      | congrFun hr =>
        match hr with
        | .point 1 hn hr | .point 0 hn hr =>
          exact ⟨_, .single (by constructor), .refl⟩
        | .point 2 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr.dom₀.unbang₀.uncoup₀.congrFun)⟩
      | congrArg hr =>
        match hr with
        | .point 0 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr.congrArg)⟩
      | point =>
        expose_names
        simp [point_arity] at h
    case dom₀ hr =>
      have ⟨_, h₁, h₂⟩ := ih hr
      exact ⟨_, dom' (by assumption), dom' (by assumption)⟩
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
        exact ⟨_, .single (.point 0 (by grind) (.congrArg (by assumption))), .single (by constructor)⟩
    | congrArg hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single (.point 1 (by grind) hr), .single (by constructor)⟩
      | .point 2 hn hr => exact ⟨_, .single (.point 2 (by grind) hr), .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case fmap | map =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .single ((RedAff.congrFun h.right).mk_point (n := ⟨0, by grind⟩)), .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .single ((RedAff.congrArg h.right).mk_point (n := ⟨0, by grind⟩)), .single (by constructor)⟩
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
        | .point 1 hn hr => exact ⟨_, .single (RedAff.point 0 (by grind) hr).congrArg, .single (by constructor)⟩
        | .point 2 hn hr => exact ⟨_, .single hr.congrFun, .single (by constructor)⟩
      | point =>
        expose_names
        simp [point_arity] at h
      | congrArg hr =>
        exact ⟨_, .single (.congrArg (RedAff.point 1 (by grind) hr)), .single (by constructor)⟩
    | congrArg hr =>
      exact ⟨_, .single (.congrArg (RedAff.point 2 (by grind) hr)), .single (by constructor)⟩
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
  case sigma =>
    cases h₂ with
    | congrFun hr =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .refl, .single (by constructor)⟩
      | .point 1 hn hr => exact ⟨_, .single (.point 0 (by grind) hr.congrFun), .single (by constructor)⟩
    | congrArg hr =>
      case _ hr => exact ⟨_, .single (.point 0 (by grind) hr.congrArg), .single (by constructor)⟩
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
    case ind_bool_true | ind_bool_false =>
      nomatch hr
    case point h => grind only [point_arity]
    case assoc =>
      exact hr.conf_assoc_congr_arg
    case bimap =>
      exact hr.conf_bimap_congr_arg
    case dup =>
      exact hr.conf_dup_congr_arg
    /-case unif_bot_sort => nomatch hr
    case unif_bot_prop => nomatch hr-/
    case cong_1 =>
      match hr with
      | .congrFun (.point 0 hn h) =>
        exact ⟨_, .single .cong_1, .single (.congrFun h)⟩
      | .congrFun (.point 1 hn h) =>
        exact ⟨_, .single .cong_1, .refl⟩
      | .congrFun (.point 2 hn h) =>
        exact ⟨_, .single .cong_1, .refl⟩
      | .congrFun (.point 3 hn h) =>
        exact ⟨_, .single .cong_1, .refl⟩
      | .congrArg h => exact ⟨_, .single .cong_1, .single (.congrArg h)⟩
      | .point 0 hn hr =>
        exact ⟨_, .single .cong_1, .refl⟩
      | .point 1 hn hr => grind
      | .point 2 hn hr =>
        exact ⟨_, .single .cong_1, .refl⟩
      | .point 3 hn hr =>
        exact ⟨_, .single .cong_1, .refl⟩
    case cong_2 =>
      match hr with
      | .congrFun (.point 1 hn h) =>
        exact ⟨_, .single .cong_2, .single (.congrFun h)⟩
      | .congrFun (.point 0 hn h) =>
        exact ⟨_, .single .cong_2, .refl⟩
      | .congrFun (.point 2 hn h) =>
        exact ⟨_, .single .cong_2, .refl⟩
      | .congrFun (.point 3 hn h) =>
        exact ⟨_, .single .cong_2, .refl⟩
      | .congrArg h => exact ⟨_, .single .cong_2, .single (.congrArg h)⟩
      | .point 0 hn hr =>
        exact ⟨_, .single .cong_2, .refl⟩
      | .point 1 hn hr => grind
      | .point 2 hn hr =>
        exact ⟨_, .single .cong_2, .refl⟩
      | .point 3 hn hr =>
        exact ⟨_, .single .cong_2, .refl⟩
    case cong_3 =>
      match hr with
      | .point 0 hn hr =>
        match hr with
        | .congrFun (.point 2 hn h) =>
          exact ⟨_, .single .cong_3, .single (.congrFun h)⟩
        | .congrFun (.point 0 hn h) =>
          exact ⟨_, .single .cong_3, .refl⟩
        | .congrFun (.point 1 hn h) =>
          exact ⟨_, .single .cong_3, .refl⟩
        | .congrFun (.point 3 hn h) =>
          exact ⟨_, .single .cong_3, .refl⟩
        | .congrArg h => exact ⟨_, .single .cong_3, .single (.congrArg h)⟩
        | .point 0 hn hr =>
          exact ⟨_, .single .cong_3, .refl⟩
        | .point 1 hn hr =>
          simp [point_arity, points, Vector.get] at hn
        | .point 2 hn hr =>
          exact ⟨_, .single .cong_3, .refl⟩
        | .point 3 hn hr =>
          exact ⟨_, .single .cong_3, .refl⟩
    case cong_4 =>
      match hr with
      | .point 0 hn hr =>
        match hr with
        | .congrFun (.point 3 hn h) =>
          exact ⟨_, .single .cong_4, .single (.congrFun h)⟩
        | .congrFun (.point 0 hn h) =>
          exact ⟨_, .single .cong_4, .refl⟩
        | .congrFun (.point 1 hn h) =>
          exact ⟨_, .single .cong_4, .refl⟩
        | .congrFun (.point 2 hn h) =>
          exact ⟨_, .single .cong_4, .refl⟩
        | .congrArg h => exact ⟨_, .single .cong_4, .single (.congrArg h)⟩
        | .point 0 hn hr =>
          exact ⟨_, .single .cong_4, .refl⟩
        | .point 1 hn hr =>
          simp [point_arity, points, Vector.get] at hn
        | .point 2 hn hr =>
          exact ⟨_, .single .cong_4, .refl⟩
        | .point 3 hn hr =>
          exact ⟨_, .single .cong_4, .refl⟩
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
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 1 hn hr => exact ⟨_, .single (by constructor), .single (.point 1 (by grind) hr)⟩
      | .point 2 hn hr => exact ⟨_, .single (by constructor), .single (.point 2 (by grind) hr)⟩
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
    case sigma => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr.congrArg)⟩
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
    case point => grind only [point_arity]
    /-case unif_bot_sort =>
      cases hr with
      | congrFun h =>
        cases h with
        | point n hn hr =>
          match n with
          | 0 =>
            simp [points, Vector.get] at hr
            nomatch hr
          | 1 =>
            simp [points, Vector.get] at hr
            nomatch hr
      | congrArg h =>
        cases h
        case point n hn h =>
          simp [point_arity] at hn
          match n with
          | 0 =>
            simp [points, Vector.get] at h
            nomatch h
          | 1 =>
            simp [points, Vector.get] at h
            nomatch h
      | point => grind only [point_arity]
    case unif_bot_prop =>
      cases hr with
      | congrFun h =>
        cases h with
        | point n hn hr =>
          match n with
          | 0 =>
            simp [points, Vector.get] at hr
            nomatch hr
          | 1 =>
            simp [points, Vector.get] at hr
            nomatch hr
      | congrArg h =>
        cases h
        case point n hn h =>
          simp [point_arity] at hn
          match n with
          | 0 =>
            simp [points, Vector.get] at h
            nomatch h
          | 1 =>
            simp [points, Vector.get] at h
            nomatch h
      | point => grind only [point_arity]-/
    case assoc => exact RedAff.conf_assoc_congr_fun (by assumption)
    case bimap => exact RedAff.conf_bimap_congr_fun (by assumption)
    case dup => exact RedAff.conf_dup_congr_fun (by assumption)
    case cong_1 =>
      match hr with
      | (.point 0 hn hr) =>
        exact ⟨_, .single .cong_1, .refl⟩
      | (.point 1 hn hr) =>
        exact ⟨_, .single .cong_1, .refl⟩
    case cong_2 =>
      match hr with
      | (.point 1 hn hr) =>
        exact ⟨_, .single .cong_2, .refl⟩
      | (.point 0 hn hr) =>
        exact ⟨_, .single .cong_2, .refl⟩
    case cong_3 =>
      match hr with
      | (.point 0 hn hr) =>
        exact ⟨_, .single .cong_3, .refl⟩
      | (.point 1 hn hr) =>
        exact ⟨_, .single .cong_3, .refl⟩
    case cong_4 =>
      match hr with
      | (.point 1 hn hr) =>
        exact ⟨_, .single .cong_4, .refl⟩
      | (.point 0 hn hr) =>
        exact ⟨_, .single .cong_4, .refl⟩
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
      | .congrArg hr => exact ⟨_, .single .eql, .single (.point 0 (by grind) (.congrArg hr))⟩
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
    case sigma =>
      match hr with
      | .point 0 hn hr => exact ⟨_, .single (by constructor), .refl⟩
      | .point 1 hn hr => exact ⟨_, .single (by constructor), .single (.point 0 (by grind) hr.congrFun)⟩
    case congrFun hr₂ =>
      have ⟨_, ha, hb⟩ := ih hr₂
      exact ⟨_, congrFun' ha, congrFun' hb⟩
    case congrArg hr => exact ⟨_, .single (.congrArg (by assumption)), .single (.congrFun (by assumption))⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance RedAff.instConf : Confluent (RedAff (τ := τ)) := ⟨RedAff.conf⟩

theorem red_aff_globally_conf {A B C : GenericExpr τ} : Relation.ReflTransGen (RedAff (τ := τ)) A B → Relation.ReflTransGen RedAff A C → ∃ D,
  Relation.ReflTransGen RedAff B D ∧ Relation.ReflTransGen RedAff C D :=
  RedAff.instRedRel.globally_confluent.conf

#check Relation.ReflTransGen.head_induction_on

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance instConfRedAffTrans : Confluent (RedAff (τ := τ)) (m := Relation.ReflTransGen) := RedAff.instRedRel.globally_confluent

end GenericExpr
