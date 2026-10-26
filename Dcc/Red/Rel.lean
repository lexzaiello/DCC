import Dcc.Attrs
import Dcc.Ast
import Dcc.Red.Size
import Dcc.Red.RelationProp
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.IntervalCases

namespace Expr

open Dsl

@[aesop safe (rule_sets := [DccForceStep]) [constructors], aesop unsafe 50% (rule_sets := [DccForceStep]) [cases]]
inductive Red : Expr → Expr → Prop
/-
Core reductions:
-/
  | dup            : Red (DCC? ((Dup B x) (& env) (& y))) (DCC? (x env (,(`(B env) (B env)) y y)))
  | bimap          : Red (DCC? ((Map A B f g) (,_B x y))) (DCC? (,(`A B) (f x) (g y)))
  | assoc          : Red (DCC? ((Assoc A B C) (,_B₁ (,_B₂ x y) z))) (DCC? (,(`A (Σ B (`B C))) x (,(`B C) y z)))
  | eql            : Red (DCC ((Eql B) (& x) (& y))) (DCC (= (B x) y y))
  | eq_mk          : Red (DCC ((=' B) x y z)) (DCC (= (B x) y z))
  | map            : Red (DCC? ((!<> f) (& x))) (DCC? (!(f x)))
  | fmap           : Red (DCC? (($<> f) (& x))) (DCC? (& (f x)))
  | unbox          : Red (DCC? ((* A) (& x))) x
  | pair           : Red (DCC? ((⟨,⟩β M N) (& x))) (DCC? (,(β x) (M x) (N x (M x))))
  | evalc          : Red (DCC? ((Eval _α _β x) (,__β y z))) (DCC? (x y z))
  | quot           : Red (DCC? ((`β x) y)) x
  | id             : Red (DCC? ((Id α) x)) x
  | fstc           : Red (DCC? ((Fst _β) (,β a b))) a
  | sndc           : Red (DCC? ((Snd _β) (,β a b))) b
  | comp           : Red (DCC? ((∘ x y) z)) (DCC? (x (y z)))
  | curr           : Red (DCC? ((Λ α β x) y z)) (DCC? (x (,β y z)))
  | curr'          : Red (DCC? ((!Λα β x) (& y) (& z))) (DCC? (x (& (,β y z))))
  | swap           : Red (DCC? ((Swap A B) (,B₂ x y))) (DCC? (,(`B A) y x))
  | ind_bool_true  : Red (DCC? ((𝟚.Rec motive x y) env 𝟙₂)) (DCC? (x env 𝟙₂))
  | ind_bool_false : Red (DCC? ((𝟚.Rec motive x y) env 𝟘₂)) (DCC? (y env 𝟘₂))
  | sigma          : Red (DCC? ((Σ' B C) (& x))) (DCC (Σ (B x) (C x)))
/-
Inner congruences:
-/
-- `(B, x)
  | point : (n : ℕ) → (h : n < point_arity e) → Red ((points e).get ⟨n, h⟩) p' → Red e (e.set_points ((points e).set n p'))
/-
App congruence:
-/
  | congrFun : Red f f' → Red (DCC? (f x)) (DCC? (f' x))
  | congrArg : Red x x' → Red (DCC? (f x)) (DCC? (f x'))

instance (A B : Expr) : Repr (PLift (Red A B)) := ⟨fun _ _ => "⋯"⟩

theorem Red.mkCongrFun (h : Red f f') : Red (DCC? (f x)) (DCC? (f' x)) := .congrFun h
theorem Red.mkCongArg (h : Red x x') : Red (DCC? (f x)) (DCC? (f x')) := .congrArg h

@[aesop safe forward (rule_sets := [DccForceReduce])]
theorem Red.elim_point₁ {A B : Expr} (hr : Red A B) (h_arr : point_arity A = 1 := by rfl) : ∃ p', B = (A.set_points (A.points.set 0 p')) ∧ Red A.points[0] p' := by
  unfold point_arity at h_arr
  split at h_arr
  any_goals (simp at h_arr)
  any_goals (
    expose_names
    dcc_simp
    cases hr
    simp at h_arr_1
    expose_names
    simp [point_arity] at h
    cases h
    dcc_simp
    assumption)

theorem Red.mk_point {x y e : Expr} (n : Fin (point_arity e) := by exact ⟨0, by grind⟩) (hr : Red x y := by assumption) (heq : (points e)[n] = x := by first | grind | (dcc_simp; rfl)) : Red e (e.set_points ((points e).set n y)) := .point n (by grind) (by
  cases heq
  exact hr)

theorem Red.instCongruent'_mp {e : Expr} {p : Fin (point_arity e)} (h : Red (points e)[p] p') : Red e (set_points e ((points e).set p p')) :=
  .point (↑ p) (by grind) h

instance Red.instCongruent : Congruent Red where
  pil_ := fun h => .point 0 (by simp [point_arity]) h
  pir_ := fun h => .point 1 (by simp [point_arity]) h
  sigl_ := fun h => .point 1 (by simp [point_arity]) h
  sigr_ := fun h => .point 2 (by simp [point_arity]) h

theorem point_trans (_hr : Red ((points e).get ⟨n, h⟩) p') (hr' : Red p' w) : Red ((points ((e.set_points ((points e).set n p')))).get ⟨n, by
  have h := congr_point_arr (e := e) (p := ⟨n, h⟩) (p' := p')
  grind⟩) w := by
  have h := get_set_point (e := e) (p := ⟨n, h⟩) (p' := p')
  simp [h]
  assumption

theorem point_trans' (_hr : Red ((points e).get ⟨n, h⟩) p') (hr' : Relation.ReflTransGen Red p' w) : Relation.ReflTransGen Red ((points ((e.set_points ((points e).set n p')))).get ⟨n, by
  have h := congr_point_arr (e := e) (p := ⟨n, h⟩) (p' := p')
  grind⟩) w := by
  have h := get_set_point (e := e) (p := ⟨n, h⟩) (p' := p')
  simp [h]
  assumption

/-theorem mk_point₂ (hr₁ : Red x x') (hr₂ : Red y y') (heq : points e = ⟨#[x, y], h_ar⟩) : Relation.ReflTransGen Red e (e.set_points ⟨#[x', y'], by grind⟩) := by
  have h₁' := Red.point 0 (by grind) (e := e) (by
    simp [heq, Vector.get]
    exact hr₁)
  have h := congr_point_arr (e := e) (p := ⟨0, by grind⟩) (p' := x')
  have h₂' := Red.point 1 (by grind) (e := (e.set_points (e.points.set 0 x' (by grind)))) (by
    simp [points, set_points, Vector.get]
    exact hr₁)
  refine Relation.ReflTransGen.trans (.single h₁') (.single ?_)
  simp [heq]
  rw [set_points_eq_set_points₂]-/

@[aesop safe apply (rule_sets := [DccForceReduce])]
theorem refl_conf : ∃ B, Relation.ReflTransGen r A B ∧ Relation.ReflTransGen r A B := ⟨_, .refl, .refl⟩

@[aesop safe apply (rule_sets := [DccReduce])]
theorem congrFun_of_single (h : Red x x' := by assumption) : Relation.ReflTransGen Red (DCC? (x y)) (DCC? (x' y)) := .single (.congrFun h)

@[aesop safe apply (rule_sets := [DccReduce])]
theorem congrArg_of_single (h : Red y y' := by assumption) : Relation.ReflTransGen Red (DCC? (x y)) (DCC? (x y')) := .single (.congrArg h)

attribute [aesop safe (rule_sets := [DccForceReduce]) [constructors]] Relation.ReflTransGen

end Expr


