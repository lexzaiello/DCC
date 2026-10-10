import Dcc.Attrs
import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Size
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

namespace GenericExpr

open Dsl

universe u
variable {τ : Type u} [DecidableEq τ]

/-
(Map τ₁ τ₂ M N) (,B x y) = (,(`τ₁ τ₂) (M x) (N y))


------------------------------------------------------
(Assoc A B C) →ᵦ (,_B (,_C x y) z) (,(`A (Σ (`B C))) x (,(`B C) y z))

(,_B (,__B (,___B ((≃.mk A₁_to_A₂ A₂_to_A₁ eq₁ eq₂) env)
                  ((≃.mk cod₁_to_cod₂ cod₂_to_cod₁ eq₃ eq₄) env₂))
            f)
      x) →ᵦ
(,_B (,___B ((≃.mk A₁_to_A₂ A₂_to_A₁ eq₁ eq₂) env)
            ((≃.mk cod₁_to_cod₂ cod₂_to_cod₁ eq₃ eq₄) env₂))
     (,? f x)) →ᵦ
(, (, A₂_to_A₂ cod₁_to_cod₂)
   (, f x)) →ᵦ should (, (, A₂_to_A₂ cod₁_to_cod₂) (, f x))

≃.1.apply = (∘ (∘ (∘ (Map (((C₁ x₁ hole) : (? (C₁ x₁ hole))) → (C₂ x₂ hole))
                          ?
                          (Id (((C₁ x₁ hole) : (? (C₁ x₁ hole))) → (C₂ x₂ hole)))
                          (∘ (∘ (Map ((((Π B₁ C₁) x₁) : Sort u) → ((Π B₁ C₁) x₁))
                                     (B₁ x₁ hole)
                                     (Id ((Π B₁ C₁) x₁))
                                     (∘ (Eval (((B₁ x₁) : (? (B₁ x₁))) → (B₂ x₂))
                                              (`(((B₁ x₁) : (? (B₁ x₁))) → (B₂ x₂)) (B₁ x₁))
                                              (Id (((B₁ x₁) : (? (B₁ x₁))) → (B₂ x₂))))
                                        (Swap (B₁ x₁) (((B₁ x₁) : (? (B₁ x₁))) → (B₂ x₂))))) -- (, (, f x) A₂_to_A₂) →ᵦ f (A₂_to_A₂ x)
                                (Assoc ((Π B₁ C₁) x₁) (B₂ x₂) (((B₁ x₁) : (? (B₁ x₁))) → (B₂ x₂)))) -- (, (, f x) A₂_to_A₂)) →ᵦ (, f (,x A₂_to_A₂))
                             (Swap (((B₁ x₁) : (? (B₁ x₁))) → (B₂ x₂)) (B₂ x₂)))) -- (, cod₁_to_cod₂ (, A₂_to_A₂ (, f x)))
                     (Assoc ? ? ?) -- (, (, cod₁_to_cod₂ A₂_to_A₂) (, f x))
                  (Map ?
                       ?
                       (Swap (((B₁ x₁) : (? (B₁ x₁))) → (B₂ x₂)) (((C₁ x₁ hole) : (? (C₁ x₁ hole))) → (C₂ x₂ hole)))
                       (Id (× ((Π B₁ C₁) x₁) (B₂ x₂)))) -- (, (, A₂_to_A₂ cod₁_to_cod₂) (, f x))
               (∘ (Map ?
                       ?
                       (Map ?
                            ?
                            (≃.1 (B₁ x₁) (B₂ x₂))
                            (≃.4 (C₁ x₁ hole) (C₂ x₂ hole)))
                       (Id (× ((Π B₁ C₁) x₁) (B₂ x₁))))
                  (Assoc ? ? ?))
-/

--abbrev unif_fn (u v : Level) (B₁ C₁ x₁ B₂ C₂ x₂ : GenericExpr τ) : GenericExpr τ :=
  /-let t_out            := (TUnif u v (DCC? ((Π B₁ C₁) x₁)) (DCC? ((Π B₂ C₂) x₂)))
  let bool_ind_motive  := (DCC? (`⊤ (`Bool t_out)))
  let t_cod_eq         := (DCC? (C₁ x₁) ≃ (C₂ x₂))
  (DCC? (((Bool.Ind bool_ind_motive
                    (≃.mk (Λ t_cod_eq
                              (`t_cod_eq ((Π B₁ C₁) x₁))
                              (-- (h₁ : (C₁ x₁) ≃ (C₂ x₂), f : ((Π B₁ c₁) x₁)), prove ((Π B₂ C₂) x₂), so also x : (B₂ x₂)
                              (Λ (Σ (`t_cod_eq ((Π B₁ C₁) x₁)))
                                 (`(Σ (`t_cod_eq ((Π B₁ C₁) x₁))) (B₂ x₂))
                                 (-- ((h₁ : (C₁ x₁) ≃ (C₂ x₂), f : ((Π B₁ c₁) x₁)), x : (B₂ x₂)), so 
                                 ))
                              ))
                           ()
                           ()
                           ())  -- (C₁ x₁) ≃ (C₂ x₂), prove ((Π B₁ C₁) x₁) ≃ ((Π B₂ C₂) x₂)
                    ()
                    ())
           ∗
           (Unify (? 1) (? 2) (C₁ x₁) (C₂ x₂))))-/
/-abbrev unif_fn (u v : Level) (B₁ C₁ x₁ B₂ C₂ x₂ : GenericExpr τ) : GenericExpr τ :=
  let t_out            := (TUnif u v (DCC? ((Π B₁ C₁) x₁)) (DCC? ((Π B₂ C₂) x₂)))
  let t_out_false      := DCC? (((Π B₁ C₁) x₁) ≃ ((Π B₂ C₂) x₂)) ≃ ⊥
  let t_out_false_fst  := DCC? (((Π B₁ C₁) x₁) ≃ ((Π B₂ C₂) x₂))
  let bool_ind_motive  := (DCC? (`⊤ (`Bool t_out)))
  let t_eq_fst_true    := (DCC? ((B₁ x₁) ≃ (B₂ x₂)))
  let t_eq_fst_false   := (DCC? ((B₁ x₁) ≃ (B₂ x₂)) ≃ ⊥)
  let with_B₁x₁_eq_B₂x₂ (e : GenericExpr τ) : GenericExpr τ :=
    (DCC? (((Bool.Ind bool_ind_motive
                     (`⊤ e) -- (B₁ x₁) ≃ (B₂ x₂), ((Π B₁ C₁) x₁), (B₂ x₂)
                     (∘ ((Λ Bool (`Bool t_out_false) (Id (Σ (`Bool t_out_false)))) False)
                        (≃.mk (`t_eq_fst_false t_out_false_fst)
                               (`t_eq_fs_falset ⊥)
                               (Λ t_eq_fst_false
                                  (`t_eq_fst_false t_out_false_fst)
                                  (∘ () (Fst (`t_eq_fst_false t_out_false_fst)))) -- (DCC? ((B₁ x₁) ≃ (B₂ x₂)) ≃ ⊥), (((Π B₁ C₁) x₁) ≃ ((Π B₂ C₂) x₂)), prove ⊥
                               ())))) -- ((B₁ x₁) ≃ (B₂ x₂)) ≃ ⊥, prove (((Π B₁ C₁) x₁) ≃ ((Π B₂ C₂) x₂)) ≃ ⊥
                     -- ^ this is equivalent to showing (B₁ x₁) is inhabited
                     -- but since (((Π B₁ C₁) x₁) ≃ ((Π B₂ C₂) x₂)), then ((B₁ x₁) ≃ (B₂ x₂))
                     -- which should be solvable with reflexivity
           (Unify (Dom (C₁ x₁)) (Dom (C₂ x₂)) (B₁ x₁) (B₂ x₂))) ∗))
  with_B₁x₁_eq_B₂x₂ (by sorry)-/

/-
Preservation proof:
- can make these more type-directed

Id(A) ∘ Fst(Id(A))

Fst(B) ∘ Id(Coup(Id(A)))
-/

/-
Funext:

-/

@[aesop safe (rule_sets := [DccForceStep]) [constructors], aesop unsafe 50% (rule_sets := [DccForceStep]) [cases]]
inductive RedAff : GenericExpr τ → GenericExpr τ → Prop
/-
Core reductions:
-/
  | dup            : RedAff (DCC? ((Dup B x) (& env) (& y))) (DCC? (x env (,(`(B env) (B env)) y y)))
  | bimap          : RedAff (DCC? ((Map A B f g) (,_B x y))) (DCC? (,(`A B) (f x) (g y)))
  | assoc          : RedAff (DCC? ((Assoc A B C) (,_B₁ (,_B₂ x y) z))) (DCC? (,(`A ((Σ (`⊤ B) (`⊤ (`B C))) ∗)) x (,(`B C) y z)))
  | eql            : RedAff (DCC? ((Eql f_α) env (,B x y))) (DCC? (= (f_α env) x y))
  | map            : RedAff (DCC? ((!<> f) (& x))) (DCC? (!(f x)))
  | fmap           : RedAff (DCC? (($<> f) (& x))) (DCC? (& (f x)))
  | unbox          : RedAff (DCC? ((* A) (& x))) x
  | pair           : RedAff (DCC? ((⟨,⟩β M N) (& x))) (DCC? (,(β x) (M x) (N x (M x))))
  | evalc          : RedAff (DCC? ((Eval _α _β x) (,__β y z))) (DCC? (x y z))
  | quot           : RedAff (DCC? ((`β x) y)) x
  | id             : RedAff (DCC? ((Id α) x)) x
  | fstc           : RedAff (DCC? ((Fst _β) (,β a b))) a
  | sndc           : RedAff (DCC? ((Snd _β) (,β a b))) b
  | comp           : RedAff (DCC? ((∘ x y) z)) (DCC? (x (y z)))
  | curr           : RedAff (DCC? ((Λ α β x) y z)) (DCC? (x (,β y z)))
  | curr'          : RedAff (DCC? ((!Λα β x) (& y) (& z))) (DCC? (x (& (,β y z))))
  | swap           : RedAff (DCC? ((Swap A B) (,B₂ x y))) (DCC? (,(`B A) y x))
  | ind_bool_true  : RedAff (DCC? ((Bool.Rec motive x y) env True)) (DCC? (x env True))
  | ind_bool_false : RedAff (DCC? ((Bool.Rec motive x y) env False)) (DCC? (y env False))
/-
Inner congruences:
-/
-- `(B, x)
  | point : (n : ℕ) → (h : n < point_arity e) → RedAff ((points e).get ⟨n, h⟩) p' → RedAff e (e.set_points ((points e).set n p'))
/-
App congruence:
-/
  | congrFun : RedAff f f' → RedAff (DCC? (f x)) (DCC? (f' x))
  | congrArg : RedAff x x' → RedAff (DCC? (f x)) (DCC? (f x'))


instance (A B : GenericExpr τ) : Repr (PLift (RedAff A B)) := ⟨fun _ _ => "⋯"⟩

theorem RedAff.mkCongrFun (h : RedAff f f') : RedAff (DCC? (f x)) (DCC? (f' x)) := .congrFun h
theorem RedAff.mkCongArg (h : RedAff x x') : RedAff (DCC? (f x)) (DCC? (f x')) := .congrArg h

@[aesop safe forward (rule_sets := [DccForceReduce])]
theorem RedAff.elim_point₁ {A B : GenericExpr τ_c} (hr : RedAff A B) (h_arr : point_arity A = 1 := by rfl) : ∃ p', B = (A.set_points (A.points.set 0 p')) ∧ RedAff A.points[0] p' := by
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

theorem RedAff.mk_point {x y e : GenericExpr τ_c} (n : Fin (point_arity e) := by exact ⟨0, by grind⟩) (hr : RedAff x y := by assumption) (heq : (points e)[n] = x := by first | grind | (dcc_simp; rfl)) : RedAff e (e.set_points ((points e).set n y)) := .point n (by grind) (by
  cases heq
  exact hr)

theorem RedAff.instCongruent'_mp {e : GenericExpr τ_c} {p : Fin (point_arity e)} (h : RedAff (points e)[p] p') : RedAff e (set_points e ((points e).set p p')) :=
  .point (↑ p) (by grind) h

instance RedAff.instCongruent : Congruent (RedAff (τ := τ)) where
  pil_ := fun h => .point 0 (by simp [point_arity]) h
  pir_ := fun h => .point 1 (by simp [point_arity]) h
  sigl_ := fun h => .point 1 (by simp [point_arity]) h
  sigr_ := fun h => .point 2 (by simp [point_arity]) h

theorem point_trans (_hr : RedAff (τ := τ_c) ((points e).get ⟨n, h⟩) p') (hr' : RedAff p' w) : RedAff ((points ((e.set_points ((points e).set n p')))).get ⟨n, by
  have h := congr_point_arr (e := e) (p := ⟨n, h⟩) (p' := p')
  grind⟩) w := by
  have h := get_set_point (e := e) (p := ⟨n, h⟩) (p' := p')
  simp [h]
  assumption

theorem point_trans' (_hr : RedAff (τ := τ_c) ((points e).get ⟨n, h⟩) p') (hr' : Relation.ReflTransGen RedAff p' w) : Relation.ReflTransGen RedAff ((points ((e.set_points ((points e).set n p')))).get ⟨n, by
  have h := congr_point_arr (e := e) (p := ⟨n, h⟩) (p' := p')
  grind⟩) w := by
  have h := get_set_point (e := e) (p := ⟨n, h⟩) (p' := p')
  simp [h]
  assumption

/-theorem mk_point₂ (hr₁ : RedAff x x') (hr₂ : RedAff y y') (heq : points e = ⟨#[x, y], h_ar⟩) : Relation.ReflTransGen RedAff e (e.set_points ⟨#[x', y'], by grind⟩) := by
  have h₁' := RedAff.point 0 (by grind) (e := e) (by
    simp [heq, Vector.get]
    exact hr₁)
  have h := congr_point_arr (e := e) (p := ⟨0, by grind⟩) (p' := x')
  have h₂' := RedAff.point 1 (by grind) (e := (e.set_points (e.points.set 0 x' (by grind)))) (by
    simp [points, set_points, Vector.get]
    exact hr₁)
  refine Relation.ReflTransGen.trans (.single h₁') (.single ?_)
  simp [heq]
  rw [set_points_eq_set_points₂]-/

@[aesop safe apply (rule_sets := [DccForceReduce])]
theorem refl_conf : ∃ B, Relation.ReflTransGen r A B ∧ Relation.ReflTransGen r A B := ⟨_, .refl, .refl⟩

@[aesop safe apply (rule_sets := [DccReduce])]
theorem congrFun_of_single (h : RedAff x x' := by assumption) : Relation.ReflTransGen RedAff (DCC? (x y)) (DCC? (x' y)) := .single (.congrFun h)

@[aesop safe apply (rule_sets := [DccReduce])]
theorem congrArg_of_single (h : RedAff y y' := by assumption) : Relation.ReflTransGen RedAff (DCC? (x y)) (DCC? (x y')) := .single (.congrArg h)

attribute [aesop safe (rule_sets := [DccForceReduce]) [constructors]] Relation.ReflTransGen

end GenericExpr

abbrev Expr.RedAff := GenericExpr.RedAff (τ := Unit)
