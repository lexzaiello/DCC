import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Dcc.Ast
import Qq
import Lean
import Lean.Elab
import Mathlib.Tactic.CasesM

namespace Expr

@[simp] theorem id_pure_ext {α : Type u} (x : α) : (pure x : Id α) = x := rfl

class Rel.{u} (r : α → β → Type u) (m : Type u → Type u := Id) [Monad m] where
  run (x : α) : m ((y : β) × r x y)
  sound       : run x = pure ⟨y, h⟩ → r x y := fun _ => h

def Rel.rel.{u} {r : α → β → Type u} {m : Type u → Type u} [Monad m] (_hR : Rel.{u} r (m := m)) : (α → β → Type u) := r

open Rel in class Complete.{u} (r : α → β → Sort u) (P : β → Prop := fun _ => True) (m : Type u → Type u := Id) [hM : Monad m]
  [hR : Rel (fun x y => PULift.{u + 1, u} (r x y)) (m := m)] where
  complete : ∀ (h : r x y) (_p : P y), hR.run x = hM.pure ⟨y, PULift.up h⟩

open Rel in class Measure (r : Expr → ℕ → Prop)
  extends Rel (fun x n => PULift.{1, 0} (r x n)), Complete r where
  complete := by
    intro x y h _h
    induction h
    all_goals (
      simp_all [pure, id_pure_ext]
      try rfl
      try grind
    )

abbrev Measure.size {r : Expr → ℕ → Prop} [hM : Measure r] (e : Expr) : ℕ := (hM.run e).fst

class RedRel (r : Expr → Expr → Prop) (t : Expr → ℕ → Prop)
  (m : Type → Type := Option) [_hM : Monad m]
  [hM : Measure t] extends Rel (fun x y => PULift.{1, 0} (r x y)) (m := m) where
  decreasing : r x y → (hM.run y).fst < (hM.run x).fst := by
    intro x y h
    induction h
    all_goals (
      try dsimp
      try simp_all
      try grind
      try aesop
      try rfl)

def IsNorm (r : Expr → Expr → Prop) (A : Expr) := ¬ ∃ B, r A B

def IsNorm.unique {r : Expr → Expr → Prop} (hn : IsNorm r A) (hr : r A B) : A = B :=
  (hn ⟨_, hr⟩).elim

def IsNorm.unique_trans {r : Expr → Expr → Prop} (hn : IsNorm r A) (hr : (Relation.TransGen r) A B) : A = B :=
  match hr with
  | .single h => hn.unique h
  | .tail hrt hr => hn.unique ((hn.unique_trans hrt) ▸ hr)

def IsNorm.unique_refl {r : Expr → Expr → Prop} (hn : IsNorm r A) (hr : (Relation.ReflTransGen r) A B) : A = B := by
  rw [← Relation.reflGen_transGen] at hr
  cases hr with
  | refl => rfl
  | single h => exact hn.unique_trans h

theorem RedRel.norm_complete {r : Expr → Expr → Prop}
  {t : Expr → ℕ → Prop}
  [hM : Measure t] [hR : RedRel r t (m := Option)] (h_norm : IsNorm r A) : (hR.run A) = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨e', ⟨h₂⟩⟩ heq
  exact (h_norm ⟨_, h₂⟩)

def RedRel.sn {r : Expr → Expr → Prop} {t : Expr → ℕ → Prop}
  {m : Type → Type} [Monad m] [hM : Measure t]
  (hR : RedRel r t (m := m)) (e : Expr) : Acc (fun b a => r a b) e := Acc.intro e (fun e' hr => by
    have h := hR.decreasing hr
    exact sn hR e')
termination_by (hM.run e).fst

def RedRel.wellFounded {r : Expr → Expr → Prop} {t : Expr → ℕ → Prop}
  {m : Type → Type} [Monad m] [hM : Measure t]
  (hR : RedRel r t (m := m)) : WellFounded (fun a b => r b a) := ⟨hR.sn⟩

@[simp] def RedRel.reduce {t : Expr → ℕ → Prop} [hT : Measure t] (hR : RedRel r t (hM := hT))
  (e : Expr) : ((e' : Expr) × (PULift.{1, 0} (Relation.ReflTransGen r e e'))) :=
  match hR.run e with
  | .some ⟨e', ⟨h⟩⟩ =>
    have _size_ : (hT.run e').fst < (hT.run e).fst := hR.decreasing h
    let ⟨e'', ⟨h₂⟩⟩ := hR.reduce (r := r) (t := t) e'
    ⟨e'', ⟨.trans (.single h) h₂⟩⟩
  | .none => ⟨e, ⟨.refl⟩⟩
termination_by (hT.run e).fst

open RedRel in def RedRel.to_trans {t : Expr → ℕ → Prop} [hT : Measure t] (hR : RedRel r t) : RedRel (Relation.TransGen r) t where
  decreasing := fun h => by
    induction h with
    | single h =>
      exact hR.decreasing h
    | tail h₁ hr ih =>
      have h := hR.decreasing hr
      grind
  -- reducer given decreasing
  run (e : Expr) :=
    let ⟨e', ⟨h⟩⟩ := reduce e (hR := hR)
    if heq : e = e' then
      .none
    else
      .some ⟨e', ⟨by
        rw [← Relation.reflGen_transGen] at h
        cases h with
        | refl => simp_all
        | single h => exact h⟩⟩

open RedRel in def RedRel.to_reflTrans {t : Expr → ℕ → Prop} [hT : Measure t] (hR : RedRel r t) : Rel (fun x y => PULift.{1, 0} (Relation.ReflTransGen r x y)) where
  run := hR.reduce

abbrev RedRel.ReflTrans {t : Expr → ℕ → Prop} [Measure t] {m : Type → Type} [Monad m] (_hR : RedRel r t (m := m)) := Relation.ReflTransGen r
abbrev RedRel.Trans {t : Expr → ℕ → Prop} [Measure t] {m : Type → Type} [Monad m] (_hR : RedRel r t (m := m))     := Relation.TransGen r

open Rel in class Congruent (r : Expr → Expr → Prop) where
  congrFun_ (h : r f f') : r (DCC (f x)) (DCC (f' x)) := by exact .congrFun
  congrArg_ (h : r x x') : r (DCC (f x)) (DCC (f x')) := by exact .congrArg
  sigl_     (h : r x x') : r (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x', y)) := by exact .sigl
  sigr_     (h : r y y') : r (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x, y')) := by exact .sigr

theorem Congruent.congrFun' {r : Expr → Expr → Prop} [hR : Congruent r] (h : r f f') : r (DCC (f x)) (DCC (f' x)) :=
  (hR.congrFun_ h)

theorem Congruent.congrArg' {r : Expr → Expr → Prop} [hR : Congruent r] (h : r x x') : r (DCC (f x)) (DCC (f x')) :=
  (hR.congrArg_ h)

theorem Congruent.sigl' {r : Expr → Expr → Prop} [hR : Congruent r] (h : r x x') : r (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x', y)) :=
  (hR.sigl_ h)

theorem Congruent.sigr' {r : Expr → Expr → Prop} [hR : Congruent r] (h : r y y') : r (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x, y')) :=
  (hR.sigr_ h)

instance Congruent.trans {r : Expr → Expr → Prop} [hC : Congruent r] : Congruent (Relation.TransGen r) where
  congrFun_ h := by
    induction h with
    | single h => exact .single (hC.congrFun' h)
    | tail => exact .trans (by assumption) (.single (hC.congrFun' (by assumption)))
  congrArg_ h := by
    induction h with
    | single h => exact .single (hC.congrArg' h)
    | tail => exact .trans (by assumption) (.single (hC.congrArg' (by assumption)))
  sigl_ h := by
    induction h with
    | single h => exact .single (hC.sigl' h)
    | tail => exact .trans (by assumption) (.single (hC.sigl' (by assumption)))
  sigr_ h := by
    induction h with
    | single h => exact .single (hC.sigr' h)
    | tail => exact .trans (by assumption) (.single (hC.sigr' (by assumption)))

instance Congruent.reflTrans {r : Expr → Expr → Prop} [hC : Congruent r] : Congruent (Relation.ReflTransGen r) where
  congrFun_ h := by
    rw [← Relation.reflGen_transGen] at *
    cases h with
    | single h => exact .single (hC.trans.congrFun' h)
    | refl => exact .refl
  congrArg_ h := by
    rw [← Relation.reflGen_transGen] at *
    cases h with
    | single h => exact .single (hC.trans.congrArg' h)
    | refl => exact .refl
  sigl_ h := by
    rw [← Relation.reflGen_transGen] at *
    cases h with
    | single h => exact .single (hC.trans.sigl' h)
    | refl => exact .refl
  sigr_ h := by
    rw [← Relation.reflGen_transGen] at *
    cases h with
    | single h => exact .single (hC.trans.sigr' h)
    | refl => exact .refl

syntax "some_congr" : tactic

macro_rules
  | `(tactic| some_congr) => `(tactic| (
    first
    | exact Congruent.congrFun' (by assumption)
    | exact Congruent.congrFun' (.single (by assumption))
    | exact Congruent.congrArg' (by assumption)
    | exact Congruent.congrArg' (.single (by assumption))
    | exact Congruent.sigl' (by assumption)
    | exact Congruent.sigl' (.single (by assumption))
    | exact Congruent.sigr' (by assumption)
    | exact Congruent.sigr' (.single (by assumption))))


open Rel in class Confluent (r : α → α → Prop) (m : (α → α → Prop) → α → α → Prop := fun p => p) where
  conf : (m r A B) → (m r A C) → ∃ D, Relation.ReflTransGen r B D ∧ Relation.ReflTransGen r C D

open Confluent in def RedRel.globally_confluent
  {r : Expr → Expr → Prop} {t : Expr → ℕ → Prop} {m : Type → Type}
  [Measure t] [Monad m] [hC : Confluent r]
  [hR : RedRel r t (m := m)] : (Confluent r (m := Relation.ReflTransGen)) where
  conf := fun {A B C} (h₁ : hR.ReflTrans A B) (h₂ : hR.ReflTrans A C) => by
    induction A using hR.wellFounded.induction generalizing B C with
    | h x ih =>
      match h₁.cases_head, h₂.cases_head with
      | .inl heq₁, .inl heq₂ =>
        exact ⟨x, heq₁ ▸ .refl, heq₂ ▸ .refl⟩
      | .inl heq₁, _ =>
        exact ⟨C, heq₁ ▸ h₂, .refl⟩
      | _, .inl heq₁ =>
        exact ⟨B, .refl, heq₁ ▸ h₁⟩
      | .inr ⟨C₁, hr₁, hrt₁⟩, .inr ⟨C₂, hr₂, hrt₂⟩ =>
        have ⟨D, hrt₁b, hrt₂b⟩ := hC.conf hr₁ hr₂
        have ⟨_, hrtt₁, hrtt₁b⟩ := ih _ hr₁ hrt₁ hrt₁b
        have ⟨_, hrtt₂, hrtt₂b⟩ := ih _ hr₂ hrt₂ hrt₂b
        have ⟨_, h₁, h₂⟩ := ih _ hr₁ (hrt₁b.trans hrtt₁b) (hrt₁b.trans hrtt₂b)
        exact ⟨_, .trans hrtt₁ h₁, .trans hrtt₂ h₂⟩

open Rel in class DecidableNorm (r : Expr → Expr → Prop)
  [hR : Rel (fun x y => PULift.{1, 0} (r x y)) (m := Option)] where
  norm_sound    : (hR.run A) = Option.none → IsNorm r A
  norm_complete : (IsNorm r A) → (hR.run A) = Option.none

class ExtRel (r : Expr → Expr → Prop) where
  ext (h₁ : r A B) (h₂ : r A B) : h₁ = h₂

open Confluent in theorem Confluent.norm_unique {r : Expr → Expr → Prop} {m : (Expr → Expr → Prop) → Expr → Expr → Prop}
  (hC : Confluent r m) (hn₁ : IsNorm r B) (h₁ : m r A B) (hn₂ : IsNorm r C) (h₂ : m r A C) : B = C := by
  have ⟨D, hr₁, hr₂⟩ := hC.conf h₁ h₂
  have ha := hn₁.unique_refl hr₁
  have hb := hn₂.unique_refl hr₂
  simp_all

/-
R a b → ∃ b' h, (run a) = .some ⟨b', ⟨h⟩⟩

If b is a normal form, then b' = b, since b' and b have a common reduct via Conf,
and if b ≠ b, then b also has a next reduct, but Norm b, so b' = b.
-/

open RedRel Measure DecidableNorm Confluent in theorem step_complete' {r : Expr → Expr → Prop} {t : Expr → ℕ → Prop}
  [hM : Measure t] (hR : RedRel r t (m := Option)) [hN : DecidableNorm r]
  {A B : Expr} (hr : r A B) : ∃ B' hr', hR.run A = .some ⟨B', ⟨hr'⟩⟩ := by
  -- if run is none, then A is a norma value, but it is not.
  match heq : hR.run A with
  | .some ⟨B', ⟨h⟩⟩ => exact ⟨B', h, rfl⟩
  | .none => exact (hN.norm_sound heq ⟨_, hr⟩).elim

/-
If A → B, and Norm B, and A → B₂, then the diamond B -*> C and B₂ -*> C can only be constructed by
C = B.

A diamond where one of the lower vertices which is not D is normal, then D = the normal vertex

Most of the arguments are unnecesary, but they help visualize.
-/
theorem triangle_collapse {r : Expr → Expr → Prop} {A B : Expr}
  (_hr₁ : r A B) (_hr₂ : r A C)
  (h_diamond : Relation.ReflTransGen r B D ∧ Relation.ReflTransGen r C D) (hn : IsNorm r C) : C = D :=
  have ⟨_ha, hb⟩ := h_diamond
  match hb.cases_head with
  | .inl heq => heq
  | .inr ⟨_c, hC, _hrt⟩ => (hn ⟨_, hC⟩).elim

theorem RedRel.reduce_norm {r : Expr → Expr → Prop} {t : Expr → ℕ → Prop}
  [Measure t] (hR : RedRel r t (m := Option))
  {A : Expr} (hn : IsNorm r A) : (hR.reduce A) = ⟨A, ⟨.refl⟩⟩ := by
  simp
  split
  case h_1 h _ =>
    exact (hn ⟨_, h⟩).elim
  case h_2 => congr

@[simp, aesop safe forward] theorem RedRel.reduce_norm_fst {r : Expr → Expr → Prop} {t : Expr → ℕ → Prop}
  [Measure t] (hR : RedRel r t (m := Option))
  {A : Expr} (hn : IsNorm r A) : (hR.reduce A).fst = A := by
  have h := hR.reduce_norm hn
  simp_all
/-
(RedRel R).reduce holds completeness because:

A -*> B
IsNorm B

by the definition of reduce,
if step? is some, then we get
A -> B'

then create a diamond

B -*> C
B' -*> C

since B is norm, B = C

hence, B' -*> B

case_head analysis on B' -*> B
if refl, trivial

if there is a step, do induction to show
reduce B' = B, then you're set.
-/
theorem RedRel.reduce_complete {r : Expr → Expr → Prop} {t : Expr → ℕ → Prop}
  [hM : Measure t] (hR : RedRel r t (m := Option)) [hN : DecidableNorm r] [Confluent r]
  {A B : Expr} (hr : Relation.ReflTransGen r A B) (hn : IsNorm r B) : (hR.reduce A) = ⟨B, ⟨hr⟩⟩ := by
  simp [RedRel.reduce]
  split
  -- hr is an actual step, not noop
  -- we get B', make a diamond with B to C, and show B = C since B IsNorm
  case h_1 B' hr₂ heq =>
    have ⟨C, h₁, h₂⟩ := hR.globally_confluent.conf hr (.single hr₂)
    have h_b_c_eq := hn.unique_refl h₁
    have hr_b'_b := h_b_c_eq ▸ h₂
    match hr_b'_b.cases_head with
    | .inl h =>
      have h_red_norm := hR.reduce_norm_fst hn
      cases h_b_c_eq; cases h
      congr
      repeat simp_all
    | .inr ⟨_, hrB', hrt⟩ =>
      rename_i w
      have h_dec : (hM.size B') < (hM.size A) := by
        have h₁ := hR.decreasing hr₂
        have h₂ := hR.decreasing hrB'
        grind
      have h := hR.reduce_complete (.trans (.single hrB') hrt) hn
      have h_fst : (hR.reduce B').fst = B := by
        simp_all
      cases h_fst
      congr
  case h_2 hneq =>
    have h_A_B_eq : A = B := by
      match hr.cases_head with
      | .inl h => exact h
      | .inr ⟨_, hr, hrt⟩ =>
        exact (hN.norm_sound hneq ⟨_, hr⟩).elim
    aesop
termination_by (hM.size A)

end Expr
