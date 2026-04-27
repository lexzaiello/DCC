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

open Rel in class Complete.{u} (r : α → β → Sort u) (m : Type u → Type u := Id) [hM : Monad m]
  [hR : Rel (fun x y => PULift.{u + 1, u} (r x y)) (m := m)] where
  complete : ∀ (h : r x y), hR.run x = hM.pure ⟨y, PULift.up h⟩

open Rel in class Measure (r : Expr → ℕ → Prop)
  extends Rel (fun x n => PULift.{1, 0} (r x n)), Complete r where
  complete := by
    intro x y h
    induction h
    all_goals (
      simp_all [pure, id_pure_ext]
      try rfl
      try grind
    )

class RedRel (r : Expr → Expr → Prop) (t : Expr → ℕ → Prop)
  (m : Type → Type := Option) [_hM : Monad m]
  [hM : Measure t] extends Rel (fun x y => PLift (r x y)) (m := m) where
  decreasing : r x y → (hM.run y).fst < (hM.run x).fst := by
    intro x y h
    induction h
    all_goals (
      try dsimp
      try simp_all
      try grind
      try aesop
      try rfl)

def RedRel.IsNorm {r : Expr → Expr → Prop} {t : Expr → ℕ → Prop} {m : Type → Type}
  [Measure t] [Monad m] (_hR : RedRel r t (m := m)) (e : Expr) : Prop :=
  ¬ ∃ e', r e e'

theorem RedRel.IsNorm.complete {r : Expr → Expr → Prop}
  {t : Expr → ℕ → Prop}
  [hM : Measure t] [hR : RedRel r t (m := Option)] (h_norm : hR.IsNorm A) : (hR.run A) = .none := by
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

def RedRel.reduce {t : Expr → ℕ → Prop} [hT : Measure t] (hR : RedRel r t (hM := hT))
  (e : Expr) : ((e' : Expr) × (PLift (Relation.ReflTransGen r e e'))) :=
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

open RedRel in def RedRel.to_reflTrans {t : Expr → ℕ → Prop} [hT : Measure t] (hR : RedRel r t) : Rel (fun x y => PLift (Relation.ReflTransGen r x y)) where
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

open Rel in class Confluent (r : α → α → Prop) where
  conf : (r A B) → (r A C) → ∃ D, Relation.ReflTransGen r B D ∧ Relation.ReflTransGen r C D

open Rel in class Confluent.Global (r : α → α → Prop) where
  conf : (Relation.ReflTransGen r A B) → (Relation.ReflTransGen r A C)
    → ∃ D, Relation.ReflTransGen r B D ∧ Relation.ReflTransGen r C D

open Confluent in def RedRel.globally_confluent
  {r : Expr → Expr → Prop} {t : Expr → ℕ → Prop} {m : Type → Type}
  [Measure t] [Monad m] [Confluent r]
  (hR : RedRel r t (m := m)) : Confluent.Global r where
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
        have ⟨D, hrt₁b, hrt₂b⟩ := conf hr₁ hr₂
        have ⟨_, hrtt₁, hrtt₁b⟩ := ih _ hr₁ hrt₁ hrt₁b
        have ⟨_, hrtt₂, hrtt₂b⟩ := ih _ hr₂ hrt₂ hrt₂b
        have ⟨_, h₁, h₂⟩ := ih _ hr₁ (hrt₁b.trans hrtt₁b) (hrt₁b.trans hrtt₂b)
        exact ⟨_, .trans hrtt₁ h₁, .trans hrtt₂ h₂⟩

/-
Confluence diamond proofs

are essentially this constructor repeated a bunch of times:

| subst₁ =>
  cases h₂ with
  | subst₁ => exact ⟨_, .refl, .refl⟩
  | congrFun h => cases h with
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .congrFun (.congrArg (.single h)), .single .subst₁⟩
  | congrArg h => cases h with
    | sigl h => exact ⟨_, .congrArg (.single h), .single .subst₁⟩
    | sigr h => exact ⟨_, .refl, .single .subst₁⟩

(Relation.ReflTransGen r A B) → (Relation.ReflTransGen r A C)
    → ∃ D, Relation.ReflTransGen r B D ∧ Relation.ReflTransGen r C D


-/

theorem RedRel.norm_sound {r : Expr → Expr → Prop}
  {t : Expr → ℕ → Prop}
  [hM : Measure t] [hR : RedRel r t (m := Option)] (heq : hR.run A = .none) : hR.IsNorm A := by
  intro ⟨e', hr⟩
  have h := hR.decreasing hr
  
  sorry

end Expr
