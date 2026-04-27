import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation
import Dcc.Ast

syntax "decreases_obvious" : tactic

macro_rules
  | `(tactic| decreases_obvious) => `(tactic| induction ‹_› <;> (simp_all; try grind))

class Rel.{u} (r : α → β → Type u) (m : Type u → Type u := Id) [Monad m] where
  run (x : α) : m ((y : β) × r x y)
  sound       : run x = pure ⟨y, h⟩ → r x y := fun _ => h

open Rel in class Complete.{u} (r : α → β → Sort u) (m : Type u → Type u := Id) [hM : Monad m]
  [hR : Rel (fun x y => PULift.{u + 1, u} (r x y)) (m := m)] where
  complete : ∀ (h : r x y), hR.run x = hM.pure ⟨y, PULift.up h⟩

class Measure (r : Expr → ℕ → Prop)
  extends Rel (fun x n => PULift.{1, 0} (r x n)), Complete r where

class RedRel (r : Expr → Expr → Prop) (t : Expr → ℕ → Prop)
  (m : Type → Type := Option) [Monad m]
  [hM : Measure t] extends Rel (fun x y => PLift (r x y)) (m := m) where
  decreasing (h : r x y) : (hM.run y).fst < (hM.run x).fst := by
    decreases_obvious
  IsNorm (e : Expr) := ¬ ∃ e', r e e'

def RedRel.sn {r : Expr → Expr → Prop} {t : Expr → ℕ → Prop}
  {m : Type → Type} [Monad m] [hM : Measure t]
  (hR : RedRel r t (m := m)) (e : Expr) : Acc (fun b a => r a b) e := Acc.intro e (fun e' hr => by
    have h := hR.decreasing hr
    exact sn hR e')
termination_by (hM.run e).fst

def RedRel.wellFounded {r : Expr → Expr → Prop} {t : Expr → ℕ → Prop}
  {m : Type → Type} [Monad m] [hM : Measure t]
  (hR : RedRel r t (m := m)) : WellFounded (fun a b => r b a) := ⟨hR.sn⟩

def reduce {t : Expr → ℕ → Prop} [hT : Measure t] [hR : RedRel r t (hM := hT)]
  (e : Expr) : ((e' : Expr) × (PLift (Relation.ReflTransGen r e e'))) :=
  match hR.run e with
  | .some ⟨e', ⟨h⟩⟩ =>
    have _size_ : (hT.run e').fst < (hT.run e).fst := hR.decreasing h
    let ⟨e'', ⟨h₂⟩⟩ := reduce (r := r) (t := t) e'
    ⟨e'', ⟨.trans (.single h) h₂⟩⟩
  | .none => ⟨e, ⟨.refl⟩⟩
termination_by (hT.run e).fst

open RedRel in def RedRel.Trans {t : Expr → ℕ → Prop} [hT : Measure t] (hR : RedRel r t) : RedRel (Relation.TransGen r) t where
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
