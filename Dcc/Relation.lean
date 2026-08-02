import Dcc.Attrs
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation
import Dcc.Ast

/-
Generalizations of normal forms and decision procedures for rewrite-rule relations
on AST terms. e.g., affine reduction and the old eta (non-NBE) reduction algorithm

Generalizations of confluence, and relations with point congruence

Once RedRel and Complete are implemented, you inherit (reduce r <expr>), where r : Expr → Expr → Prop

This notion of a relation assumes reduction makes a choice of path. That is, we assume call by value
rather than a determinstic reduction like call by name.

All of the classes here have been proven for the core β/ affine-reduction.
Old η-reduction does as well, but new NBE is much smarter and doesn't require as much
machinery, since it works in a single pass with recursion, rather than through rewrite rules.
-/

namespace GenericExpr

@[simp]
theorem id_pure_ext.{u} {α : Type u} (x : α) : (pure x : Id α) = x := rfl

@[grind]
def IsNorm.{u} {α : Type u} (r : α → α → Prop) (A : α) := ¬ ∃ B, r A B

@[grind]
def IsNorm.elim.{u,v } {α : Type u} {C : Sort v} (r : α → α → Prop) {A B : α} (hn : IsNorm r A) (hr : r A B) : C := (hn ⟨_, hr⟩).elim

class Rel.{u, v, s} {α : Type u} {β : Type s} (r : α → β → Sort v) (m : Type (max (max u s) v) → Type (max u s v) := Id) [hM : Monad m] where
  run (x : α) : m ((y : β) × (PULift.{(max (max u s) v) + 1, v} (r x y)))
  sound       : run x = pure ⟨y, ⟨h⟩⟩ → r x y := fun _ => h

def Rel.rel.{u, v, s} {α : Type u} {β : Type s}
  {r : α → β → Sort v} {m : Type (max (max u s) v) → Type (max (max u s) v)} [Monad m]
  (_hR : Rel.{u, v, s} r (m := m)) : (α → β → Sort v) := r

open Rel in class Complete.{u, v, s} {α : Type u} {β : Type s} (r : α → β → Sort v) (P : β → Prop := fun _ => True)
  (m : Type (max (max u s) v) → Type (max (max u s) v) := Id) [hm : Monad m]
  [hR : Rel.{u, v, s} r (m := m)] where
  complete : ∀ (h : r x y) (_p : P y), hR.run x = hm.pure ⟨y, PULift.up h⟩

instance Complete.instDecidable.{u}
  {α : Type u}
  [DecidableEq α]
  (r : α → α → Prop)
  (P : α → Prop := fun _ => True)
  (hDec : outParam (∀ (a : α), Decidable (P a)) := by infer_instance)
  (hR : outParam (Rel.{u, 0, u} r (m := Id)))
  (hC : outParam (Complete.{u, 0, u} r (P := P))) : ∀ (A B : α), Decidable (r A B ∧ P B) := fun A B =>
  if heq : (hR.run A).fst = B then
    if heq₂ : P B then
      .isTrue (⟨heq ▸ (hR.run A).snd.down, heq₂⟩)
    else .isFalse (by simp_all)
  else .isFalse (fun ⟨h, hp⟩ => by simp [hC.complete h hp] at *)

class RedRel.{u, v} {α : Type u} (r : α → α → Sort v) (t : outParam (α → ℕ))
  (m : Sort ((max u v) + 1) → Sort ((max u v) + 1) := Option) [_hM : Monad m] extends Rel.{u, v, u} r (m := m) where
  decreasing : r x y → t y < t x := by
    intro x y h
    induction h
    any_goals (
      focus
      try dsimp
      try grind
      try simp_all [dcc_rel, dcc_size, Rel.run]
      try grind
      try aesop (rule_sets := [DccRel, DccSize])
      try rfl
      done)

attribute [dcc_size] RedRel.decreasing

attribute [dcc_force_rel] RedRel.toRel.eq_def RedRel.toRel Rel.run Rel.run.eq_def

def IsNorm.unique.{u} {α : Type u} {r : α → α → Prop} {A B : α} (hn : IsNorm r A) (hr : r A B) : A = B :=
  (hn ⟨_, hr⟩).elim

def IsNorm.unique'.{u} {α : Type u} {r : α → α → Prop} {A B C : α} (hn : IsNorm r A) (hr₁ : r A B) (_hr₂ : r B C) : A = C :=
  (hn ⟨_, hr₁⟩).elim

def IsNorm.unique_trans.{u} {α : Type u} {r : α → α → Prop} {A B : α} (hn : IsNorm r A) (hr : (Relation.TransGen r) A B) : A = B :=
  match hr with
  | .single h => hn.unique h
  | .tail hrt hr => hn.unique ((hn.unique_trans hrt) ▸ hr)

def IsNorm.unique_refl.{u} {α : Type u} {r : α → α → Prop} {A B : α} (hn : IsNorm r A) (hr : (Relation.ReflTransGen r) A B) : A = B := by
  rw [← Relation.reflGen_transGen] at hr
  cases hr with
  | refl => rfl
  | single h => exact hn.unique_trans h

def RedRel.sn.{u} {α : Type u} {r : α → α → Prop} (t : outParam (α → ℕ))
  {m : Sort ((max u 0) + 1) → Sort ((max u 0) + 1)} [Monad m]
  (hR : RedRel r t (m := m)) (e : α) : Acc (fun b a => r a b) e := Acc.intro e (fun e' hr => by
    have h := hR.decreasing hr
    exact sn t hR e')
termination_by t e

def RedRel.wellFounded.{u} {α : Type u} {r : α → α → Prop} (t : outParam (α → ℕ))
  {m : Sort ((max u 0) + 1) → Sort ((max u 0) + 1)} [Monad m]
  (hR : RedRel (α := α) r t (m := m)) : WellFounded (fun a b => r b a) := ⟨hR.sn⟩

@[dcc_force_reduce, aesop norm (rule_sets := [DccForceReduce])]
def reduce.{u} {α : Type u} {t : α → ℕ} (r : α → α → Prop) [hR : RedRel r t]
  (e : α) : ((e' : α) × (PULift.{u + 1, 0} (Relation.ReflTransGen r e e'))) :=
  match hR.run e with
  | .some ⟨e', ⟨h⟩⟩ =>
    have _size_ : t e' < t e := hR.decreasing h
    let ⟨e'', ⟨h₂⟩⟩ := reduce r (t := t) e'
    ⟨e'', ⟨.trans (.single h) h₂⟩⟩
  | .none => ⟨e, ⟨.refl⟩⟩
termination_by t e

@[dcc_reduce, inline] abbrev reduce' {t : α → ℕ} (r : α → α → Prop) [hR : RedRel r t]
  (e : α) : α := (reduce r e).fst

def reduce? [DecidableEq α] {t : α → ℕ} (r : α → α → Prop) [hR : RedRel r t]
  (e : α) : Option ((e' : α) × (PULift.{u + 1, 0} (Relation.TransGen r e e'))) :=
  let ⟨e', ⟨h⟩⟩ := reduce r e
  if heq : e = e' then
    .none
  else
    .some ⟨e', ⟨by
      rw [← Relation.reflGen_transGen] at h
      cases h with
      | refl => simp_all
      | single h => exact h⟩⟩

open RedRel in @[reducible]
def RedRel.to_trans.{u} {α : Type u} [DecidableEq α] {r : α → α → Prop} (t : outParam (α → ℕ)) (hR : RedRel.{u, 0} r t) : RedRel.{u, 0} (Relation.TransGen r) t where
  decreasing := fun h => by
    induction h with
    | single h =>
      exact hR.decreasing h
    | tail h₁ hr ih =>
      have h := hR.decreasing hr
      grind
  -- reducer given decreasing
  run := reduce? r

@[reducible] def RedRel.to_reflTrans.{u} {α : Type u} {r : α → α → Prop} {t : α → ℕ} (hR : RedRel (α := α) r t (m := Option)) : Rel.{u, 0, u}
  (Relation.ReflTransGen r) Id where
  run := reduce r

instance RedRel.instReflTransRel.{u} {α : Type u} {r : α → α → Prop} {t : α → ℕ}
  [hR : RedRel r t (m := Option)] :
  Rel.{u,0,u} (Relation.ReflTransGen r) Id :=
  hR.to_reflTrans

abbrev RedRel.ReflTrans.{u} {α : Type u} {r : α → α → Prop} {t : α → ℕ} {m : Type u → Type u} [Monad m] (_hR : RedRel (α := α) r t (m := m)) : α → α → Prop := Relation.ReflTransGen r
abbrev RedRel.Trans {r : α → α → Prop} {t : α → ℕ} {m : Type → Type} [Monad m] (_hR : RedRel r t (m := m)) : α → α → Prop    := Relation.TransGen r

open Rel in class Congruent.{u} {τ : Type u} (r : GenericExpr τ → GenericExpr τ → Prop) where
  congrFun_ (h : r f f') : r (DCC[τ] (f x)) (DCC[τ] (f' x)) := by exact .congrFun
  congrArg_ (h : r x x') : r (DCC[τ] (f x)) (DCC[τ] (f x')) := by exact .congrArg
  sigl_     (h : r x x') : r (DCC[τ] ⟦β⟧(x, y)) (DCC[τ] ⟦β⟧(x', y)) := by exact .sigl
  sigr_     (h : r y y') : r (DCC[τ] ⟦β⟧(x, y)) (DCC[τ] ⟦β⟧(x, y')) := by exact .sigr
  pil_      (h : r x x') : r (DCC[τ] Π(x, y)) (DCC[τ] Π(x', y)) := by exact .pil
  pir_      (h : r y y') : r (DCC[τ] Π(x, y)) (DCC[τ] Π(x, y')) := by exact .pir
  coup_     (h : r β β') : r (DCC[τ] Coup(β)) (DCC[τ] Coup(β'))     := by exact .coup

theorem Congruent.congrFun'.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop}
  {f x f' : GenericExpr τ} [hR : Congruent (τ := τ) r] (h : r f f') : r
  (DCC[τ] (f x))
  (DCC[τ] (f' x)) :=
  (hR.congrFun_ h)

theorem Congruent.congrArg'.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} {f x x' : GenericExpr τ}
  [hR : Congruent r] (h : r x x') : r (DCC[τ] (f x)) (DCC[τ] (f x')) :=
  (hR.congrArg_ h)

theorem Congruent.sigl'.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} {β x y x' : GenericExpr τ} [hR : Congruent r]
  (h : r x x') : r (DCC[τ] ⟦β⟧(x, y)) (DCC[τ] ⟦β⟧(x', y)) :=
  (hR.sigl_ h)

theorem Congruent.pil'.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} {x x' y : GenericExpr τ} [hR : Congruent r]
  (h : r x x') : r (DCC[τ] Π(x, y)) (DCC[τ] Π(x', y)) :=
  (hR.pil_ h)

theorem Congruent.pir'.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} {x y y' : GenericExpr τ} [hR : Congruent r]
  (h : r y y') : r (DCC[τ] Π(x, y)) (DCC[τ] Π(x, y')) :=
  (hR.pir_ h)

theorem Congruent.sigr'.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} {β x y y' : GenericExpr τ}
  [hR : Congruent r] (h : r y y') : r (DCC[τ] ⟦β⟧(x, y)) (DCC[τ] ⟦β⟧(x, y')) :=
  (hR.sigr_ h)

theorem Congruent.coup'.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} {β β' : GenericExpr τ} [hR : Congruent r] (h : r β β') : r (DCC[τ] Coup(β)) (DCC[τ] Coup(β')) :=
  (hR.coup_ h)

instance Congruent.trans.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} [hC : Congruent r] : Congruent (Relation.TransGen r) where
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
  coup_ h := by
    induction h with
    | single h => exact .single (hC.coup' h)
    | tail => exact .trans (by assumption) (.single (hC.coup' (by assumption)))
  pil_ h := by
    induction h with
    | single h => exact .single (hC.pil' h)
    | tail => exact .trans (by assumption) (.single (hC.pil' (by assumption)))
  pir_ h := by
    induction h with
    | single h => exact .single (hC.pir' h)
    | tail => exact .trans (by assumption) (.single (hC.pir' (by assumption)))

instance Congruent.reflTrans.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} [hC : Congruent r] : Congruent (Relation.ReflTransGen r) where
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
  pil_ h := by
    rw [← Relation.reflGen_transGen] at *
    cases h with
    | single h => exact .single (hC.trans.pil' h)
    | refl => exact .refl
  pir_ h := by
    rw [← Relation.reflGen_transGen] at *
    cases h with
    | single h => exact .single (hC.trans.pir' h)
    | refl => exact .refl
  coup_ h := by
    rw [← Relation.reflGen_transGen] at *
    cases h with
    | single h => exact .single (hC.trans.coup' h)
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

open Rel in class Confluent.{u} {α : Type u} (r : α → α → Prop)
  (m : (α → α → Prop) → α → α → Prop := fun x => x) where
  conf : (m r A B) → (m r A C) → ∃ D, Relation.ReflTransGen r B D ∧ Relation.ReflTransGen r C D

open Confluent in @[reducible] def RedRel.globally_confluent.{u} {α : Type u}
  {r : α → α → Prop} {t : α → ℕ} {m : Type u → Type u}
  [Monad m] [hC : Confluent (α := α) r]
  [hR : RedRel.{u} (α := α) r t (m := m)] : (Confluent (α := α) r (m := Relation.ReflTransGen)) where
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

@[dcc_rel, aesop safe apply (rule_sets := [DccRel])] def IsNorm.sigl.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop}
  {β x y : GenericExpr τ} [hC : Congruent r]
  (hn : IsNorm r (DCC[τ] ⟦β⟧(x, y))) : IsNorm r x := fun ⟨_, h⟩ =>
  (hn ⟨_, hC.sigl' h⟩).elim

@[dcc_rel, aesop safe apply (rule_sets := [DccRel])] def IsNorm.sigr.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop}
  {β x y : GenericExpr τ} [hC : Congruent r]
  (hn : IsNorm r (DCC[τ] ⟦β⟧(x, y))) : IsNorm r y := fun ⟨_, h⟩ =>
  (hn ⟨_, hC.sigr' h⟩).elim

@[dcc_rel, aesop safe apply (rule_sets := [DccRel])] def IsNorm.congrFun.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} [hC : Congruent r]
  {f x : GenericExpr τ}
  (hn : IsNorm r (DCC[τ] (f x))) : IsNorm r f := fun ⟨_, h⟩ =>
  (hn ⟨_, hC.congrFun' h⟩).elim

@[dcc_rel, aesop safe apply (rule_sets := [DccRel])] def IsNorm.congrArg.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} [hC : Congruent r]
  {f x : GenericExpr τ}
  (hn : IsNorm r (DCC[τ] (f x))) : IsNorm r x := fun ⟨_, h⟩ =>
  (hn ⟨_, hC.congrArg' h⟩).elim

@[dcc_rel, aesop safe apply (rule_sets := [DccRel])] def IsNorm.pil.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop}
  {f_α f_β : GenericExpr τ} [hC : Congruent r]
  (hn : IsNorm r (DCC[τ] Π(f_α, f_β))) : IsNorm r f_α := fun ⟨_, h⟩ =>
  (hn ⟨_, hC.pil' h⟩).elim

@[dcc_rel, aesop safe apply (rule_sets := [DccRel])] def IsNorm.pir.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop}
  {f_α f_β : GenericExpr τ} [hC : Congruent r]
  (hn : IsNorm r (DCC[τ] Π(f_α, f_β))) : IsNorm r f_β := fun ⟨_, h⟩ =>
  (hn ⟨_, hC.pir' h⟩).elim

@[dcc_rel, aesop safe apply (rule_sets := [DccRel])] def IsNorm.coup.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop}
  {β : GenericExpr τ} [hC : Congruent r]
  (hn : IsNorm r (DCC? Coup(β))) : IsNorm r β := fun ⟨_, h⟩ =>
  (hn ⟨_, hC.coup' h⟩).elim

@[dcc_rel] def IsNorm.complete.{u}
  {α : Type u}
  {r : α → α → Prop}
  {t : α → ℕ}
  [hR : RedRel (α := α) r t (m := Option)]
  {A : α}
  (h : IsNorm r A) : (hR.run A) = Option.none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨e', ⟨h₂⟩⟩ heq
  exact (h ⟨_, h₂⟩)

open Rel in class SemiComplete.{u} {α : Type u} {t : α → ℕ}
  (r : α → α → Prop)
  [hR : RedRel.{u} (α := α) r t (m := Option.{u})] where
  complete : r A B → ∃ B h, (hR.run A) = .some ⟨B, ⟨h⟩⟩

@[dcc_rel, aesop safe apply (rule_sets := [DccRel])]
theorem run_none.{u} {τ : Type u} {t : τ → ℕ}
  (r : τ → τ → Prop)
  {A : τ}
  [hR : RedRel (α := τ) r t (m := Option)]
  [hC : SemiComplete (α := τ) r] : hR.run A = .none → IsNorm (α := τ) r A := by
  intro heq ⟨A', h_red⟩
  have ⟨B, h₁, h₂⟩ := hC.complete h_red
  simp_all

open Confluent in @[dcc_rel, aesop safe destruct (rule_sets := [DccRel]), aesop safe apply (rule_sets := [DccForceReduce])]
theorem norm_unique.{u} {α : Type u} {r : α → α → Prop} {m : (α → α → Prop) → α → α → Prop}
  [hC : Confluent r m] {A B C : α} (h₁ : m r A B) (hn₁ : IsNorm r B) (h₂ : m r A C) (hn₂ : IsNorm r C) : B = C := by
  have ⟨D, hr₁, hr₂⟩ := hC.conf h₁ h₂
  have ha := hn₁.unique_refl hr₁
  have hb := hn₂.unique_refl hr₂
  simp_all

@[dcc_reduce, aesop safe apply (rule_sets := [DccReduce])]
theorem RedRel.reduce_norm.{u} {α : Type u}
  {r : α → α → Prop} {t : α → ℕ}
  (hR : RedRel r t (m := Option))
  {A : α} (hn : IsNorm r A) : (reduce r A) = ⟨A, ⟨.refl⟩⟩ := by
  simp [reduce]
  split
  case h_1 h _ =>
    exact (hn ⟨_, h⟩).elim
  case h_2 => congr

@[dcc_reduce, aesop safe forward (rule_sets := [DccReduce])]
theorem RedRel.reduce_norm_fst.{u} {α : Type u} {t : α → ℕ}
  {r : α → α → Prop}
  (hR : RedRel r t (m := Option))
  {A : α} (hn : IsNorm r A) : (reduce r A).fst = A := by
  have h := hR.reduce_norm hn
  simp_all

@[aesop safe apply (rule_sets := [DccReduce])]
theorem reduce_complete.{u} {α : Type u} {r : α → α → Prop} {t : α → ℕ}
  [hR : RedRel (α := α) r t (m := Option)] [hN : SemiComplete (α := α) r (hR := hR)] [hC : Confluent r]
  {A B : α} (hr : Relation.ReflTransGen r A B) (hn : IsNorm r B) : (reduce r A) = ⟨B, ⟨hr⟩⟩ := by
  simp [reduce]
  split
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
      have h_dec : t B' < t A := by
        have h₁ := hR.decreasing hr₂
        have h₂ := hR.decreasing hrB'
        grind
      have h := reduce_complete (.trans (.single hrB') hrt) hn
      have h_fst : (reduce r B').fst = B := by
        simp_all
      cases h_fst
      congr
  case h_2 hneq =>
    match hr.cases_head with
    | .inl h => cases h; congr
    | .inr ⟨_, hrb', hrt⟩ =>
      have ⟨_, hA₁, hA₂⟩ := hN.complete hrb'
      simp_all
termination_by (t A, t B)

@[aesop safe apply (rule_sets := [DccReduce])]
theorem reduce_complete_fst.{u} {α : Type u} {r : α → α → Prop} {t : α → ℕ}
  [hR : RedRel r t (m := Option)] [hN : SemiComplete (α := α) r (hR := hR)] [Confluent r]
  {A B : α} (hr : Relation.ReflTransGen r A B) (hn : IsNorm r B) : (reduce r A).fst = B := by
  have h := reduce_complete hr hn
  simp_all

@[aesop safe apply (rule_sets := [DccReduce])]
theorem reduce_complete_snd.{u} {α : Type u} {r : α → α → Prop} {t : α → ℕ}
  [hR : RedRel r t (m := Option)] [hN : SemiComplete (α := α) r (hR := hR)] [Confluent r]
  {A B : α} (hr : Relation.ReflTransGen r A B) (hn : IsNorm r B) : (reduce r A).snd.down ≍ hr := by
  have h := reduce_complete hr hn
  simp_all

@[aesop safe apply (rule_sets := [DccReduce])]
theorem reduce_complete_pointwise.{u} {α : Type u} {r : α → α → Prop} {t : α → ℕ}
  [hR : RedRel r t (m := Option)] [hN : SemiComplete (α := α) r (hR := hR)] [Confluent r]
  {A B : α} (hr : Relation.ReflTransGen r A B) (hn : IsNorm r B) : (reduce r A).fst = B ∧ (reduce r A).snd.down ≍ hr := by
  have h := reduce_complete hr hn
  simp_all

@[dcc_rel] instance RedRel.instComplete.{u} {α : Type u} {r : α → α → Prop} {t : α → ℕ}
  (hR : RedRel (α := α) r t (m := Option))
  [hN : SemiComplete (α := α) r (hR := hR)] [Confluent r] : Complete.{u, 0, u}
    (r := Relation.ReflTransGen r) (P := IsNorm r) (hR := hR.to_reflTrans (α := α) (r := r) (t := t)) :=
  ⟨fun hr hn => reduce_complete (α := α) (r := r) (t := t) hr hn⟩

@[dcc_step, aesop safe apply (rule_sets := [DccStep])]
theorem reduce_sound.{u} {α : Type u} {r : α → α → Prop} {t : α → ℕ} [_hR : RedRel r t] {A B : α}
  {h : Relation.ReflTransGen r A B}
  (_heq : reduce r A = ⟨B, ⟨h⟩⟩) : Relation.ReflTransGen r A B := h

@[dcc_step, aesop safe apply (rule_sets := [DccStep])]
theorem reduce_norm.{u} {τ : Type u} {t : τ → ℕ}
  {r : τ → τ → Prop}
  [hR : RedRel.{u} (α := τ) r t]
  [hN : SemiComplete.{u} (α := τ) r (hR := hR)]
  {A B : τ} {h : Relation.ReflTransGen r A B}
  (heq : reduce r A = ⟨B, ⟨h⟩⟩) : IsNorm r B := by
  induction A using hR.wellFounded.induction generalizing B with
  | h x ih =>
    simp [reduce] at heq
    split at heq
    case h_1 hred' heq' =>
      have h := ih _ hred' (by cases heq; rfl)
      simp_all
    case h_2 heq' =>
      have h_norm := (run_none r (by cases heq; exact heq'))
      exact (h_norm.unique_refl h) ▸ h_norm

@[dcc_step, aesop safe apply (rule_sets := [DccStep])]
theorem reduce_norm_fst.{u} {α : Type u} {t : α → ℕ}
  {r : α → α → Prop}
  [hR : RedRel (α := α) r t]
  [hN : SemiComplete r (hR := hR)]
  {A B : α}
  (heq : (reduce r A).fst = B) : IsNorm (α := α) r B := by
  cases heq
  exact reduce_norm rfl (A := A) (B := (reduce r A).fst)

@[dcc_step, aesop safe apply (rule_sets := [DccStep])] theorem reduce?_norm.{u} {α : Type u} [DecidableEq α] {t : α → ℕ}
  (r : α → α → Prop)
  [hR : RedRel r t]
  [hN : SemiComplete r (hR := hR)]
  {A B : α}
  (h_some : (reduce? (hR := hR) r A).isSome)
  (heq : ((reduce? (hR := hR) r A).get h_some).fst = B) : IsNorm r B := by
  induction A using hR.wellFounded.induction generalizing B with
  | h x ih =>
    simp [reduce?] at heq
    exact reduce_norm_fst heq

@[dcc_force_reduce] theorem reduce_self.{u} {α : Type u} {t : α → ℕ}
  (r : α → α → Prop) [hR : RedRel r t] [SemiComplete r] {e : α} : (reduce r (reduce r e).fst).fst = (reduce r e).fst := by
  have h := hR.reduce_norm (reduce_norm (A := e) (hR := hR) (B := (reduce r e).fst) rfl)
  simp_all

attribute [dcc_force_reduce] Rel.run.eq_def

@[grind .]
theorem decreasing?.{u} {α : Type u} {t : α → ℕ}
  (r : α → α → Prop) [hR : RedRel r t] {A B : α} (hr : Relation.ReflTransGen r A B) : t B ≤ t A := by
  match hr.cases_head with
  | .inl h =>
    grind
  | .inr ⟨C, h₁, h₂⟩ =>
    have h := hR.decreasing h₁
    have h₂ := decreasing? r h₂
    grind
termination_by t A

theorem reduce'_complete.{u} {α : Type u} {r : α → α → Prop} {t : α → ℕ}
  [hR : RedRel (α := α) r t (m := Option)] [hN : SemiComplete (α := α) r (hR := hR)] [hC : Confluent r]
  {A B : α} (hr : Relation.ReflTransGen r A B) (hn : IsNorm r B) : (reduce' r A) = B := by
  simp [reduce', reduce_complete hr hn]

theorem reduce'_norm.{u} {τ : Type u} {t : τ → ℕ}
  {r : τ → τ → Prop}
  [hR : RedRel.{u} (α := τ) r t]
  [hN : SemiComplete.{u} (α := τ) r (hR := hR)]
  {A B : τ} (heq : reduce' r A = B) : IsNorm r B := by
  simp [reduce'] at heq
  cases heq
  have heq : reduce r A = ⟨(reduce r A).fst, (reduce r A).snd⟩ := by
    simp
  exact reduce_norm heq

theorem reduce'_norm'.{u} {τ : Type u} {t : τ → ℕ}
  {r : τ → τ → Prop}
  [hR : RedRel.{u} (α := τ) r t]
  [hN : SemiComplete.{u} (α := τ) r (hR := hR)]
  {A : τ} : IsNorm r (reduce' r A) :=
  reduce'_norm rfl

@[grind ., grind! .]
theorem decreasing?'.{u} {α : Type u} {t : α → ℕ}
  (r : α → α → Prop) [hR : RedRel r t] {A : α} : (t (reduce r A).fst) ≤ t A :=
  decreasing? _ (reduce_sound (r := r) (A := A) rfl)

instance IsNorm.decidableEq.{u} {τ : Type u} {t : τ → ℕ}
  (r : outParam (τ → τ → Prop))
  [hR : RedRel.{u} (α := τ) r t]
  [Confluent r]
  [DecidableEq τ]
  [hN : SemiComplete.{u} (α := τ) r (hR := hR)]
  {A: τ} : Decidable (IsNorm r A) :=
  if heq : reduce' r A = A then
    have h := reduce'_norm' (hN := hN) (A := A)
    .isTrue (heq ▸ h)
  else
    .isFalse (fun h => heq (reduce'_complete .refl h))

@[dcc_force_reduce, aesop norm (rule_sets := [DccForceReduce])]
def reduce_with_norm.{u} {α : Type u} {t : α → ℕ} (r : α → α → Prop) [hR : RedRel r t]
  [SemiComplete r]
  (e : α) : ((e' : α) × (PULift.{u + 1, 0} (Relation.ReflTransGen r e e' ∧ IsNorm r e'))) :=
  let h_reduce := reduce r e
  ⟨h_reduce.fst, ⟨⟨h_reduce.snd.down, reduce_norm rfl⟩⟩⟩

theorem reduce_sound_fst.{u} {α : Type u} {r : α → α → Prop} {t : α → ℕ} [_hR : RedRel r t] {A B : α}
  (_heq : (reduce r A).fst = B) : Relation.ReflTransGen r A B :=
  have h := reduce_sound (r := r) (A := A) rfl
  _heq ▸ h

theorem reduce_sound_fst_norm.{u} {α : Type u} {r : α → α → Prop} {t : α → ℕ} [_hR : RedRel r t] {A B : α}
  [SemiComplete r]
  (_heq : (reduce r A).fst = B) : Relation.ReflTransGen r A B ∧ IsNorm r B :=
  have ha := reduce_sound (r := r) (A := A) rfl
  have hb := reduce_norm (r := r) (A := A) rfl
  ⟨_heq ▸ ha, _heq ▸ hb⟩

end GenericExpr

inductive NormExpr.{u} {τ : Type u} (r : GenericExpr τ → GenericExpr τ → Prop) : Type u
  | mk : (e : GenericExpr τ) → GenericExpr.IsNorm r e → NormExpr r
deriving DecidableEq

def test_dec_eq_norm_expr.{u} {τ : Type u} [DecidableEq τ] {r : GenericExpr τ → GenericExpr τ → Prop}
  (h₁ h₂ : NormExpr (τ := τ) r) : Bool := decide (h₁ = h₂)

@[grind, inline]
def NormExpr.size {t : GenericExpr τ_c → ℕ} {r : GenericExpr τ_c → GenericExpr τ_c → Prop} [GenericExpr.RedRel r t]
  (n : NormExpr r) : ℕ :=
  match n with
  | ⟨e, _⟩ => t e

@[inline, grind, dcc_rel]
def NormExpr.raw.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} (r : NormExpr r) : GenericExpr τ :=
  match r with
  | ⟨e, _⟩ => e

@[grind =, grind →, dcc_size]
theorem NormExpr.size_eq {t : GenericExpr τ_c → ℕ} {r : GenericExpr τ_c → GenericExpr τ_c → Prop} [GenericExpr.RedRel r t]
  {e : GenericExpr τ_c} {hn : GenericExpr.IsNorm r e} : (NormExpr.mk e hn).size = t e := by
  simp [size]

def NormExpr.ext_iff.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop}
  {A B : NormExpr r} : A = B ↔ A.raw = B.raw :=
  ⟨fun heq => by grind, fun h => by
    match A, B with
    | ⟨A, hn₁⟩, ⟨B, hn₂⟩ => grind⟩

@[grind .]
theorem NormExpr.ext.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop}
  {A B : NormExpr r} : A.raw = B.raw → A = B := ext_iff.mpr

@[grind .]
theorem NormExpr.ext'.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop}
  {A B : NormExpr r} : A = B → A.raw = B.raw := ext_iff.mp

abbrev NormExpr.is_norm.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} (hr : NormExpr r) : GenericExpr.IsNorm r hr.raw :=
  match hr with
  | ⟨_, hn⟩ => hn

@[aesop safe apply (rule_sets := [DccRel])]
def NormExpr.red.{u} {τ : Type u} {r : GenericExpr τ → GenericExpr τ → Prop} (hn : NormExpr r) {B : GenericExpr τ} (hr : r hn.raw B) : False :=
  hn.is_norm ⟨_, hr⟩

namespace Relation

namespace ReflTransGen

def conf.{u} {τ : Type u} {r : τ → τ → Prop} {t : τ → ℕ} [hR : GenericExpr.RedRel r t] [GenericExpr.Confluent r] {A B C : τ} (h₁ : ReflTransGen r A B) (h₂ : ReflTransGen r A C) : ∃ D, ReflTransGen r B D ∧ ReflTransGen r C D := hR.globally_confluent.conf h₁ h₂

end ReflTransGen

end Relation
