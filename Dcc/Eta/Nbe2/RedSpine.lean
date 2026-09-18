import Dcc.Aff.Red
import Dcc.Eta.Nbe2.Hole
import Dcc.Attrs

universe u
variable {τ_c : Type u}

namespace GenericExpr

class Decreasing? (r : GenericExpr τ_c → GenericExpr τ_c → Sort v) where
  decreasing?' : ∀ (_h : r A B), B.size ≤ A.size

class MaxHolePreserved (r : GenericExpr τ_c → GenericExpr τ_c → Sort v) where
  max_hole_preserved (h : r A B) : max_hole B ≤ max_hole A

open MaxHolePreserved

class ReflT (m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Sort v) (_A _B : GenericExpr τ_c), Sort v) (r : GenericExpr τ_c → GenericExpr τ_c → Sort v) where
  refl : m r A A

class Decreasing (r : GenericExpr τ_c → GenericExpr τ_c → Sort v) where
  decreasing : ∀ (_h : r A B), B.size < A.size

def no_refl [hD : Decreasing r] (h : r A A := by assumption) : Faflse := by
  have h := hD.decreasing h
  grind

class Run (m : Type u → Type u) (r : GenericExpr τ_c → GenericExpr τ_c → Type u) where
  run : ∀ (A : GenericExpr τ_c), m (Σ' (B : GenericExpr τ_c), r A B)

class Unique (r : GenericExpr τ_c → GenericExpr τ_c → Sort v) where
  unique : ∀ ⦃B C⦄, r A B → r A C → B = C

class ProofEq (r : GenericExpr τ_c → GenericExpr τ_c → Sort v) where
  eq : ∀ (h₁ h₂ : r A B), h₁ = h₂

class Single (m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Sort v) (_A _B : GenericExpr τ_c), Sort v) (r : GenericExpr τ_c → GenericExpr τ_c → Sort v) where
  single (h : r A B) : m r A B

open Single

open Trans in
class CasesHead (m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u) (r : GenericExpr τ_c → GenericExpr τ_c → Type u)
  [hP : Single m r] [Trans (m r) (m r) (m r)] where
  cases_head (h : m r A C) : (Σ' (h' : r A C), h = single h') ⊕ (Σ' (B : GenericExpr τ_c) (hr' : r A B) (hrt' : m r B C), h = Trans.trans (hP.single hr') hrt')

attribute [dcc_force_rel] CasesHead.cases_head
attribute [dcc_rel] Single.single Single.single.eq_def
attribute [grind] Single.single
attribute [grind =] Single.single.eq_def

class PushHead (m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Sort v) (_A _B : GenericExpr τ_c), Sort v) (r : GenericExpr τ_c → GenericExpr τ_c → Sort v) where
  push_head (hrt : m r B C) (hr : r A B) : m r A C

open CasesHead
open PushHead

def proof_eq {r : GenericExpr τ_c → GenericExpr τ_c → Sort v} [hP : ProofEq r] (h₁ h₂ : r A B) : h₁ = h₂ := hP.eq h₁ h₂

def unique {r : GenericExpr τ_c → GenericExpr τ_c → Sort v} [hP : Unique r] (h₁ : r A B) (h₂ : r A C) : B = C := hP.unique h₁ h₂

def proof_heq {r : GenericExpr τ_c → GenericExpr τ_c → Sort v} [hP : ProofEq r] [hU : Unique r] (h₁ : r A B) (h₂ : r A C) : h₁ ≍ h₂ := by
  let heq := unique h₁ h₂
  let hb := proof_eq (heq ▸ h₁) (heq ▸ h₂)
  grind

attribute [dcc_force_reduce] Run.run
attribute [dcc_size] Decreasing.decreasing

attribute [dcc_force_rel] Run.run Run.run.eq_def Single.single

open Decreasing Run

def run_sound {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [hD : Run m r] [Pure m] {h : r A B} (_heq : hD.run A = pure ⟨B, h⟩) : r A B := h

class Complete' (m : outParam (Type u → Type u)) (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [Run m r] [Pure m] where
  complete : ∀ (h : r A B), run (m := m) A = pure ⟨B, h⟩

open Complete'

def none_complete {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Run Option r] [Complete' (m := Option) r] {A : GenericExpr τ_c} (hn : ∀ ⦃B⦄, r A B → False) : run (m := Option) (r := r) A = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨B, hr⟩
  exact (hn hr).elim

def none_sound {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Run Option r] [Complete' (m := Option) r] {A : GenericExpr τ_c} (heq : run (m := Option) (r := r) A = .none) : ∀ ⦃B⦄, r A B → False := fun ⦃B⦄ h => by
  have heq := complete (m := Option) h
  grind

def complete {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Run M r] [Pure M] [hD : Complete' (m := M) r] (h : r A B) : run (m := M) A = pure ⟨B, h⟩ := hD.complete h

theorem decreasing [hD : Decreasing r] (h : r A B := by assumption) : size B < size A := hD.decreasing h

/-
Deterministic path version of Relation.TransGen.
-/
inductive RedChoicePlus (r : GenericExpr τ_c → GenericExpr τ_c → Type u) : GenericExpr τ_c → GenericExpr τ_c → Type u
  | single : (hr : r A B) → RedChoicePlus r A B
  | head   : (hr : r A B) → (hrt₂ : RedChoicePlus r B C) → RedChoicePlus r A C

inductive RedChoiceStar (r : GenericExpr τ_c → GenericExpr τ_c → Type u) : GenericExpr τ_c → GenericExpr τ_c → Type u
  | plus : RedChoicePlus r A B → RedChoiceStar r A B
  | refl : RedChoiceStar r A A

instance : ReflT RedChoiceStar r := ⟨.refl⟩

instance RedChoicePlus.instSingle {r : GenericExpr τ_c → GenericExpr τ_c → Type u} : Single RedChoicePlus r := ⟨.single⟩
instance RedChoiceStar.instSingle {r : GenericExpr τ_c → GenericExpr τ_c → Type u} : Single RedChoiceStar r := ⟨.plus ∘ .single⟩

@[dcc_force_rel]
def RedChoicePlus.trans (hr₁ : RedChoicePlus r A B) (hr₂ : RedChoicePlus r B C) : RedChoicePlus r A C :=
  match hr₁ with
  | .single h => .head h (by assumption)
  | .head a c => .head a (trans (by assumption) (by assumption))

instance RedChoicePlus.instTrans : Trans (RedChoicePlus r) (RedChoicePlus r) (RedChoicePlus r) := ⟨RedChoicePlus.trans⟩
instance RedChoicePlus.instTrans' : Trans r (RedChoicePlus r) (RedChoicePlus r) := ⟨fun h₁ h₂ => RedChoicePlus.trans (single h₁) h₂⟩

@[dcc_force_rel]
def RedChoiceStar.trans (hr₁ : RedChoiceStar r A B) (hr₂ : RedChoiceStar r B C) : RedChoiceStar r A C :=
  match hr₁, hr₂ with
  | h, .refl | .refl, h => h
  | .plus h₁, .plus h₂ => .plus (h₁.trans h₂)

instance RedChoiceStar.instTrans : Trans (RedChoiceStar r) (RedChoiceStar r) (RedChoiceStar r) := ⟨RedChoiceStar.trans⟩
instance RedChoiceStar.instTrans' : Trans r (RedChoiceStar r) (RedChoiceStar r) := ⟨fun h₁ h₂ => match h₂ with
  | .refl => .plus (.single h₁)
  | .plus p => .plus (RedChoicePlus.head h₁ p)⟩

attribute [dcc_force_rel] Trans.trans Trans.trans.eq_def

instance RedChoicePlus.instCasesHead {r : GenericExpr τ_c → GenericExpr τ_c → Type u} : CasesHead (r := r) (m := RedChoicePlus) := ⟨fun hrt => match heq : hrt with
  | .single h => .inl ⟨h, rfl⟩
  | .head hr hrt => .inr ⟨_, hr, hrt, by dcc_simp_all (! !)⟩⟩

@[grind]
def IsNorm' (r : GenericExpr τ_c → GenericExpr τ_c → Type u) (A : GenericExpr τ_c) := ∀ ⦃B⦄, r A B → False

def IsNorm'.elim (hn : IsNorm' r A) (hr : r A B) : A = B := (hn hr).elim

class ElimNorm (m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u) (r : GenericExpr τ_c → GenericExpr τ_c → Type u) where
  elim_norm (hn : IsNorm' r A) (h : m r A B) : A = B

open ElimNorm

@[grind]
def AndNorm (m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u) (r : GenericExpr τ_c → GenericExpr τ_c → Type u) (A B : GenericExpr τ_c) :=
  m r A B × (PLift (IsNorm' r B))

@[grind]
def AndNorm.mk {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} (h : m r A B) (hn : IsNorm' r B) : AndNorm m r A B := ⟨h, ⟨hn⟩⟩

@[grind]
def AndNorm.raw (h : AndNorm m r A B) : m r A B := match h with | ⟨hr, _⟩ => hr

def AndNorm.is_norm (h : AndNorm m r A B) : IsNorm' r B := match h with | ⟨_, ⟨hn⟩⟩ => hn

def AndNorm.ext {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u}
  {A B : GenericExpr τ_c} {h₁ : AndNorm m r A B} {h₂ : m r A B} {hn : IsNorm' r B} (heq₁ : h₁.raw = h₂) (heq₂ : h₁.is_norm = hn) : h₁ = (AndNorm.mk h₂ hn) :=
  match h₁ with
  | ⟨hr, hn⟩ => by
    cases heq₁; cases heq₂
    simp [mk, raw]

def AndNorm.ext_mpr {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u}
  {A B : GenericExpr τ_c} {h₁ h₂ : AndNorm m r A B} (heq : h₁ = h₂) : h₁.raw = h₂.raw ∧ h₁.is_norm = h₂.is_norm := by
  constructor <;> grind

@[grind, dcc_size]
def RedChoicePlus.length (h : RedChoicePlus r A B) : ℕ :=
  match h with
  | .single _ => 1
  | .head _ xs => xs.length.succ

@[grind, dcc_size]
def RedChoiceStar.length (h : RedChoiceStar r A B) : ℕ :=
  match h with
  | .refl => 0
  | .plus h => h.length

@[grind .]
theorem RedChoicePlus.length_pos (h : RedChoicePlus r A B) : 0 < h.length := by
  cases h <;> grind

instance RedChoicePlus.push_head : PushHead RedChoicePlus r := ⟨fun hrt hr => .trans (.single hr) hrt⟩
instance RedChoiceStar.push_head : PushHead RedChoiceStar r := ⟨fun hrt hr => .trans (.plus (.single hr)) hrt⟩

def RedChoicePlus.decreasing_impl [Decreasing r] (hrt : RedChoicePlus r A B) : size B < size A :=
  match hrt with
  | .single h => GenericExpr.decreasing h
  | .head hr hrt => by
    have h_dec₁ := GenericExpr.decreasing hr
    have h_dec₂ := decreasing_impl hrt
    grind

instance {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] : Decreasing (RedChoicePlus r) := ⟨RedChoicePlus.decreasing_impl⟩
instance {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] : Decreasing? (RedChoiceStar r) := ⟨fun h => match h with
  | .refl => by grind
  | .plus p => by have h := p.decreasing_impl; grind⟩

def RedChoicePlus.length_same {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] [Unique r] [ProofEq r] (h₁ h₂ : RedChoicePlus r A B) : h₁.length = h₂.length := by
  match cases_head h₁, cases_head h₂ with
  | .inl ⟨hr₁, heq₁⟩, .inl ⟨hr₂, heq₂⟩ =>
    cases heq₁; cases heq₂
    rfl
  | .inr ⟨_, hr₁, hrt₁, heq₁⟩, .inl ⟨hr₂, heq₂⟩
  | .inl ⟨hr₁, heq₁⟩, .inr ⟨_, hr₂, hrt₂, heq₂⟩ =>
    cases heq₁; cases heq₂
    cases unique hr₁ hr₂
    have h_dec := decreasing (by assumption)
    grind
  | .inr ⟨_, hr₁, hrt₁, heq₁⟩, .inr ⟨_, hr₂, hrt₂, heq₂⟩ =>
    cases heq₁; cases heq₂
    cases unique hr₁ hr₂
    cases proof_eq hr₁ hr₂
    have h_dec₁ := decreasing hr₁
    have h := hrt₁.length_same hrt₂
    dcc_simp_all (! !)
termination_by A.size

open Run in
def run_trans {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [Run Option r] [Decreasing r] [Single m r] [Trans (m r) (m r) (m r)] (A : GenericExpr τ_c) : Option (Σ' B, m r A B) :=
  match run (m := Option) (r := r) A with
  | .some ⟨B, hr⟩ =>
    have h_dec := decreasing hr
    match B.run_trans (m := m) (r := r) with
    | .some ⟨C, hr'⟩ => .some ⟨_, trans (single (m := m) hr) hr'⟩
    | .none => .some ⟨_, single (by assumption)⟩
  | .none => .none
termination_by A.size

instance {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] [Run Option r] : Run Option (RedChoicePlus r) := ⟨run_trans r⟩
instance {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] [Run Option r] [Single m r] [Trans (m r) (m r) (m r)] : Run Option (m r) := ⟨run_trans r⟩

instance CasesHead.elim_cast_higher [Trans (m r) (m r) (m r)] [Decreasing r] [Single m r] [CasesHead m r] : ElimNorm m r := ⟨fun {A B} hn h => by
  match cases_head h with
  | .inl ⟨h', heq⟩ => exact hn.elim h'
  | .inr ⟨_, h₁, h₂, heq'⟩ => cases hn.elim h₁; exact no_refl h₁⟩

def IsNorm'.down {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Single m r] (hn : IsNorm' (m r) A) : IsNorm' r A := fun _ h =>
  hn (single h)

def IsNorm'.up {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (hn : IsNorm' r A) : IsNorm' (m r) A := fun _ h =>
  match cases_head h with
  | .inl ⟨h, _⟩ => hn h
  | .inr ⟨_, h, _, _⟩ => hn h

open Unique

def normal_form_unique {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] [Unique r] [ProofEq r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (h₁ : AndNorm m r A B) (h₂ : AndNorm m r A C) : B = C := by
  match cases_head h₁.raw, cases_head h₂.raw with
  | .inl ⟨hr₁, heq₁⟩, .inl ⟨hr₂, heq₂⟩ =>
    exact unique hr₁ hr₂
  | .inr ⟨_, hr₁, hrt₁, heq₁⟩, .inl ⟨hr₂, heq₂⟩ =>
    have hn₁ := h₁.is_norm
    have hn₂ := h₂.is_norm
    cases unique hr₁ hr₂
    simp [elim_norm hn₂ hrt₁]
  | .inl ⟨hr₁, heq₁⟩, .inr ⟨_, hr₂, hrt₂, heq₂⟩ =>
    have hn₁ := h₁.is_norm
    have hn₂ := h₂.is_norm
    cases unique hr₁ hr₂
    simp [elim_norm hn₁ hrt₂]
  | .inr ⟨_, hr₁, hrt₁, heq₁⟩, .inr ⟨_, hr₂, hrt₂, heq₂⟩ =>
    have hn₁ := h₁.is_norm
    have hn₂ := h₂.is_norm
    cases unique hr₁ hr₂
    cases proof_eq hr₁ hr₂
    have h_dec₁ := decreasing hr₁
    exact normal_form_unique ⟨hrt₁, ⟨hn₁⟩⟩ ⟨hrt₂, ⟨hn₂⟩⟩
termination_by A.size

instance instUniqueNorm {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] [Unique r] [ProofEq r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] : Unique (AndNorm m r) := ⟨normal_form_unique⟩

def normal_proof_unique {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] [Decreasing (m r)] [Unique r] [ProofEq r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (h₁ h₂ : AndNorm m r A B) : h₁ = h₂ := by
  match cases_head h₁.raw, cases_head h₂.raw with
  | .inl ⟨hr₁, heq₁⟩, .inl ⟨hr₂, heq₂⟩ =>
    refine (AndNorm.ext (h₁ := h₁) ?_ (by grind)).trans (AndNorm.ext (h₁ := h₂) ?_ (by grind))
    <;> (
      change AndNorm.raw _ = AndNorm.raw _
      have ha := proof_eq hr₁ hr₂
      simp_all)
  | .inr ⟨_, hr₁, hrt₁, heq₁⟩, .inl ⟨hr₂, heq₂⟩ =>
    have hn₁ := h₁.is_norm
    have hn₂ := h₂.is_norm
    cases unique hr₁ hr₂
    exact no_refl hrt₁
  | .inl ⟨hr₁, heq₁⟩, .inr ⟨_, hr₂, hrt₂, heq₂⟩ =>
    have hn₁ := h₁.is_norm
    have hn₂ := h₂.is_norm
    cases unique hr₁ hr₂
    exact no_refl hrt₂
  | .inr ⟨_, hr₁, hrt₁, heq₁⟩, .inr ⟨_, hr₂, hrt₂, heq₂⟩ =>
    have hn₁ := h₁.is_norm
    have hn₂ := h₂.is_norm
    cases unique hr₁ hr₂
    cases proof_eq hr₁ hr₂
    have h_dec₁ := decreasing hr₁
    have heq' := normal_proof_unique ⟨hrt₁, ⟨hn₁⟩⟩ ⟨hrt₂, ⟨hn₂⟩⟩
    refine (AndNorm.ext (h₁ := h₁) ?_ (by grind)).trans (AndNorm.ext (h₁ := h₂) ?_ (by grind))
    <;> (
      change AndNorm.raw _ = AndNorm.raw _
      grind)
termination_by A.size

instance instProofEqNorm {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] [Unique r] [ProofEq r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] [Decreasing (m r)] : ProofEq (AndNorm m r) := ⟨normal_proof_unique⟩

def cast_decreasing_up {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} [Decreasing r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (h : m r A B) : B.size < A.size :=
  match cases_head h with
  | .inl ⟨hr, _heq⟩ => decreasing hr
  | .inr ⟨B, hr', hrt', heq'⟩ => by
    have h_dec₁ := decreasing hr'
    have h := cast_decreasing_up hrt'
    grind
termination_by A.size

instance Decreasing.instUp {m : ∀ (_r : GenericExpr τ_c → GenericExpr τ_c → Type u) (_A _B : GenericExpr τ_c), Type u} [Decreasing r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] : Decreasing (m r) := ⟨cast_decreasing_up⟩

open Run in
def run_norm (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [Run Option r] [Decreasing r] [Complete' (m := Option) r] (A : GenericExpr τ_c) : Σ' B, AndNorm RedChoiceStar r A B :=
  match heq : run (m := Option) (r := r) A with
  | .some ⟨B, hr⟩ =>
    have _h_dec := decreasing hr
    match B.run_norm (r := r) with
    |  ⟨C, ⟨hr', ⟨hn⟩⟩⟩ => ⟨_, ⟨trans (single (m := RedChoiceStar) hr) hr', ⟨hn⟩⟩⟩
  | .none =>
    have hn : IsNorm' r A := none_sound heq
    ⟨_, ⟨.refl, ⟨hn⟩⟩⟩
termination_by A.size

open Run in
def run_norm_plus (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [Run Option r] [Decreasing r] [Complete' (m := Option) r] (A : GenericExpr τ_c) : Option (Σ' B, AndNorm RedChoicePlus r A B) :=
  match run_norm r A with
  | ⟨_, ⟨hr, ⟨hn⟩⟩⟩ =>
    match hr with
    | .refl => .none
    | .plus hr => .some ⟨_, ⟨hr, ⟨hn⟩⟩⟩

instance [Run Option r] [Decreasing r] [Complete' (m := Option) r] : Run Id (AndNorm RedChoiceStar r) := ⟨run_norm _⟩
instance [Run Option r] [Decreasing r] [Complete' (m := Option) r] : Run Option (AndNorm RedChoicePlus r) := ⟨run_norm_plus _⟩

def get_head [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (hr : m r A B) : Σ' B', r A B' :=
  match cases_head hr with
  | .inl ⟨h, _heq⟩ => ⟨_, h⟩
  | .inr ⟨_, h, _, _⟩ => ⟨_, h⟩

instance : ElimNorm RedChoicePlus r := ⟨fun hn hr => (hn (get_head hr).snd).elim⟩

instance : ElimNorm RedChoiceStar r := ⟨fun {_A B} hn hr => match hr with
  | .refl => rfl
  | .plus h => elim_norm hn h⟩

def RedChoiceStar.complete {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [ProofEq r] [Unique r] [Decreasing r] [Run Option r] [Complete' (m := Option) r] (hr : AndNorm RedChoiceStar r A B) : run_norm _ A = ⟨B, hr⟩ := by
  unfold run_norm
  split
  case h_1 B' hr' heq =>
    simp
    split
    case h_1 =>
      expose_names
      match hr with
      | ⟨.refl, ⟨hn⟩⟩ =>
        cases hn.elim hr'
        exact no_refl hr'
      | ⟨.plus hr, ⟨hn⟩⟩ =>
        cases hr'_1 with
        | refl =>
          cases unique (AndNorm.mk hr (by assumption)) (AndNorm.mk (.single hr') (by assumption))
          congr!
          dcc_simp (! !)
          have heq : (AndNorm.mk (RedChoicePlus.single hr') (by assumption)) = (AndNorm.mk hr (by assumption)) := by
            apply proof_eq
          have ⟨heql, heqr⟩ := AndNorm.ext_mpr heq
          cases heql; cases heqr
          rfl
        | plus hrp =>
          cases unique (AndNorm.mk hr (by assumption)) (AndNorm.mk (Trans.trans (RedChoicePlus.single hr') hrp) (by assumption))
          congr!
          dcc_simp (! !)
          have heq : (AndNorm.mk (RedChoicePlus.head hr' hrp) (by assumption)) = (AndNorm.mk hr (by assumption)) := by
            apply proof_eq
          have ⟨heql, heqr⟩ := AndNorm.ext_mpr heq
          cases heql; cases heqr
          rfl
  case h_2 heq_none =>
    have hnorm : IsNorm' _ _ := none_sound heq_none
    cases elim_norm hnorm hr.raw
    dcc_simp (! !)
    match hr with
    | ⟨.refl, _⟩ => rfl
    | ⟨.plus h, ⟨hn⟩⟩ => exact (hn.up h).elim

instance RedChoiceStar.instComplete {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [ProofEq r] [Unique r] [Decreasing r] [Run Option r] [Complete' (m := Option) r] : Complete' (m := Id) (AndNorm RedChoiceStar r) := ⟨RedChoiceStar.complete⟩

instance RedChoicePlus.instComplete {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [ProofEq r] [Unique r] [Decreasing r] [Run Option r] [Complete' (m := Option) r] : Complete' (m := Option) (AndNorm RedChoicePlus r) := ⟨by
  intro A B ⟨h, ⟨hn⟩⟩
  dcc_simp (! !)
  unfold run_norm_plus
  split
  case h_1 =>
    split
    case h_1 =>
      expose_names
      have heq' := RedChoiceStar.instComplete.complete ⟨hr, ⟨hn_1⟩⟩
      dcc_simp_all (! !)
      exact hn_2 (get_head h).snd
    case h_2 =>
      expose_names
      have heq' := RedChoiceStar.instComplete.complete ⟨hr, ⟨by assumption⟩⟩
      dcc_simp_all (! !)
      have heq_fst : fst = fst_1 := by grind
      cases heq_fst
      have heq'' := unique (AndNorm.mk h (by assumption)) (AndNorm.mk hr_1 (by assumption))
      dcc_simp_all (! !)
      change AndNorm.mk _ _ ≍ AndNorm.mk _ _
      apply proof_heq⟩

instance RedChoicePlus.elim_norm : ElimNorm RedChoicePlus r := ⟨fun hn hrt =>
  match hrt with
  | .single hr => (hn hr).elim
  | .head hrt₁ hrt₂ => (hn (by assumption)).elim⟩

/-
Possible unary head-level reductions. Otherwise,
no head-level step is made.
-/
@[grind, aesop safe (rule_sets := [DccRel]) [constructors], aesop safe (rule_sets := [DccRel]) [cases]]
inductive RedAff.IsHead : (hr : RedAff A B) → Type u
  | fstc  {B _B a b}     : IsHead (.fstc (_α := B) (β := _B) (a := a) (b := b))
  | sndc  {B _B a b}     : IsHead (.sndc (_α := B) (β := _B) (a := a) (b := b))
  | eval  {A B _B x y z} : IsHead (.evalc (_α := A) (_β := B) (x := x) (__β := _B) (y := y) (z := z))
  | eql   {B env x}      : IsHead (.eql (f_α := B) (env := env) (x := x))
  | map   {x y}          : IsHead (.map (f := x) (x := y))
  | fmap  {x y}          : IsHead (.fmap (f := x) (x := y))
  | unbox {A y}          : IsHead (.unbox (A := A) (x := y))
  | pair  {B x y z}      : IsHead (.pair (β := B) (M := x) (N := y) (x := z))
  | curr' {A B x y z}    : IsHead (.curr' (α := A) (β := B) (x := x) (y := y) (z := z))
  | id    {A x}          : IsHead (.id (α := A) (x := x))
  | quot  {B x y}        : IsHead (.quot (β := B) (x := x) (y := y))
  | curr  {A B x y z}    : IsHead (.curr (α := A) (β := B) (x := x) (y := y) (z := z))
  | sigma {B C x}        : IsHead (.sigma (f_α := B) (f_β := C) (env := x))
  /-
    Cases like Id(A) ∘ Fst(Id(A)) ⟦Id(A)⟧(x, y) = Id(A) (Fst(Id(A)) ⟦Id(A)⟧(x, y)) will get stuck
    due to lacking congruence, since we are specifically interested in head-reductions.

    Maybe?: have two variants of each comp where one checks (y z).IsNorm and one checks that there is a h : y z -> z' such that h.IsHead?
  -/
  | comp  {x y z}        : IsHead (.comp (x := x) (y := y) (z := z))
deriving Repr

@[grind]
def RedHead (A B : GenericExpr τ_c) := Σ' (hr : PLift (RedAff A B)), hr.down.IsHead

def IsNorm.to_head (h : IsNorm RedAff x) : IsNorm' RedHead x := fun _ ⟨⟨h'⟩, _⟩ => h ⟨_, h'⟩

@[aesop norm (rule_sets := [DccRel])]
def red_head? (A : GenericExpr τ_c) : Option (Σ' (B : GenericExpr τ_c), RedHead A B) :=
  match A with
  | DCC? (Σ(_B, _C) _x) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (Eql(_B) &(_y) &(_z)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (!Λ(_A, _B, _x) &(_y) &(_z)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (Λ(_A, _B, _x) _y _z) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (`(_B, _x) _y) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (⟦_B⟧⟨_x, _y⟩ &(_z)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? ((_x ∘ _y) _z) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (*(_A) &(_y)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? ($<_x> &(_y)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (!<_x> &(_y)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (Eval(_A, _B, _x) ⟦_C⟧(_y, _z)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (Id(_A) _x) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (Fst(_B) ⟦__B⟧(_x, _y)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (Snd(_B) ⟦__B⟧(_x, _y)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | _ => .none

@[grind ., grind =>, aesop safe forward (rule_sets := [DccRel])]
theorem RedAff.IsHead.complete {hr : RedAff A B} (hrt : hr.IsHead) : red_head? A = .some ⟨B, ⟨hr⟩, hrt⟩ := by
  induction hr
  any_goals (
    focus
    try (simp [red_head?])
    cases hrt
    try (rfl)
    done)
  case congrArg hr ih =>
    cases hrt <;> simp [red_head?]

def RedAff.IsHead.decreasing {hr : RedAff A B} (_hrt : hr.IsHead) : B.size < A.size := hr.decreasing

instance : Decreasing (RedHead (τ_c := τ_c)) := ⟨fun ⟨_, h⟩ => RedAff.IsHead.decreasing h⟩

instance : Run Option (RedHead (τ_c := τ_c)) := ⟨red_head?⟩

instance : Unique (RedHead (τ_c := τ_c)) := ⟨fun ⟨⟨hr₁⟩, h₁⟩ ⟨⟨hr₂⟩, h₂⟩ => by
  cases h₁ <;> (cases h₂; grind)⟩

instance : ProofEq (RedHead (τ_c := τ_c)) := ⟨fun ⟨⟨hr₁⟩, h₁⟩ ⟨⟨hr₂⟩, h₂⟩ => by
  cases h₁ <;> (cases h₂; grind)⟩

instance : Complete' (m := Option) (RedHead (τ_c := τ_c)) := ⟨fun {A B} ⟨_, h⟩ => by
  dcc_simp (! !)
  unfold red_head?
  cases h <;> grind⟩

instance : MaxHolePreserved (RedHead (τ_c := τ_c)) := ⟨fun ⟨_, h⟩ => by
  cases h <;> grind⟩

inductive RedCongrFun : GenericExpr τ_c → GenericExpr τ_c → Type u
  | single   : (hr : RedHead A B) → RedCongrFun A B
  | congrFun : (hn : ∀ ⦃B⦄, (RedHead (DCC? (f x)) B) → False) → RedCongrFun f f' → RedCongrFun (DCC? (f x)) (DCC? (f' x))

def step_congr_fun? (A : GenericExpr τ_c) : Option (Σ' B, RedCongrFun A B) :=
  if heq : (red_head? A).isSome then
    .some ⟨_, .single ((red_head? A).get heq).2⟩
  else
    match A with
    | DCC? (f x) =>
      match f.step_congr_fun? with
      | .some ⟨_, h⟩ =>
        have hn : ∀ ⦃B⦄ (hr : RedHead (DCC? (f x)) B), False := by
          intro B ⟨hr, hn⟩
          simp_all [hn.complete]
        .some ⟨_, .congrFun hn h⟩
      | .none => .none
    | _ => .none

instance : Decreasing (RedCongrFun (τ_c := τ_c)) := ⟨fun h => by
  induction h
  · exact decreasing (by assumption)
  · grind⟩

instance : Run Option (RedCongrFun (τ_c := τ_c)) := ⟨step_congr_fun?⟩

instance : Unique (RedCongrFun (τ_c := τ_c)) := ⟨fun h₁ h₂ => by
  rename_i A B C
  induction h₁ generalizing C with
  | single h₁ =>
    induction h₂ with
    | single h₂ => exact unique (by assumption) (by assumption)
    | congrFun hn hrt ih => cases hn h₁
  | congrFun hn hrt ih =>
    cases h₂ with
    | single h₂ =>
      cases hn h₂
    | congrFun hn₂ hrt₂ =>
      congr
      exact ih hrt₂⟩

instance : ProofEq (RedCongrFun (τ_c := τ_c)) := ⟨fun h₁ h₂ => by
  rename_i A B
  induction h₁ with
  | single h₁ =>
    induction h₂ with
    | single h₂ =>
      cases unique (by assumption) (by assumption)
      simp [proof_eq h₁ h₂]
    | congrFun hn hrt ih => cases hn h₁
  | congrFun hn hrt ih =>
    cases h₂ with
    | single h₂ =>
      cases hn h₂
    | congrFun hn₂ hrt₂ =>
      congr
      exact ih hrt₂⟩

instance RedCongrFun.complete : Complete' (m := Option) (RedCongrFun (τ_c := τ_c)) := ⟨fun {A B} hr => by
  dcc_simp (! !)
  induction hr with
  | single hr =>
    rename_i A B
    unfold step_congr_fun?
    let heq := hr.2.complete
    simp [heq]
    apply proof_heq
  | congrFun hr hn a_ih =>
    rename_i f x f'
    unfold step_congr_fun?
    have hn : (f.app x).red_head?.isSome = false := by
      have hn' : (f.app x).red_head? = Option.none := by
        apply Option.eq_none_iff_forall_ne_some.mpr
        intro ⟨B', hr'⟩ heq'
        exact hr hr'
      simp [hn']
    simp [hn, a_ih]⟩

instance : MaxHolePreserved (RedCongrFun (τ_c := τ_c)) := ⟨fun h => by
  induction h
  · rename_i hr; exact max_hole_preserved hr
  · grind⟩

instance [MaxHolePreserved r] : MaxHolePreserved (RedChoicePlus r) := ⟨fun h => by
  induction h with
  | single h => exact max_hole_preserved h
  | head hr hrt ih =>
    have h := max_hole_preserved hr
    grind⟩

instance [MaxHolePreserved r] : MaxHolePreserved (RedChoiceStar r) := ⟨fun h => by
  induction h with
  | refl => grind
  | plus p => exact max_hole_preserved p⟩

declare_syntax_cat red_rel
scoped syntax "wh"  : red_rel
scoped syntax "whᶠ" : red_rel
scoped syntax "β"  : red_rel

declare_syntax_cat step_count
scoped syntax "⋆" : step_count
scoped syntax "⁺" : step_count

declare_syntax_cat arrow_kind
scoped syntax "→!" : arrow_kind
scoped syntax "→"  : arrow_kind

scoped syntax "interpr" red_rel    : term
scoped syntax "interpn" step_count : term
scoped syntax "interp→" arrow_kind : term

declare_syntax_cat reduction

scoped syntax gen_dcc ((arrow_kind noWs red_rel) noWs step_count) gen_dcc : reduction
scoped syntax gen_dcc (arrow_kind noWs red_rel) gen_dcc : reduction

/-scoped syntax ((arrow_kind noWs red_rel) noWs step_count) : reduction
scoped syntax (arrow_kind noWs red_rel) : reduction-/

syntax "DSL(" reduction ")" : term
syntax "DSL(" noWs ((arrow_kind noWs red_rel) noWs step_count) noWs ")" : term
syntax "DSL(" noWs (arrow_kind noWs red_rel) noWs ")" : term

macro_rules
  | `(term| DSL(→β)) => `(term| RedAff)
  | `(term| DSL(→!β)) => `(term| RedAffNorm)
  | `(interpr wh) => `(term| RedHead)
  | `(interpr whᶠ) => `(term| RedCongrFun)
  | `(interpr β) => `(term| (fun a b => PLift (RedAff a b)))
  | `(interpn ⋆) => `(term| RedChoiceStar)
  | `(interpn ⁺) => `(term| RedChoicePlus)
  | `(interp→ →!) => `(term| AndNorm)
  | `(interp→ →) => `(term| _root_.id)
  | `(term| DSL($knd:arrow_kind$rel:red_rel$cnt:step_count)) => do
    let m ← `(interp→ $knd)
    let r ← `(interpr $rel)
    let cnt ← `(interpn $cnt)
    `(term| $m $cnt $r)
  | `(term| DSL($A:gen_dcc $knd:arrow_kind$rel:red_rel$cnt:step_count $B:gen_dcc)) => do
    let m ← `(interp→ $knd)
    let r ← `(interpr $rel)
    let cnt ← `(interpn $cnt)
    `(term| $m $cnt $r (DCC? $A) (DCC? $B))
  | `(term| DSL($A:gen_dcc $knd:arrow_kind$rel:red_rel $B:gen_dcc)) => do
    let m ← `(interp→ $knd)
    let r ← `(interpr $rel)
    `(term| $m $r (DCC? $A) (DCC? $B))
  | `(term| DSL($knd:arrow_kind$rel:red_rel)) => do
    let m ← `(interp→ $knd)
    let r ← `(interpr $rel)
    `(term| $m $r)
  /-| `(term| $A:gen_dcc $knd:arrow_kind$rel:red_rel$cnt:step_count $B:gen_dcc) =>
    `(term| (DCC? $A) $knd:arrow_kind$rel:red_rel$cnt:step_count (DCC? $B))
  | `(term| $A:gen_dcc $knd:arrow_kind$rel:red_rel $B:gen_dcc) =>
    `(term| (DCC? $A) $knd:arrow_kind$rel:red_rel (DCC? $B))-/

#check DSL(Id(Sort 1) →wh Id(Sort 1))
#check DSL(Id(Sort 1) →!wh⁺ Id(Sort 1))
#check DSL(Id(Sort 1) →!β⋆ Id(Sort 1))

instance [ElimNorm m r] : ElimNorm (AndNorm m) r := ⟨fun hn hr => elim_norm hn hr.raw⟩

instance [Decreasing (m r)] : Decreasing (AndNorm m r) := ⟨fun h => decreasing h.raw⟩

def AndNorm.elim_norm_flse [Decreasing r] [ElimNorm m r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (h : AndNorm m r A B) (hn : IsNorm' r A) : False :=
  no_refl (elim_norm hn h ▸ h)

instance [MaxHolePreserved (m r)] : MaxHolePreserved (AndNorm m r) := ⟨fun h => max_hole_preserved h.raw⟩

instance [Run Id (AndNorm m r)] [Complete' (m := Id) (AndNorm m r)] : ProofEq (AndNorm m r) := ⟨fun h₁ h₂ => by
  have ha := Complete'.complete h₁
  have hb := Complete'.complete h₂
  cases ha.symm.trans hb
  rfl⟩

instance [Run Option (AndNorm m r)] [Complete' (m := Option) (AndNorm m r)] : ProofEq (AndNorm m r) := ⟨fun h₁ h₂ => by
  have ha := Complete'.complete h₁
  have hb := Complete'.complete h₂
  cases ha.symm.trans hb
  rfl⟩

def IsNorm'.to_single (hn : IsNorm' RedCongrFun A) : IsNorm' RedHead A := fun _ h => hn (.single h)

/-
227:8:
failed to synthesize instance of type class
  CasesHead (AndNorm RedChoicePlus) RedHead
-/

/-
Destructure (A →!wh⁺ B) or from (A →!wh⁺ᶠ B)

will need to recurse on the left component of hr₁
CasesHead most appropriate.

Because when we get to single case, we know the single case
of readbackfold will fire.
-/

def cases_star (h : RedChoiceStar r A C) : (PLift (A = C))
  ⊕ (Σ' (h' : r A C), h = RedChoiceStar.plus (.single h'))
  ⊕ (Σ' (B : GenericExpr τ_c) (hr' : r A B) (hrt' : RedChoicePlus r B C), h = Trans.trans (RedChoiceStar.plus (.single hr')) (RedChoiceStar.plus hrt')) :=
  match A, heq : h with
  | _, .refl => .inl ⟨rfl⟩
  | _, .plus (.single h) => .inr (.inl ⟨h, by grind⟩)
  | _, .plus (.head h hrt) => .inr (.inr ⟨_, h, hrt, by dcc_simp (! !)⟩)

def IsNorm'.congrFun (hn : IsNorm' RedCongrFun (DCC? (f x))) : IsNorm' RedCongrFun f := fun _ h =>
  hn (.congrFun hn.to_single h)

end GenericExpr
