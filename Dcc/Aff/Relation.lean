import Dcc.Ast.Format
import Dcc.Aff.Size
import Dcc.Attrs

universe u
variable {τ_c : Type u} [DecidableEq τ_c]

namespace GenericExpr

class Decreasing? (r : GenericExpr τ_c → GenericExpr τ_c → Sort v) where
  decreasing?' : ∀ (_h : r A B), B.size ≤ A.size

class ReflT (m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u) (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] where
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

class Single (m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u) (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] where
  single (h : r A B) : m r A B

open Single

open Trans in
class CasesHead (m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u) (r : GenericExpr τ_c → GenericExpr τ_c → Type u)
  [∀ x y, Repr (r x y)] [hP : Single m r] [Trans (m r) (m r) (m r)] where
  cases_head (h : m r A C) : (Σ' (h' : r A C), h = single h') ⊕ (Σ' (B : GenericExpr τ_c) (hr' : r A B) (hrt' : m r B C), h = Trans.trans (hP.single hr') hrt')

attribute [dcc_force_rel] CasesHead.cases_head
attribute [dcc_rel] Single.single Single.single.eq_def
attribute [grind] Single.single
attribute [grind =] Single.single.eq_def

class PushHead (m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u) (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] where
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
attribute [grind =] Run.run.eq_def
attribute [grind] Run.run
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
inductive RedChoicePlus (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ A B, Repr (r A B)] : GenericExpr τ_c → GenericExpr τ_c → Type u
  | single : (hr : r A B) → RedChoicePlus r A B
  | head   : (hr : r A B) → (hrt₂ : RedChoicePlus r B C) → RedChoicePlus r A C
deriving Repr

inductive RedChoiceStar (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ A B, Repr (r A B)] : GenericExpr τ_c → GenericExpr τ_c → Type u
  | plus : RedChoicePlus r A B → RedChoiceStar r A B
  | refl : RedChoiceStar r A A
deriving Repr

instance [∀ x y, Repr (r x y)] : ReflT RedChoiceStar r := ⟨.refl⟩

instance RedChoicePlus.instSingle {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] : Single RedChoicePlus r := ⟨.single⟩
instance RedChoiceStar.instSingle {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] : Single RedChoiceStar r := ⟨.plus ∘ .single⟩

@[dcc_force_rel]
def RedChoicePlus.trans [∀ x y, Repr (r x y)] (hr₁ : RedChoicePlus r A B) (hr₂ : RedChoicePlus r B C) : RedChoicePlus r A C :=
  match hr₁ with
  | .single h => .head h (by assumption)
  | .head a c => .head a (trans (by assumption) (by assumption))

instance RedChoicePlus.instTrans [∀ x y, Repr (r x y)] : Trans (RedChoicePlus r) (RedChoicePlus r) (RedChoicePlus r) := ⟨RedChoicePlus.trans⟩
instance RedChoicePlus.instTrans' [∀ x y, Repr (r x y)] : Trans r (RedChoicePlus r) (RedChoicePlus r) := ⟨fun h₁ h₂ => RedChoicePlus.trans (single h₁) h₂⟩

@[dcc_force_rel]
def RedChoiceStar.trans [∀ x y, Repr (r x y)] (hr₁ : RedChoiceStar r A B) (hr₂ : RedChoiceStar r B C) : RedChoiceStar r A C :=
  match hr₁, hr₂ with
  | h, .refl | .refl, h => h
  | .plus h₁, .plus h₂ => .plus (h₁.trans h₂)

instance RedChoiceStar.instTrans [∀ x y, Repr (r x y)] : Trans (RedChoiceStar r) (RedChoiceStar r) (RedChoiceStar r) := ⟨RedChoiceStar.trans⟩
instance RedChoiceStar.instTrans' [∀ x y, Repr (r x y)] : Trans r (RedChoiceStar r) (RedChoiceStar r) := ⟨fun h₁ h₂ => match h₂ with
  | .refl => .plus (.single h₁)
  | .plus p => .plus (RedChoicePlus.head h₁ p)⟩

attribute [dcc_force_rel] Trans.trans Trans.trans.eq_def

instance RedChoicePlus.instCasesHead {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] : CasesHead (r := r) (m := RedChoicePlus) := ⟨fun hrt => match heq : hrt with
  | .single h => .inl ⟨h, rfl⟩
  | .head hr hrt => .inr ⟨_, hr, hrt, by dcc_simp_all (! !)⟩⟩

@[grind]
def IsNorm' (r : GenericExpr τ_c → GenericExpr τ_c → Type u) (A : GenericExpr τ_c) := ∀ ⦃B⦄, r A B → False

def IsNorm'.elim (hn : IsNorm' r A) (hr : r A B) : A = B := (hn hr).elim

class ElimNorm (m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u) (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] where
  elim_norm (hn : IsNorm' r A) (h : m r A B) : A = B

open ElimNorm

@[grind]
def AndNorm (m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u) (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (A B : GenericExpr τ_c) :=
  m r A B × (PLift (IsNorm' r B))

@[grind]
def AndNorm.mk {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] (h : m r A B) (hn : IsNorm' r B) : AndNorm m r A B := ⟨h, ⟨hn⟩⟩

instance [∀ x y, Repr (r x y)] [∀ x y, Repr (m r x y)] : Repr (AndNorm m r A B) := ⟨fun ⟨x, _y⟩ prec => Repr.addAppParen s!"AndNorm.mk {reprPrec x prec} ⋯" prec⟩

@[grind]
def AndNorm.raw [∀ x y, Repr (r x y)] (h : AndNorm m r A B) : m r A B := match h with | ⟨hr, _⟩ => hr

def AndNorm.is_norm [∀ x y, Repr (r x y)] (h : AndNorm m r A B) : IsNorm' r B := match h with | ⟨_, ⟨hn⟩⟩ => hn

def AndNorm.ext {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)]
  {A B : GenericExpr τ_c} {h₁ : AndNorm m r A B} {h₂ : m r A B} {hn : IsNorm' r B} (heq₁ : h₁.raw = h₂) (heq₂ : h₁.is_norm = hn) : h₁ = (AndNorm.mk h₂ hn) :=
  match h₁ with
  | ⟨hr, hn⟩ => by
    cases heq₁; cases heq₂
    simp [mk, raw]

def AndNorm.ext_mpr {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)]
  {A B : GenericExpr τ_c} {h₁ h₂ : AndNorm m r A B} (heq : h₁ = h₂) : h₁.raw = h₂.raw ∧ h₁.is_norm = h₂.is_norm := by
  constructor <;> grind

@[grind, dcc_size]
def RedChoicePlus.length [∀ x y, Repr (r x y)] (h : RedChoicePlus r A B) : ℕ :=
  match h with
  | .single _ => 1
  | .head _ xs => xs.length.succ

@[grind, dcc_size]
def RedChoiceStar.length [∀ x y, Repr (r x y)] (h : RedChoiceStar r A B) : ℕ :=
  match h with
  | .refl => 0
  | .plus h => h.length

@[grind .]
theorem RedChoicePlus.length_pos [∀ x y, Repr (r x y)] (h : RedChoicePlus r A B) : 0 < h.length := by
  cases h <;> grind

instance RedChoicePlus.push_head [∀ x y, Repr (r x y)] : PushHead RedChoicePlus r := ⟨fun hrt hr => .trans (.single hr) hrt⟩
instance RedChoiceStar.push_head [∀ x y, Repr (r x y)] : PushHead RedChoiceStar r := ⟨fun hrt hr => .trans (.plus (.single hr)) hrt⟩

def RedChoicePlus.decreasing_impl [∀ x y, Repr (r x y)] [Decreasing r] (hrt : RedChoicePlus r A B) : size B < size A :=
  match hrt with
  | .single h => GenericExpr.decreasing h
  | .head hr hrt => by
    have h_dec₁ := GenericExpr.decreasing hr
    have h_dec₂ := decreasing_impl hrt
    grind

instance {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] [∀ x y, Repr (r x y)] : Decreasing (RedChoicePlus r) := ⟨RedChoicePlus.decreasing_impl⟩
instance {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] [∀ x y, Repr (r x y)] : Decreasing? (RedChoiceStar r) := ⟨fun h => match h with
  | .refl => by grind
  | .plus p => by have h := p.decreasing_impl; grind⟩

def RedChoicePlus.length_same {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] [Unique r] [ProofEq r] [∀ x y, Repr (r x y)] (h₁ h₂ : RedChoicePlus r A B) : h₁.length = h₂.length := by
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
def run_trans {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] [Run Option r] [Decreasing r] [Single m r] [Trans (m r) (m r) (m r)] (A : GenericExpr τ_c) : Option (Σ' B, m r A B) :=
  match run (m := Option) (r := r) A with
  | .some ⟨B, hr⟩ =>
    have h_dec := decreasing hr
    match B.run_trans (m := m) (r := r) with
    | .some ⟨C, hr'⟩ => .some ⟨_, trans (single (m := m) hr) hr'⟩
    | .none => .some ⟨_, single (by assumption)⟩
  | .none => .none
termination_by A.size

instance {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [Decreasing r] [Run Option r] [∀ x y, Repr (r x y)] : Run Option (RedChoicePlus r) := ⟨run_trans r⟩
instance {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] [Decreasing r] [Run Option r] [Single m r] [Trans (m r) (m r) (m r)] : Run Option (m r) := ⟨run_trans r⟩

instance CasesHead.elim_cast_higher [∀ x y, Repr (r x y)] [Trans (m r) (m r) (m r)] [Decreasing r] [Single m r] [CasesHead m r] : ElimNorm m r := ⟨fun {A B} hn h => by
  match cases_head h with
  | .inl ⟨h', heq⟩ => exact hn.elim h'
  | .inr ⟨_, h₁, h₂, heq'⟩ => cases hn.elim h₁; exact no_refl h₁⟩

def IsNorm'.down {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] [Single m r] (hn : IsNorm' (m r) A) : IsNorm' r A := fun _ h =>
  hn (single h)

def IsNorm'.up {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (hn : IsNorm' r A) : IsNorm' (m r) A := fun _ h =>
  match cases_head h with
  | .inl ⟨h, _⟩ => hn h
  | .inr ⟨_, h, _, _⟩ => hn h

open Unique

def normal_form_unique {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] [Decreasing r] [Unique r] [ProofEq r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (h₁ : AndNorm m r A B) (h₂ : AndNorm m r A C) : B = C := by
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

instance instUniqueNorm {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] [Decreasing r] [Unique r] [ProofEq r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] : Unique (AndNorm m r) := ⟨normal_form_unique⟩

def normal_proof_unique {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] [Decreasing r] [Decreasing (m r)] [Unique r] [ProofEq r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (h₁ h₂ : AndNorm m r A B) : h₁ = h₂ := by
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

instance instProofEqNorm {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] [Decreasing r] [Unique r] [ProofEq r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] [Decreasing (m r)] : ProofEq (AndNorm m r) := ⟨normal_proof_unique⟩

def cast_decreasing_up {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} [Decreasing r] [∀ x y, Repr (r x y)] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (h : m r A B) : B.size < A.size :=
  match cases_head h with
  | .inl ⟨hr, _heq⟩ => decreasing hr
  | .inr ⟨B, hr', hrt', heq'⟩ => by
    have h_dec₁ := decreasing hr'
    have h := cast_decreasing_up hrt'
    grind
termination_by A.size

instance Decreasing.instUp {m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u} [Decreasing r] [∀ x y, Repr (r x y)] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] : Decreasing (m r) := ⟨cast_decreasing_up⟩

open Run in
def reduce (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] [Run Option r] [Decreasing r] [Complete' (m := Option) r] (A : GenericExpr τ_c) : Σ' B, AndNorm RedChoiceStar r A B :=
  match heq : run (m := Option) (r := r) A with
  | .some ⟨B, hr⟩ =>
    have _h_dec := decreasing hr
    match B.reduce (r := r) with
    |  ⟨C, ⟨hr', ⟨hn⟩⟩⟩ => ⟨_, ⟨trans (single (m := RedChoiceStar) hr) hr', ⟨hn⟩⟩⟩
  | .none =>
    have hn : IsNorm' r A := none_sound heq
    ⟨_, ⟨.refl, ⟨hn⟩⟩⟩
termination_by A.size

open Run in
def reduce_plus (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] [Run Option r] [Decreasing r] [Complete' (m := Option) r] (A : GenericExpr τ_c) : Option (Σ' B, AndNorm RedChoicePlus r A B) :=
  match reduce r A with
  | ⟨_, ⟨hr, ⟨hn⟩⟩⟩ =>
    match hr with
    | .refl => .none
    | .plus hr => .some ⟨_, ⟨hr, ⟨hn⟩⟩⟩

instance [∀ x y, Repr (r x y)] [Run Option r] [Decreasing r] [Complete' (m := Option) r] : Run Id (AndNorm RedChoiceStar r) := ⟨reduce _⟩
instance [∀ x y, Repr (r x y)] [Run Option r] [Decreasing r] [Complete' (m := Option) r] : Run Option (AndNorm RedChoicePlus r) := ⟨reduce_plus _⟩

def get_head [∀ x y, Repr (r x y)] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (hr : m r A B) : Σ' B', r A B' :=
  match cases_head hr with
  | .inl ⟨h, _heq⟩ => ⟨_, h⟩
  | .inr ⟨_, h, _, _⟩ => ⟨_, h⟩

instance [∀ x y, Repr (r x y)] : ElimNorm RedChoicePlus r := ⟨fun hn hr => (hn (get_head hr).snd).elim⟩

instance [∀ x y, Repr (r x y)] : ElimNorm RedChoiceStar r := ⟨fun {_A B} hn hr => match hr with
  | .refl => rfl
  | .plus h => elim_norm hn h⟩

def RedChoiceStar.complete {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] [ProofEq r] [Unique r] [Decreasing r] [Run Option r] [Complete' (m := Option) r] (hr : AndNorm RedChoiceStar r A B) : reduce _ A = ⟨B, hr⟩ := by
  unfold reduce
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

instance RedChoiceStar.instComplete {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] [ProofEq r] [Unique r] [Decreasing r] [Run Option r] [Complete' (m := Option) r] : Complete' (m := Id) (AndNorm RedChoiceStar r) := ⟨RedChoiceStar.complete⟩

instance RedChoicePlus.instComplete {r : GenericExpr τ_c → GenericExpr τ_c → Type u} [∀ x y, Repr (r x y)] [ProofEq r] [Unique r] [Decreasing r] [Run Option r] [Complete' (m := Option) r] : Complete' (m := Option) (AndNorm RedChoicePlus r) := ⟨by
  intro A B ⟨h, ⟨hn⟩⟩
  dcc_simp (! !)
  unfold reduce_plus
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
      have heq_fst : fst = fst_1 := by
        cases heq'
        rfl
      cases heq_fst
      have heq'' := unique (AndNorm.mk h (by assumption)) (AndNorm.mk hr_1 (by assumption))
      dcc_simp_all (! !)
      change AndNorm.mk _ _ ≍ AndNorm.mk _ _
      apply proof_heq⟩

instance RedChoicePlus.elim_norm [∀ x y, Repr (r x y)] : ElimNorm RedChoicePlus r := ⟨fun hn hrt =>
  match hrt with
  | .single hr => (hn hr).elim
  | .head hrt₁ hrt₂ => (hn (by assumption)).elim⟩

open Unique in
open ReflT in
def conf
  {r : GenericExpr τ_c → GenericExpr τ_c → Type u}
  [∀ x y, Repr (r x y)]
  (m : ∀ (r : GenericExpr τ_c → GenericExpr τ_c → Type u) [∀ x y, Repr (r x y)] (_A _B : GenericExpr τ_c), Type u)
  [ReflT m r]
  [Unique r]
  (h₁ : r A B) (h₂ : r A C) : Σ' D, m r B D × m r C D :=
  ⟨_, unique h₁ h₂ ▸ ReflT.refl, ReflT.refl⟩

open Unique in
open ReflT in
def conf_global
  {r : GenericExpr τ_c → GenericExpr τ_c → Type u}
  [∀ x y, Repr (r x y)]
  [Unique r]
  [Decreasing r]
  (h₁ : RedChoiceStar r A B) (h₂ : RedChoiceStar r A C) : Σ' D, RedChoiceStar r B D × RedChoiceStar r C D :=
  match h₁, h₂ with
  | .refl, .refl => ⟨_, .refl, .refl⟩
  | .plus h₁, .refl =>
    ⟨_, .refl, .plus h₁⟩
  | .refl, .plus h₁ =>
    ⟨_, .plus h₁, .refl⟩
  | .plus h₁, .plus h₂ =>
    have h_dec₁ := decreasing h₁
    have h_dec₂ := decreasing h₂
    match cases_head h₁, cases_head h₂ with
    | .inl ⟨hr₁, heq₁⟩, .inl ⟨hr₂, heq₂⟩ =>
      ⟨_, unique hr₁ hr₂ ▸ .refl, .refl⟩
    | .inr ⟨_, hr₁, hrt'₁, heq₁⟩, .inl ⟨hr₂, heq₂⟩ => by
      cases unique hr₁ hr₂
      exact ⟨_,  .refl, .plus hrt'₁⟩
    | .inl ⟨hr₂, heq₂⟩, .inr ⟨_, hr₁, hrt'₁, heq₁⟩ => by
      cases unique hr₁ hr₂
      exact ⟨_,  .plus hrt'₁, .refl⟩
    | .inr ⟨_, hr₁, hrt'₁, heq₁⟩, .inr ⟨_, hr₂, hrt'₂, heq₂⟩ => by
      cases unique hr₁ hr₂
      have h_dec := decreasing hr₁
      exact conf_global (.plus hrt'₁) (.plus hrt'₂)
termination_by A.size

end GenericExpr
