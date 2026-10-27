import Dcc.Ast.Format
import Dcc.Red.Size
import Dcc.Attrs

namespace Expr

class Decreasing? (r : Expr → Expr → Sort v) where
  decreasing?' : ∀ (_h : r A B), B.size ≤ A.size

class ReflT (m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u) (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] where
  refl : m r A A

class Decreasing (r : Expr → Expr → Sort v) where
  decreasing : ∀ (_h : r A B), B.size < A.size

def no_refl [hD : Decreasing r] (h : r A A := by assumption) : False := by
  have h := hD.decreasing h
  grind

class Run (m : Type u → Type u) (r : Expr → Expr → Type u) where
  run : ∀ (A : Expr), m (Σ' (B : Expr), r A B)

class Unique (r : Expr → Expr → Sort v) where
  unique : ∀ ⦃B C⦄, r A B → r A C → B = C

class ProofEq (r : Expr → Expr → Sort v) where
  eq : ∀ (h₁ h₂ : r A B), h₁ = h₂

class Single (m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u) (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] where
  single (h : r A B) : m r A B

open Single

open Trans in
class CasesHead (m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u) (r : Expr → Expr → Type u)
  [∀ x y, Repr (r x y)] [hP : Single m r] [Trans (m r) (m r) (m r)] where
  cases_head (h : m r A C) : (Σ' (h' : r A C), h = single h') ⊕ (Σ' (B : Expr) (hr' : r A B) (hrt' : m r B C), h = Trans.trans (hP.single hr') hrt')

attribute [dcc_force_rel] CasesHead.cases_head
attribute [dcc_rel] Single.single Single.single.eq_def
attribute [grind] Single.single
attribute [grind =] Single.single.eq_def

class PushHead (m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u) (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] where
  push_head (hrt : m r A C) (hr : r A B) : m r B C

class PopHead (m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u) (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] where
  pop_head (hr : r A B) (hrt : m r B C) : m r A C

open CasesHead
open PushHead

def proof_eq {r : Expr → Expr → Sort v} [hP : ProofEq r] (h₁ h₂ : r A B) : h₁ = h₂ := hP.eq h₁ h₂

def unique {r : Expr → Expr → Sort v} [hP : Unique r] (h₁ : r A B) (h₂ : r A C) : B = C := hP.unique h₁ h₂

def proof_heq {r : Expr → Expr → Sort v} [hP : ProofEq r] [hU : Unique r] (h₁ : r A B) (h₂ : r A C) : h₁ ≍ h₂ := by
  let heq := unique h₁ h₂
  let hb := proof_eq (heq ▸ h₁) (heq ▸ h₂)
  grind

attribute [dcc_force_reduce] Run.run
attribute [grind =] Run.run.eq_def
attribute [grind] Run.run
attribute [dcc_size] Decreasing.decreasing

attribute [dcc_force_rel] Run.run Run.run.eq_def Single.single

open Decreasing Run

def run_sound {r : Expr → Expr → Type u} [hD : Run m r] [Pure m] {h : r A B} (_heq : hD.run A = Pure.pure ⟨B, h⟩) : r A B := h

class Complete' (m : outParam (Type u → Type u)) (r : Expr → Expr → Type u) [Run m r] [hp : Pure m] where
  complete : ∀ (h : r A B), Run.run (m := m) A = pure ⟨B, h⟩

open Complete'

def none_complete {r : Expr → Expr → Type u} [Run Option r] [Complete' (m := Option) r] {A : Expr} (hn : ∀ ⦃B⦄, r A B → False) : run (m := Option) (r := r) A = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨B, hr⟩
  exact (hn hr).elim

def none_sound {r : Expr → Expr → Type u} [Run Option r] [Complete' (m := Option) r] {A : Expr} (heq : run (m := Option) (r := r) A = .none) : ∀ ⦃B⦄, r A B → False := fun ⦃B⦄ h => by
  have heq := complete (m := Option) h
  grind

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def complete {r : Expr → Expr → Type u} [Run M r] [Pure M] [hD : Complete' (m := M) r] (h : r A B) : run (m := M) A = Pure.pure ⟨B, h⟩ := hD.complete h

theorem decreasing [hD : Decreasing r] (h : r A B := by assumption) : size B < size A := hD.decreasing h

/-
Deterministic path version of Relation.TransGen.
-/
inductive RedChoicePlus (r : Expr → Expr → Type u) [∀ A B, Repr (r A B)] : Expr → Expr → Type u
  | single : (hr : r A B) → RedChoicePlus r A B
  | head   : (hr : r A B) → (hrt₂ : RedChoicePlus r B C) → RedChoicePlus r A C
deriving Repr

inductive RedChoiceStar (r : Expr → Expr → Type u) [∀ A B, Repr (r A B)] : Expr → Expr → Type u
  | head : (hr : r A B) → (hrt₂ : RedChoiceStar r B C) → RedChoiceStar r A C
  | refl : RedChoiceStar r A A
deriving Repr

instance [∀ x y, Repr (r x y)] : ReflT RedChoiceStar r := ⟨.refl⟩

instance RedChoicePlus.instSingle {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] : Single RedChoicePlus r := ⟨.single⟩
instance RedChoiceStar.instSingle {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] : Single RedChoiceStar r := ⟨(.head · .refl)⟩

@[dcc_force_rel]
def RedChoicePlus.trans [∀ x y, Repr (r x y)] (hr₁ : RedChoicePlus r A B) (hr₂ : RedChoicePlus r B C) : RedChoicePlus r A C :=
  match hr₁ with
  | .single h => .head h (by assumption)
  | .head a c => .head a (trans (by assumption) (by assumption))

instance RedChoicePlus.instTrans [∀ x y, Repr (r x y)] : Trans (RedChoicePlus r) (RedChoicePlus r) (RedChoicePlus r) := ⟨RedChoicePlus.trans⟩
instance RedChoicePlus.instTrans' [∀ x y, Repr (r x y)] : Trans r (RedChoicePlus r) (RedChoicePlus r) := ⟨fun h₁ h₂ => RedChoicePlus.trans (single h₁) h₂⟩

@[dcc_force_rel]
def RedChoiceStar.trans [∀ x y, Repr (r x y)] (hr₁ : RedChoiceStar r A B) (hr₂ : RedChoiceStar r B C) : RedChoiceStar r A C :=
  match hr₁ with
  | .refl => hr₂
  | .head hr hrt => .head hr (hrt.trans hr₂)

instance RedChoiceStar.instTrans [∀ x y, Repr (r x y)] : Trans (RedChoiceStar r) (RedChoiceStar r) (RedChoiceStar r) := ⟨RedChoiceStar.trans⟩
instance RedChoiceStar.instTrans' [∀ x y, Repr (r x y)] : Trans r (RedChoiceStar r) (RedChoiceStar r) := ⟨RedChoiceStar.head⟩

attribute [dcc_force_rel] Trans.trans Trans.trans.eq_def

instance RedChoicePlus.instCasesHead {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] : CasesHead (r := r) (m := RedChoicePlus) := ⟨fun hrt => match heq : hrt with
  | .single h => .inl ⟨h, rfl⟩
  | .head hr hrt => .inr ⟨_, hr, hrt, by dcc_simp_all (! !)⟩⟩

@[grind]
def IsNorm' (r : Expr → Expr → Type u) (A : Expr) := ∀ ⦃B⦄, r A B → False

def IsNorm'.elim (hn : IsNorm' r A) (hr : r A B) : A = B := (hn hr).elim

class ElimNorm (m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u) (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] where
  elim_norm (hn : IsNorm' r A) (h : m r A B) : A = B

open ElimNorm

@[grind]
def AndNorm (m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u) (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (A B : Expr) :=
  m r A B × (PLift (IsNorm' r B))

@[grind]
def AndNorm.mk {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] (h : m r A B) (hn : IsNorm' r B) : AndNorm m r A B := ⟨h, ⟨hn⟩⟩

instance [∀ x y, Repr (r x y)] [∀ x y, Repr (m r x y)] : Repr (AndNorm m r A B) := ⟨fun ⟨x, _y⟩ prec => Repr.addAppParen s!"AndNorm.mk {reprPrec x prec} ⋯" prec⟩

@[grind]
def AndNorm.raw [∀ x y, Repr (r x y)] (h : AndNorm m r A B) : m r A B := match h with | ⟨hr, _⟩ => hr

def AndNorm.is_norm [∀ x y, Repr (r x y)] (h : AndNorm m r A B) : IsNorm' r B := match h with | ⟨_, ⟨hn⟩⟩ => hn

def AndNorm.ext {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)]
  {A B : Expr} {h₁ : AndNorm m r A B} {h₂ : m r A B} {hn : IsNorm' r B} (heq₁ : h₁.raw = h₂) (heq₂ : h₁.is_norm = hn) : h₁ = (AndNorm.mk h₂ hn) :=
  match h₁ with
  | ⟨hr, hn⟩ => by
    cases heq₁; cases heq₂
    simp [mk, raw]

def AndNorm.ext_mpr {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)]
  {A B : Expr} {h₁ h₂ : AndNorm m r A B} (heq : h₁ = h₂) : h₁.raw = h₂.raw ∧ h₁.is_norm = h₂.is_norm := by
  constructor <;> grind

@[grind, dcc_size]
def RedChoicePlus.length [∀ x y, Repr (r x y)] (h : RedChoicePlus r A B) : ℕ :=
  match h with
  | .single _ => 1
  | .head _ xs => xs.length.succ

def RedChoiceStar.single [∀ x y, Repr (r x y)] (hr : r A B) : RedChoiceStar r A B := .head hr .refl

@[grind, dcc_size]
def RedChoiceStar.length [∀ x y, Repr (r x y)] (h : RedChoiceStar r A B) : ℕ :=
  match h with
  | .refl => 0
  | .head _h hrt => hrt.length.succ

@[grind .]
theorem RedChoicePlus.length_pos [∀ x y, Repr (r x y)] (h : RedChoicePlus r A B) : 0 < h.length := by
  cases h <;> grind

def RedChoicePlus.decreasing_impl [∀ x y, Repr (r x y)] [Decreasing r] (hrt : RedChoicePlus r A B) : size B < size A :=
  match hrt with
  | .single h => Expr.decreasing h
  | .head hr hrt => by
    have h_dec₁ := Expr.decreasing hr
    have h_dec₂ := decreasing_impl hrt
    grind

instance {r : Expr → Expr → Type u} [Decreasing r] [∀ x y, Repr (r x y)] : Decreasing (RedChoicePlus r) := ⟨RedChoicePlus.decreasing_impl⟩
instance {r : Expr → Expr → Type u} [Decreasing r] [∀ x y, Repr (r x y)] : Decreasing? (RedChoiceStar r) := ⟨fun h => by
  induction h with
  | refl => grind
  | head h hrt =>
    have h_dec := decreasing h
    grind⟩

def RedChoicePlus.length_same {r : Expr → Expr → Type u} [Decreasing r] [Unique r] [ProofEq r] [∀ x y, Repr (r x y)] (h₁ h₂ : RedChoicePlus r A B) : h₁.length = h₂.length := by
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
def run_trans {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] [Run Option r] [Decreasing r] [Single m r] [Trans (m r) (m r) (m r)] (A : Expr) : Option (Σ' B, m r A B) :=
  match run (m := Option) (r := r) A with
  | .some ⟨B, hr⟩ =>
    have h_dec := decreasing hr
    match B.run_trans (m := m) (r := r) with
    | .some ⟨C, hr'⟩ => .some ⟨_, trans (single (m := m) hr) hr'⟩
    | .none => .some ⟨_, single (by assumption)⟩
  | .none => .none
termination_by A.size

instance {r : Expr → Expr → Type u} [Decreasing r] [Run Option r] [∀ x y, Repr (r x y)] : Run Option (RedChoicePlus r) := ⟨run_trans r⟩
instance {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] [Decreasing r] [Run Option r] [Single m r] [Trans (m r) (m r) (m r)] : Run Option (m r) := ⟨run_trans r⟩

instance CasesHead.elim_cast_higher [∀ x y, Repr (r x y)] [Trans (m r) (m r) (m r)] [Decreasing r] [Single m r] [CasesHead m r] : ElimNorm m r := ⟨fun {A B} hn h => by
  match cases_head h with
  | .inl ⟨h', heq⟩ => exact hn.elim h'
  | .inr ⟨_, h₁, h₂, heq'⟩ => cases hn.elim h₁; exact (no_refl h₁).elim⟩

def IsNorm'.down {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] [Single m r] (hn : IsNorm' (m r) A) : IsNorm' r A := fun _ h =>
  hn (single h)

def IsNorm'.up {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (hn : IsNorm' r A) : IsNorm' (m r) A := fun _ h =>
  match cases_head h with
  | .inl ⟨h, _⟩ => hn h
  | .inr ⟨_, h, _, _⟩ => hn h

open Unique

def normal_form_unique {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] [Decreasing r] [Unique r] [ProofEq r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (h₁ : AndNorm m r A B) (h₂ : AndNorm m r A C) : B = C := by
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

instance instUniqueNorm {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] [Decreasing r] [Unique r] [ProofEq r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] : Unique (AndNorm m r) := ⟨normal_form_unique⟩

def normal_proof_unique {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] [Decreasing r] [Decreasing (m r)] [Unique r] [ProofEq r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (h₁ h₂ : AndNorm m r A B) : h₁ = h₂ := by
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
    exact (no_refl hrt₁).elim
  | .inl ⟨hr₁, heq₁⟩, .inr ⟨_, hr₂, hrt₂, heq₂⟩ =>
    have hn₁ := h₁.is_norm
    have hn₂ := h₂.is_norm
    cases unique hr₁ hr₂
    exact (no_refl hrt₂).elim
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

instance instProofEqNorm {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] [Decreasing r] [Unique r] [ProofEq r] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] [Decreasing (m r)] : ProofEq (AndNorm m r) := ⟨normal_proof_unique⟩

def cast_decreasing_up {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} [Decreasing r] [∀ x y, Repr (r x y)] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (h : m r A B) : B.size < A.size :=
  match cases_head h with
  | .inl ⟨hr, _heq⟩ => decreasing hr
  | .inr ⟨B, hr', hrt', heq'⟩ => by
    have h_dec₁ := decreasing hr'
    have h := cast_decreasing_up hrt'
    grind
termination_by A.size

instance Decreasing.instUp {m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u} [Decreasing r] [∀ x y, Repr (r x y)] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] : Decreasing (m r) := ⟨cast_decreasing_up⟩

open Run in
def reduce (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] [Run Option r] [Decreasing r] [Complete' (m := Option) r] (A : Expr) : Σ' B, AndNorm RedChoiceStar r A B :=
  match heq : run (m := Option) (r := r) A with
  | .some ⟨B, hr⟩ =>
    have _h_dec := decreasing hr
    match B.reduce (r := r) with
    |  ⟨C, ⟨hr', ⟨hn⟩⟩⟩ => ⟨_, ⟨trans (single (m := RedChoiceStar) hr) hr', ⟨hn⟩⟩⟩
  | .none =>
    have hn : IsNorm' r A := none_sound heq
    ⟨_, ⟨.refl, ⟨hn⟩⟩⟩
termination_by A.size

/-open Run in
def reduce_plus (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] [Run Option r] [Decreasing r] [Complete' (m := Option) r] (A : Expr) : Option (Σ' B, AndNorm RedChoicePlus r A B) :=
  match reduce r A with
  | ⟨_, ⟨hr, ⟨hn⟩⟩⟩ =>
    match hr with
    | .refl => .none
    | .plus hr => .some ⟨_, ⟨hr, ⟨hn⟩⟩⟩-/

instance [∀ x y, Repr (r x y)] [Run Option r] [Decreasing r] [Complete' (m := Option) r] : Run Id (AndNorm RedChoiceStar r) := ⟨reduce _⟩
--instance [∀ x y, Repr (r x y)] [Run Option r] [Decreasing r] [Complete' (m := Option) r] : Run Option (AndNorm RedChoicePlus r) := ⟨reduce_plus _⟩

def get_head [∀ x y, Repr (r x y)] [Single m r] [Trans (m r) (m r) (m r)] [CasesHead m r] (hr : m r A B) : Σ' B', r A B' :=
  match cases_head hr with
  | .inl ⟨h, _heq⟩ => ⟨_, h⟩
  | .inr ⟨_, h, _, _⟩ => ⟨_, h⟩

instance [∀ x y, Repr (r x y)] : ElimNorm RedChoicePlus r := ⟨fun hn hr => (hn (get_head hr).snd).elim⟩

instance [∀ x y, Repr (r x y)] : ElimNorm RedChoiceStar r := ⟨fun {_A B} hn hr => by
  induction hr with
  | head =>
    expose_names
    cases hn.elim hr
    exact hrt₂_ih hn
  | refl => rfl⟩

def RedChoiceStar.complete {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] [ProofEq r] [Unique r] [Decreasing r] [Run Option r] [Complete' (m := Option) r] (hr : AndNorm RedChoiceStar r A B) : reduce _ A = ⟨B, hr⟩ := by
  match hr with
  | ⟨hr, ⟨hn⟩⟩ =>
    induction hr with
    | head =>
      unfold reduce
      expose_names
      have h := Complete'.complete hr_1
      split
      case h_1 =>
        expose_names
        cases unique hr_1 hr_2
        simp
        have heq' := hrt₂_ih (AndNorm.mk hrt₂ hn) hn
        split
        case h_1 heq'' =>
          cases heq''.symm.trans heq'
          simp [Trans.trans, trans]
          cases proof_eq hr_1 hr_2
          rfl
      case h_2 =>
        expose_names
        have heq' := hrt₂_ih (AndNorm.mk hrt₂ hn) hn
        simp_all
    | refl =>
      expose_names
      unfold reduce
      split
      case h_1 =>
        expose_names
        cases hn.elim hr_1
        simp
        exact (Expr.no_refl hr_1).elim
      simp

instance RedChoiceStar.instComplete {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] [ProofEq r] [Unique r] [Decreasing r] [Run Option r] [Complete' (m := Option) r] : Complete' (m := Id) (AndNorm RedChoiceStar r) := ⟨RedChoiceStar.complete⟩

/-instance RedChoicePlus.instComplete {r : Expr → Expr → Type u} [∀ x y, Repr (r x y)] [ProofEq r] [Unique r] [Decreasing r] [Run Option r] [Complete' (m := Option) r] : Complete' (m := Option) (AndNorm RedChoicePlus r) := ⟨by
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
      apply proof_heq⟩-/

instance RedChoicePlus.elim_norm [∀ x y, Repr (r x y)] : ElimNorm RedChoicePlus r := ⟨fun hn hrt =>
  match hrt with
  | .single hr => (hn hr).elim
  | .head hrt₁ hrt₂ => (hn (by assumption)).elim⟩

open Unique in
open ReflT in
def conf
  {r : Expr → Expr → Type u}
  [∀ x y, Repr (r x y)]
  (m : ∀ (r : Expr → Expr → Type u) [∀ x y, Repr (r x y)] (_A _B : Expr), Type u)
  [ReflT m r]
  [Unique r]
  (h₁ : r A B) (h₂ : r A C) : Σ' D, m r B D × m r C D :=
  ⟨_, unique h₁ h₂ ▸ ReflT.refl, ReflT.refl⟩

open Unique in
open ReflT in
def conf_global
  {r : Expr → Expr → Type u}
  [∀ x y, Repr (r x y)]
  [Unique r]
  [Decreasing r]
  (h₁ : RedChoiceStar r A B) (h₂ : RedChoiceStar r A C) : Σ' D, RedChoiceStar r B D × RedChoiceStar r C D :=
  match h₁, h₂ with
  | .refl, .refl => ⟨_, .refl, .refl⟩
  | .head h₁ hrt, .refl =>
    ⟨_, .refl, .head h₁ (by assumption)⟩
  | .refl, .head h₁ hrt =>
    ⟨_, .head h₁ (by assumption), .refl⟩
  | .head h₁ hrt₁, .head h₂ hrt₂ => by
    have h_dec₁ := decreasing h₁
    have h_dec₂ := decreasing h₂
    cases unique h₁ h₂
    have ⟨C, h₁, h₂⟩ := conf_global hrt₁ hrt₂
    exact ⟨_, h₁, h₂⟩

instance AndNorm.instPushHead [∀ x y, Repr (r x y)] [Unique r] : PushHead (AndNorm RedChoiceStar) r := ⟨fun ⟨hrt, ⟨hn⟩⟩ hr => by
  cases hrt with
  | refl =>
    cases hn.elim hr
    exact ⟨.refl, ⟨hn⟩⟩
  | head hr hrt =>
    expose_names
    cases unique hr_1 hr
    apply AndNorm.mk <;> assumption⟩

open Trans in
instance AndNorm.instPopHead [∀ x y, Repr (r x y)] [Unique r] : PopHead (AndNorm RedChoiceStar) r := ⟨fun hr ⟨hrt, ⟨hn⟩⟩ =>
  match hrt with
  | .refl => ⟨.single hr, ⟨hn⟩⟩
  | .head hr₀ hrt => ⟨.trans (.single (by assumption)) (by
    expose_names
    exact x_1.raw), ⟨by assumption⟩⟩⟩

instance AndNorm.instElim₁ [∀ x y, Repr (r x y)] : ElimNorm (AndNorm RedChoiceStar) r := ⟨fun hn ⟨hrt, hn⟩ => elim_norm (by assumption) hrt⟩
instance AndNorm.instElim₂ [∀ x y, Repr (r x y)] : ElimNorm (AndNorm RedChoicePlus) r := ⟨fun hn ⟨hrt, hn⟩ => elim_norm (by assumption) hrt⟩

instance [Run Option r] [Complete' Option r] : Unique r := ⟨fun h₁ h₂ => by
  have heq₁ := complete h₁
  have heq₂ := complete h₂
  have heq₃ := heq₂.symm.trans heq₁
  grind⟩

instance [Run Id r] [Complete' Id r] : Unique r := ⟨fun h₁ h₂ => by
  have heq₁ := complete h₁
  have heq₂ := complete h₂
  have heq₃ := heq₂.symm.trans heq₁
  simp [Pure.pure] at heq₃
  grind⟩

instance [Run Option r] [Complete' Option r] : ProofEq r := ⟨fun h₁ h₂ => by
  have heq₁ := complete h₁
  have heq₂ := complete h₂
  have heq₃ := heq₂.symm.trans heq₁
  grind⟩

instance [Run Id r] [Complete' Id r] : ProofEq r := ⟨fun h₁ h₂ => by
  have heq₁ := complete h₁
  have heq₂ := complete h₂
  have heq₃ := heq₂.symm.trans heq₁
  simp [Pure.pure] at heq₃
  grind⟩

@[dcc_force_reduce, aesop safe forward (rule_sets := [DccReduce])]
def complete_fst [hR : Run Id r] [Complete' Id r] (h : r A B) (heqr : hR.run = run_def := by simp [Run.run]; try rfl) : (run_def A).fst = B := by
  cases heqr
  have h := complete h
  simp [Pure.pure] at h
  grind

def reduce_norm_fst [Run Option r] [Decreasing r] [Complete' Option r] [∀ x y, Repr (r x y)] : IsNorm' r (reduce r x).fst := (reduce r x).snd.is_norm

open PopHead in
def reduce_self [Run Option r] [Decreasing r] [Complete' Option r] [∀ x y, Repr (r x y)] (h : r A B) : (reduce r A).fst = (reduce r B).fst := complete_fst (pop_head h (reduce r B).snd)

def complete' [hR : Run m r] [hP : Pure m] [Complete' m r] (h : r A B)
  (heqr : hR.run = run_def := by simp [Run.run]; try rfl) (heqp : hP.pure = pure_def := by simp [Pure.pure]; try rfl) : (run_def A) = pure_def ⟨B, h⟩ := by
  cases heqr; cases heqp
  exact complete (by assumption)

end Expr
