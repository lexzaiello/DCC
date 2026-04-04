import Dcc.CC.Ast
import Mathlib.Tactic

namespace Expr

inductive IsRedex : Expr → Prop
  | app    : IsRedex (DCC (App(_δ, _τ) ⟦β⟧(a, b)))
  | fst    : IsRedex (DCC (Fst(_δ, _τ) ⟦β⟧(a, b)))
  | snd    : IsRedex (DCC (Snd(_δ, _τ) ⟦β⟧(a, b)))
  | id     : IsRedex (DCC (Id(_α) x))
  | quot   : IsRedex (DCC (`(α, β, x) y))
  | comp   : IsRedex (DCC ((x ∘ y) z))
  | pair   : IsRedex (DCC (⟦β⟧⟨f, g⟩ x))
  | curr   : IsRedex (DCC (Λ(β, x) y z))

inductive HasRedex : Expr → Prop
  | single : IsRedex a  → HasRedex a
  | left   : HasRedex f → HasRedex (DCC (f x))
  | right  : HasRedex x → HasRedex (DCC (f x))
  | coupl  : HasRedex a → HasRedex (DCC ⟦β⟧(a, b))
  | coupr  : HasRedex b → HasRedex (DCC ⟦β⟧(a, b))
  | coupβ  : HasRedex β → HasRedex (DCC ⟦β⟧(a, b))
  | pairl  : HasRedex a → HasRedex (DCC ⟦β⟧⟨a, b⟩)
  | pairr  : HasRedex b → HasRedex (DCC ⟦β⟧⟨a, b⟩)
  | pairβ  : HasRedex β → HasRedex (DCC ⟦β⟧⟨a, b⟩)
  | app₁   : HasRedex δ → HasRedex (DCC App(δ, _τ))
  | app₂   : HasRedex τ → HasRedex (DCC App(_δ, τ))
  | fst₁   : HasRedex α → HasRedex (DCC Fst(α, _β))
  | fst₂   : HasRedex β → HasRedex (DCC Fst(_α, β))
  | snd₁   : HasRedex α → HasRedex (DCC Snd(α, _β))
  | snd₂   : HasRedex β → HasRedex (DCC Snd(_α, β))
  | id     : HasRedex α → HasRedex (DCC Id(α))
  | quot₁  : HasRedex α → HasRedex (DCC `(α, _β, _x))
  | quot₂  : HasRedex β → HasRedex (DCC `(_α, β, _x))
  | quot₃  : HasRedex x → HasRedex (DCC `(_α, _β, x))
  | comp₁  : HasRedex f → HasRedex (DCC (f ∘ _g))
  | comp₂  : HasRedex g → HasRedex (DCC (_f ∘ g))
  | sigα   : HasRedex α → HasRedex (DCC (Σ(α, _β)))
  | sigβ   : HasRedex β → HasRedex (DCC (Σ(_α, β)))
  | curr₁  : HasRedex β → HasRedex (DCC (Λ(β, _x)))
  | curr₂  : HasRedex x → HasRedex (DCC (Λ(_β, x)))

def is_redex (e : Expr) : Option (PLift e.IsRedex) :=
  match e with
  | (DCC (App(_δ, _τ) ⟦_β⟧(_a, _b))) => .some ⟨.app⟩
  | (DCC (Fst(_δ, _τ) ⟦_β⟧(_a, _b))) => .some ⟨.fst⟩
  | (DCC (Snd(_δ, _τ) ⟦_β⟧(_a, _b))) => .some ⟨.snd⟩
  | (DCC (Id(_α) _x))                => .some ⟨.id⟩
  | (DCC (`(_α, _β, _x) _y))         => .some ⟨.quot⟩
  | (DCC ((_x ∘ _y) _z))             => .some ⟨.comp⟩
  | (DCC (⟦_β⟧⟨_f, _g⟩ _x))          => .some ⟨.pair⟩
  | (DCC (Λ(_β, _x) _y _z))          => .some ⟨.curr⟩
  | _                                => .none

@[simp] theorem IsRedex.sound (_h : Expr.is_redex e = .some he) : IsRedex e := he.down

theorem IsRedex.complete (h : IsRedex e) : is_redex e = .some (.up h) := by
  match h with
  | .quot | .id | .snd | .fst | .comp | .curr | .app | .pair =>
    simp only [is_redex]

theorem IsRedex.sound' (_h : is_redex e = .none) : ¬ IsRedex e := fun h => by
  have h := h.complete
  simp_all only [reduceCtorEq]

instance IsRedex.instDecidable : Decidable (IsRedex e) :=
  if h : e.is_redex.isSome then
    .isTrue (e.is_redex.get h).down
  else
    .isFalse (fun h => absurd h (IsRedex.sound' (by simp_all only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none])))

def has_redex (e : Expr) : Option (PLift e.HasRedex) :=
  if h : IsRedex e then
    .some ⟨.single h⟩
  else
    match e with
    | (DCC ⟦β⟧(x, y)) => match _heq₁ : β.has_redex, _heq₂ : x.has_redex, _heq₃ : y.has_redex with
      | .some ⟨h⟩, _, _ => .some ⟨.coupβ h⟩
      | _, .some ⟨h⟩, _ => .some ⟨.coupl h⟩
      | _, _, .some ⟨h⟩ => .some ⟨.coupr h⟩
      | _, _, _ => .none
    | (DCC ⟦β⟧⟨x, y⟩) => match _heq₁ : β.has_redex, _heq₂ : x.has_redex, _heq₃ : y.has_redex with
      | .some ⟨h⟩, _, _ => .some ⟨.pairβ h⟩
      | _, .some ⟨h⟩, _ => .some ⟨.pairl h⟩
      | _, _, .some ⟨h⟩ => .some ⟨.pairr h⟩
      | _, _, _ => .none
    | (DCC App(δ, τ)) => match _heq₁ : δ.has_redex, _heq₂ : τ.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.app₁ h⟩
      | _, .some ⟨h⟩ => .some ⟨.app₂ h⟩
      | _, _ => .none
    | (DCC Fst(α, β)) => match _heq₁ : α.has_redex, _heq₂ : β.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.fst₁ h⟩
      | _, .some ⟨h⟩ => .some ⟨.fst₂ h⟩
      | _, _ => .none
    | (DCC Snd(α, β)) => match _heq₁ : α.has_redex, _heq₂ : β.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.snd₁ h⟩
      | _, .some ⟨h⟩ => .some ⟨.snd₂ h⟩
      | _, _ => .none
    | (DCC Id(α)) => match _heq₁ : α.has_redex with
      | .some ⟨h⟩ => .some ⟨.id h⟩
      | _ => .none
    | (DCC `(α, β, x)) => match _heq₁ : α.has_redex, _heq₂ : β.has_redex, _heq₃ : x.has_redex with
      | .some ⟨h⟩, _, _ => .some ⟨.quot₁ h⟩
      | _, .some ⟨h⟩, _ => .some ⟨.quot₂ h⟩
      | _, _, .some ⟨h⟩ => .some ⟨.quot₃ h⟩
      | _, _, _ => none
    | (DCC f ∘ g) => match _heq₁ : f.has_redex, _heq₂ : g.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.comp₁ h⟩
      | _, .some ⟨h⟩ => .some ⟨.comp₂ h⟩
      | _, _ => .none
    | (DCC Σ(α, β)) => match _heq₁ : α.has_redex, _heq₂ : β.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.sigα h⟩
      | _, .some ⟨h⟩ => .some ⟨.sigβ h⟩
      | _, _ => .none
    | (DCC Λ(β, x)) => match _heq₁ : β.has_redex, _heq₂ : x.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.curr₁ h⟩
      | _, .some ⟨h⟩ => .some ⟨.curr₂ h⟩
      | _, _ => .none
    | (DCC (f x)) => match _heq₂ : f.has_redex, _heq₃ : x.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.left h⟩
      | _, .some ⟨h⟩ => .some ⟨.right h⟩
      | _, _ => .none
    | _e => .none

@[simp] theorem HasRedex.sound (_h : Expr.has_redex e = .some he) : HasRedex e := he.down

@[simp] theorem sig_not_redex : ¬ IsRedex (DCC Σ(_α, _β)) := fun h => by
  cases h

@[simp] theorem curr_not_redex : ¬ IsRedex (DCC Λ(_β, x)) := fun h => by
  cases h

@[simp] theorem coupl_not_redex : ¬ IsRedex (DCC ⟦_β⟧(_a, _b)) := fun h => by
  cases h

@[simp] theorem pair_not_redex : ¬ IsRedex (DCC ⟦_β⟧⟨_a, _b⟩) := fun h => by
  cases h

@[simp] theorem app_not_redex : ¬ IsRedex (DCC App(_α, _β)) := fun h => by
  cases h

@[simp] theorem fst_not_redex : ¬ IsRedex (DCC Fst(_α, _β)) := fun h => by
  cases h

@[simp] theorem id_not_redex : ¬ IsRedex (DCC Id(_α)) := fun h => by
  cases h

@[simp] theorem snd_not_redex : ¬ IsRedex (DCC Snd(_α, _β)) := fun h => by
  cases h

@[simp] theorem quot_not_redex : ¬ IsRedex (DCC `(_α, _β, _x)) := fun h => by
  cases h

@[simp] theorem comp_not_redex : ¬ IsRedex (DCC (f ∘ g)) := fun h => by
  cases h

theorem HasRedex.complete (h : HasRedex e) : has_redex e = .some (.up h) := by
  induction h with
  | single h =>
    unfold has_redex
    simp only [h, ↓reduceDIte]
  | coupr h_redex h_redex_eq =>
    unfold has_redex
    simp only [coupl_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | pairr h_redex h_redex_eq =>
    unfold has_redex
    simp only [pair_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | coupl h_redex h_redex_eq =>
    unfold has_redex
    simp only [coupl_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | pairl h_redex h_redex_eq =>
    unfold has_redex
    simp only [pair_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | coupβ h_redex h_redex_eq =>
    unfold has_redex
    simp only [coupl_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
  | pairβ h_redex h_redex_eq =>
    unfold has_redex
    simp only [pair_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
  | id h_redex h_redex_eq =>
    unfold has_redex
    simp only [id_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
  | fst₁ h_redex h_redex_eq =>
    unfold has_redex
    simp only [fst_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
  | fst₂ h_redex h_redex_eq =>
    unfold has_redex
    simp only [fst_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | snd₁ h_redex h_redex_eq =>
    unfold has_redex
    simp only [snd_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
  | snd₂ h_redex h_redex_eq =>
    unfold has_redex
    simp only [snd_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | app₁ h_redex h_redex_eq =>
    unfold has_redex
    simp only [app_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
  | app₂ h_redex h_redex_eq =>
    unfold has_redex
    simp only [app_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | quot₁ h_redex h_redex_eq =>
    unfold has_redex
    simp only [quot_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
  | quot₂ h_redex h_redex_eq =>
    unfold has_redex
    simp only [quot_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | quot₃ h_redex h_redex_eq =>
    unfold has_redex
    simp only [quot_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | comp₁ h_redex h_redex_eq =>
    unfold has_redex
    simp only [comp_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
  | comp₂ h_redex h_redex_eq =>
    unfold has_redex
    simp only [comp_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | sigα h_redex h_redex_eq =>
    unfold has_redex
    simp only [sig_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
  | sigβ h_redex h_redex_eq =>
    unfold has_redex
    simp only [sig_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | curr₁ h_redex h_redex_eq =>
    unfold has_redex
    simp only [curr_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
  | curr₂ h_redex h_redex_eq =>
    unfold has_redex
    simp only [curr_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | right h_redex h_redex_eq =>
    unfold has_redex
    split
    · simp_all only
    · simp_all only
      split
      repeat simp_all
  | left h_redex h_redex_eq =>
    unfold has_redex
    simp only
    split
    · simp_all only
    · split
      repeat simp_all

@[simp] theorem HasRedex.sound' (_h : has_redex e = .none) : ¬ HasRedex e := fun h => by
  have h := h.complete
  simp_all only [reduceCtorEq]

instance HasRedex.instDecidable : Decidable (HasRedex e) :=
  if h : e.has_redex.isSome then
    .isTrue (e.has_redex.get h).down
  else
    .isFalse (fun h => absurd h (HasRedex.sound' (by simp_all only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, sound'])))

@[simp] theorem HasRedex.complete' (h : ¬ HasRedex e) : has_redex e = .none := by
  have h : ¬ ∃ h, e.has_redex = .some ⟨h⟩ := fun ⟨hp, heq⟩ => by
    have h : e.HasRedex := HasRedex.sound heq
    contradiction
  cases h₂ : e.has_redex with
  | none => rfl
  | some val => exfalso; exact h ⟨val.down, by simp_all only [Option.some.injEq, sound, not_true_eq_false]⟩

/-
TySize

⟦β⟧⟨a, b⟩ x → (a x, b x) size does decrease because we can consider term size and type size.
can just define size of couple to be 1?

then we consider both TySize and Size

it's actually even simpler, because the type doesn't mention x.

however this requires judge.
-/

inductive Size : Expr → ℕ → Prop
  | sort   : Size (DCC Sort m) 1
  | id     : Size α m → Size (DCC Id(α)) m.succ
  | quot   : Size α m → Size β n → Size x o → Size (DCC `(α, β, x)) (m + n + o).succ
  | comp   : Size f m → Size g n → Size (DCC (f ∘ g)) (m + n).succ
  | coup   : Size β m → Size f n → Size g o → Size (DCC ⟦β⟧(f, g)) (m + n + o).succ
  | pair   : Size β m → Size f n → Size g o → Size (DCC ⟦β⟧⟨f, g⟩) (m + n + o).succ
  | fst    : Size α m → Size β n → Size (DCC Fst(α, β)) (m + n).succ
  | snd    : Size α m → Size β n → Size (DCC Snd(α, β)) (m + n).succ
  | curr   : Size β m → Size x n → Size (DCC Λ(β, x)) (m + n).succ.succ
  | pi     : Size (DCC Π(_m, _n)) 1
  | appl   : Size α m → Size β n → Size (DCC App(α, β)) (m + n).succ
  | app    : Size f m → Size x n → Size (DCC (f x)) (m + n)
  | sig    : Size α m → Size β n → Size (DCC Σ(α, β)) (m + n).succ

def size (e : Expr) : ((n : ℕ) × (PLift (Size e n))) :=
  match e with
  | DCC Sort _m => ⟨1, ⟨.sort⟩⟩
  | DCC Σ(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    ⟨(m + n).succ, ⟨.sig h₁ h₂⟩⟩
  | DCC Id(α) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    ⟨m.succ, ⟨.id h₁⟩⟩
  | DCC `(α, β, x) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    let ⟨o, ⟨h₃⟩⟩ := x.size
    ⟨(m + n + o).succ, ⟨.quot h₁ h₂ h₃⟩⟩
  | DCC (f ∘ g) =>
    let ⟨m, ⟨h₁⟩⟩ := f.size
    let ⟨n, ⟨h₂⟩⟩ := g.size
    ⟨(m + n).succ, ⟨.comp h₁ h₂⟩⟩
  | DCC ⟦β⟧(a, b) =>
    let ⟨m, ⟨h₁⟩⟩ := β.size
    let ⟨n, ⟨h₂⟩⟩ := a.size
    let ⟨o, ⟨h₃⟩⟩ := b.size
    ⟨(m + n + o).succ, ⟨.coup h₁ h₂ h₃⟩⟩
  | DCC ⟦β⟧⟨a, b⟩ =>
    let ⟨m, ⟨h₁⟩⟩ := β.size
    let ⟨n, ⟨h₂⟩⟩ := a.size
    let ⟨o, ⟨h₃⟩⟩ := b.size
    ⟨(m + n + o).succ, ⟨.pair h₁ h₂ h₃⟩⟩
  | DCC Fst(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    ⟨(m + n).succ, ⟨.fst h₁ h₂⟩⟩
  | DCC Snd(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    ⟨(m + n).succ, ⟨.snd h₁ h₂⟩⟩
  | DCC Λ(β, x) =>
    let ⟨m, ⟨h₁⟩⟩ := β.size
    let ⟨n, ⟨h₂⟩⟩ := x.size
    ⟨(m + n).succ.succ, ⟨.curr h₁ h₂⟩⟩
  | DCC Π(_m, _n) =>
    ⟨1, ⟨.pi⟩⟩
  | DCC App(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    ⟨(m + n).succ, ⟨.appl h₁ h₂⟩⟩
  | DCC (f x) =>
    let ⟨m, ⟨h₁⟩⟩ := f.size
    let ⟨n, ⟨h₂⟩⟩ := x.size
    ⟨(m + n), ⟨.app h₁ h₂⟩⟩

theorem Size.no_zero (h : Size e n) : n ≠ 0 := by
  induction h
  repeat simp
  case app f m x n hf hx ih₁ ih₂ =>
    intro h
    simp_all only [ne_eq, not_true_eq_false]
  simp

theorem Size.sound (_h : Expr.size e = ⟨n, ⟨h⟩⟩) : Size e n := h

theorem no_zero_size' : (size e).fst ≠ 0 := by
  intro ha
  have h := (size e).snd.down.no_zero
  simp_all only

theorem size_pos : 0 < (size e).fst := by
  have h := no_zero_size' (e := e)
  if h : (size e).fst = 0 then
    contradiction
  else grind

theorem Size.complete (h : Size e n) : size e = ⟨n, .up h⟩ := by
  induction h with
  | sort | pi => rfl
  | curr h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | quot h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    unfold size
    rw [ih₁, ih₂, ih₃]
  | fst h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | snd h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | sig h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | id h₁ ih₁ =>
    unfold size
    rw [ih₁]
  | appl h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | comp h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | pair h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    unfold size
    rw [ih₁, ih₂, ih₃]
  | coup h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    unfold size
    rw [ih₁, ih₂, ih₃]
  | app h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]

instance instSizeOf : SizeOf Expr := ⟨fun e => e.size.fst⟩

inductive Red : Expr → Expr → Prop
  | curr₁     : ¬ HasRedex β → Red α α' → Red (DCC Λ(α, β)) (DCC Λ(α', β))
  | curr₂     : Red β β' → Red (DCC Λ(α, β)) (DCC Λ(α, β'))
  | sig₁      : ¬ HasRedex β → Red α α' → Red (DCC Σ(α, β)) (DCC Σ(α', β))
  | sig₂      : Red β β' → Red (DCC Σ(α, β)) (DCC Σ(α, β'))
  | app₁      : ¬ HasRedex β → Red α α' → Red (DCC App(α, β)) (DCC App(α', β))
  | app₂      : Red β β' → Red (DCC App(α, β)) (DCC App(α, β'))
  | fst₁      : ¬ HasRedex β → Red α α' → Red (DCC Fst(α, β)) (DCC Fst(α', β))
  | fst₂      : Red β β' → Red (DCC Fst(α, β)) (DCC Fst(α, β'))
  | snd₁      : ¬ HasRedex β → Red α α' → Red (DCC Snd(α, β)) (DCC Snd(α', β))
  | snd₂      : Red β β' → Red (DCC Snd(α, β)) (DCC Snd(α, β'))
  | id₁       : Red α α' → Red (DCC Id(α)) (DCC Id(α'))
  | quot₁     : ¬ HasRedex x → ¬ HasRedex β → Red α α' → Red (DCC `(α, β, x)) (DCC `(α', β, x))
  | quot₂     : ¬ HasRedex x → Red β β' → Red (DCC `(α, β, x)) (DCC `(α, β', x))
  | quot₃     : Red x x' → Red (DCC `(α, β, x)) (DCC `(α, β, x'))
  | comp₁     : ¬ HasRedex g → Red f f' → Red (DCC (f ∘ g)) (DCC (f' ∘ g))
  | comp₂     : Red g g' → Red (DCC (f ∘ g)) (DCC (f ∘ g'))
  | app       : Red (DCC (App(_δ, _τ) ⟦β⟧(f, x))) (DCC (f x))
  | fst       : Red (DCC (Fst(_δ, _τ) ⟦β⟧(a, b))) a
  | snd       : Red (DCC (Snd(_δ, _τ) ⟦β⟧(a, b))) b
  | id        : Red (DCC (Id(_α) x)) x
  | quot      : Red (DCC (`(_α, _β, x) y)) x
  | comp      : Red (DCC ((x ∘ y) z)) (DCC (x (y z)))
  | pair      : Red (DCC (⟦β⟧⟨f, g⟩ x)) (DCC ⟦β⟧((f x), (g x)))
  | curr      : Red (DCC (Λ(β, x) y z)) (DCC (x ⟦β⟧(y, z)))
  | sigβ      : ¬ HasRedex a → ¬ HasRedex b → Red β β' → Red (DCC ⟦β⟧(a, b)) (DCC ⟦β'⟧(a, b))
  | sigl      : ¬ HasRedex b → Red a a' → Red (DCC ⟦β⟧(a, b)) (DCC ⟦β⟧(a', b))
  | sigr      : Red b b'     → Red (DCC ⟦β⟧(a, b)) (DCC ⟦β⟧(a, b'))
  | pairβ     : ¬ HasRedex a → ¬ HasRedex b → Red β β' → Red (DCC ⟦β⟧⟨a, b⟩) (DCC ⟦β'⟧⟨a, b⟩)
  | pairl     : ¬ HasRedex b → Red a a' → Red (DCC ⟦β⟧⟨a, b⟩) (DCC ⟦β⟧⟨a', b⟩)
  | pairr     : Red b b'     → Red (DCC ⟦β⟧⟨a, b⟩) (DCC ⟦β⟧⟨a, b'⟩)
  | congrFun  : ¬ HasRedex x → ¬ IsRedex (DCC (f x)) → Red f f' → Red (DCC (f x)) (DCC (f' x))
  | congrArg  : ¬ IsRedex (DCC (f x)) → Red x x' → Red (DCC (f x)) (DCC (f x'))

theorem Red.HasRedex : Red a b → a.HasRedex := fun h => by
  induction h
  · simp [HasRedex.curr₁ (by assumption)]
  · simp [HasRedex.curr₂ (by assumption)]
  · simp [HasRedex.sigα (by assumption)]
  · simp [HasRedex.sigβ (by assumption)]
  · simp [HasRedex.app₁ (by assumption)]
  · simp [HasRedex.app₂ (by assumption)]
  · simp [HasRedex.fst₁ (by assumption)]
  · simp [HasRedex.fst₂ (by assumption)]
  · simp [HasRedex.snd₁ (by assumption)]
  · simp [HasRedex.snd₂ (by assumption)]
  · simp [HasRedex.id (by assumption)]
  · simp [HasRedex.quot₁ (by assumption)]
  · simp [HasRedex.quot₂ (by assumption)]
  · simp [HasRedex.quot₃ (by assumption)]
  · simp [HasRedex.comp₁ (by assumption)]
  · simp [HasRedex.comp₂ (by assumption)]
  · simp [HasRedex.single IsRedex.app]
  · simp [HasRedex.single IsRedex.fst]
  · simp [HasRedex.single IsRedex.snd]
  · simp [HasRedex.single IsRedex.id]
  · simp [HasRedex.single IsRedex.quot]
  · simp [HasRedex.single IsRedex.comp]
  · simp [HasRedex.single IsRedex.pair]
  · simp [HasRedex.single IsRedex.curr]
  · simp [HasRedex.coupβ (by assumption)]
  · simp [HasRedex.coupl (by assumption)]
  · simp [HasRedex.coupr (by assumption)]
  · simp [HasRedex.pairβ (by assumption)]
  · simp [HasRedex.pairl (by assumption)]
  · simp [HasRedex.pairr (by assumption)]
  · simp [HasRedex.left (by assumption)]
  · simp [HasRedex.right (by assumption)]

/-
Π(m, n) A B x -> B ⟦Id(Sort m)⟧(a, x)
-/

inductive ParRed : Expr → Expr → Prop
  | refl_sig  : ParRed (DCC Σ(a, b)) (DCC Σ(a, b))
  | refl_app  : ParRed (DCC App(_δ, _τ)) (DCC App(_δ, _τ))
  | refl_fst  : ParRed (DCC Fst(_δ, _τ)) (DCC Fst(_δ, _τ))
  | refl_snd  : ParRed (DCC Snd(_δ, _τ)) (DCC Snd(_δ, _τ))
  | refl_id   : ParRed (DCC Id(_α)) (DCC Id(_α))
  | refl_pi   : ParRed (DCC Π(m, n)) (DCC Π(m, n))
  | refl_quot : ParRed (DCC `(_α, _β, x)) (DCC `(_α, _β, x))
  | refl_curr : ParRed (DCC Λ(_β, _x)) (DCC Λ(_β, _x))
  | refl_pair : ParRed (DCC ⟦β⟧⟨_f, _g⟩) (DCC ⟦β⟧⟨_f, _g⟩)
  | refl_sort : ParRed (DCC Sort m) (DCC Sort m)
  | refl_comp : ParRed (DCC f ∘ g)  (DCC f ∘ g)
  | app       : ParRed (DCC (f x)) e' → ParRed (DCC (App(_δ, _τ) ⟦β⟧(f, x))) e'
  | fst       : ParRed a a' → ParRed (DCC (Fst(_δ, _τ) ⟦β⟧(a, b))) a'
  | snd       : ParRed b b' → ParRed (DCC (Snd(_δ, _τ) ⟦β⟧(a, b))) b'
  | id        : ParRed x x' → ParRed (DCC (Id(_α) x)) x'
  | quot      : ParRed x x' → ParRed (DCC (`(_α, _β, x) y)) x'
  | comp      : ParRed (DCC (x (y z))) e' → ParRed (DCC ((x ∘ y) z)) e'
  | pair      : ParRed (DCC (f x)) a'
    → ParRed (DCC (g x)) b'
    → ParRed (DCC (⟦β⟧⟨f, g⟩ x)) (DCC ⟦β⟧(a', b'))
  | curr      : ParRed (DCC (x ⟦β⟧(y, z))) e' → ParRed (DCC (Λ(β, x) y z)) e'
  | coupl     : ParRed a a' → ParRed b b'     → ParRed (DCC ⟦β⟧(a, b)) (DCC ⟦β⟧(a', b'))
  | congr     : ¬ IsRedex (DCC (f x)) → ParRed f f'  → ParRed x x' → ParRed (DCC (f x)) (DCC (f' x'))

def red_par (e : Expr) : ((e' : Expr) × PLift (ParRed e e')) :=
  if h : e.IsRedex then
    match heq : e with
    | DCC (`(_α, _β, x) y) =>
      have _h₁ : x.size.fst < ((_α.quot _β x).app y).size.fst := by
        simp [size]
        grind
      let ⟨x', ⟨h⟩⟩ := x.red_par
      ⟨x', ⟨.quot h⟩⟩
    | DCC (App(_δ, _τ) ⟦β⟧(f, x)) =>
      have _h₂ : (f.app x).size.fst < ((_δ.appl _τ).app (β.mk f x)).size.fst := by
        simp only [size, Nat.succ_eq_add_one]
        grind
      let ⟨e', ⟨h⟩⟩ := (DCC (f x)).red_par
      ⟨e', ⟨.app h⟩⟩
    | DCC (Fst(_α, _β) ⟦_γ⟧(a, b)) =>
      have _h₃ : a.size.fst < ((_α.fst _β).app (_γ.mk a b)).size.fst := by
        simp only [size, Nat.succ_eq_add_one]
        grind
      let ⟨a', ⟨h⟩⟩ := a.red_par
      ⟨a', ⟨.fst h⟩⟩
    | DCC (Snd(_α, _β) ⟦_γ⟧(a, b)) =>
      have _h₄ : b.size.fst < ((_α.snd _β).app (_γ.mk a b)).size.fst := by
        simp only [size, Nat.succ_eq_add_one]
        grind
      let ⟨b', ⟨h⟩⟩ := b.red_par
      ⟨b', ⟨.snd h⟩⟩
    | DCC ((f ∘ g) x) =>
      have _h₆ : (f.app (g.app x)).size.fst < ((f.comp g).app x).size.fst := by
        simp [size]
        grind
      let ⟨e', ⟨h⟩⟩ := (DCC (f (g x))).red_par
      ⟨e', ⟨.comp h⟩⟩
    | DCC (⟦β⟧⟨f, g⟩ x) =>
      have _h₇ : (f.app x).size.fst < ((β.pair f g).app x).size.fst := by
        simp only [size, Nat.succ_eq_add_one, add_lt_add_iff_right]
        grind
      have _h₈ : (g.app x).size.fst < ((β.pair f g).app x).size.fst := by
        simp only [size, Nat.succ_eq_add_one, add_lt_add_iff_right]
        grind
      let ⟨a', ⟨h₁⟩⟩ := red_par (DCC (f x))
      let ⟨b', ⟨h₂⟩⟩ := red_par (DCC (g x))
      ⟨DCC ⟦β⟧(a', b'), ⟨.pair h₁ h₂⟩⟩
    | DCC (Λ(β, x) y z) =>
      have _h₉ : (x.app (β.mk y z)).size.fst < (((β.curr x).app y).app z).size.fst := by
        simp [size]
        grind
      let ⟨e', ⟨h⟩⟩ := red_par (DCC (x ⟦β⟧(y, z)))
      ⟨e', ⟨.curr h⟩⟩
    | DCC (Id(_α) x) =>
      have _h₅ : x.size.fst < (_α.id.app x).size.fst := by
        simp [size]
      let ⟨x', ⟨h⟩⟩ := x.red_par
      ⟨x', ⟨.id h⟩⟩
  else
    match e with
    | DCC Sort m       => ⟨DCC Sort m, ⟨.refl_sort⟩⟩
    | DCC App(_δ, _τ)  => ⟨DCC App(_δ, _τ), ⟨.refl_app⟩⟩
    | DCC Fst(_δ, _τ)  => ⟨DCC Fst(_δ, _τ), ⟨.refl_fst⟩⟩
    | DCC Snd(_δ, _τ)  => ⟨DCC Snd(_δ, _τ), ⟨.refl_snd⟩⟩
    | DCC Id(_α)       => ⟨DCC Id(_α), ⟨.refl_id⟩⟩
    | DCC Λ(_β, _x)    => ⟨DCC Λ(_β, _x), ⟨.refl_curr⟩⟩
    | DCC ⟦_β⟧⟨_a, _b⟩ => ⟨DCC ⟦_β⟧⟨_a, _b⟩, ⟨.refl_pair⟩⟩
    | DCC Σ(a, b)      => ⟨DCC Σ(a, b), ⟨.refl_sig⟩⟩
    | DCC Π(m, n)      => ⟨DCC Π(m, n), ⟨.refl_pi⟩⟩
    | DCC `(α, β, x)   => ⟨DCC `(α, β, x), ⟨.refl_quot⟩⟩
    | DCC f ∘ g        => ⟨DCC f ∘ g, ⟨.refl_comp⟩⟩
    | DCC ⟦β⟧(a, b)    =>
      have _h0 : (size a).fst < (size (β.mk a b)).fst := by
        simp [size]
        grind
      have _h01 : (size b).fst < (size (β.mk a b)).fst := by
        simp [size]
        grind
      let ⟨a', ⟨h₂⟩⟩ := a.red_par
      let ⟨b', ⟨h₃⟩⟩ := b.red_par
      ⟨DCC ⟦β⟧(a', b'), ⟨.coupl h₂ h₃⟩⟩
    | DCC (f x) =>
      have h₁ : ¬ (DCC (f x)).IsRedex := by
        simp_all
      have _ha : (size f).fst < (size (f.app x)).fst := by
        simp [size, size_pos]
      have _hb : (size x).fst < (size (f.app x)).fst := by
        simp [size, size_pos]
      let ⟨f', ⟨h₂⟩⟩ := f.red_par
      let ⟨x', ⟨h₃⟩⟩ := x.red_par
      ⟨DCC (f' x'), ⟨.congr h₁ h₂ h₃⟩⟩
termination_by e

theorem ParRed.sound (_h : red_par e = ⟨e', ⟨hr⟩⟩) : ParRed e e' := hr

theorem ParRed.complete (h : ParRed e e') : red_par e = ⟨e', ⟨h⟩⟩ := by
  induction heq : h with
  | refl_comp | refl_pair | refl_curr | refl_quot | refl_pi | refl_sort | refl_id | refl_snd | refl_fst | refl_app | refl_sig =>
    simp only [red_par, dite_eq_right_iff]
    intro h
    contradiction
  | app ih₁ ih₂ =>
    unfold red_par
    simp [IsRedex.app]
    simp_all
    congr
    repeat simp_all
  | fst ih₁ =>
    unfold red_par
    simp [IsRedex.fst]
    simp_all
    congr
    repeat simp_all
  | snd ih₁ =>
    unfold red_par
    simp [IsRedex.snd]
    simp_all
    congr
    repeat simp_all
  | id =>
    unfold red_par
    simp [IsRedex.id]
    simp_all
    congr
    repeat simp_all
  | quot =>
    unfold red_par
    simp [IsRedex.quot]
    simp_all
    congr
    repeat simp_all
  | comp =>
    unfold red_par
    simp [IsRedex.comp]
    simp_all
    congr
    repeat simp_all
  | pair =>
    unfold red_par
    simp [IsRedex.pair]
    simp_all
    congr
    repeat simp_all
  | curr =>
    unfold red_par
    simp [IsRedex.curr]
    simp_all
    congr
    repeat simp_all
  | coupl =>
    rename_i a a' b b' β hra hrb ih₁ ih₂
    have h : ¬ (β.mk a b).IsRedex := fun h => by cases h
    unfold red_par
    simp_all
    congr
    repeat simp_all
  | congr =>
    rename_i f x f' x' h_n_redex h_r_f h_r_x ih₁ ih₂
    unfold red_par
    simp [h_n_redex]
    simp_all
    congr
    repeat simp_all

theorem ParRed.diamond (h₁ : ParRed A B) (h₂ : ParRed A C) : ∃ D, ParRed B D ∧ ParRed C D := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all
  exact ⟨_, ParRed.sound rfl⟩

def ParRed.Trans     := Relation.TransGen ParRed
def ParRed.ReflTrans := Relation.ReflTransGen ParRed

def step? (e : Expr) : Option ((e' : Expr) × (PLift (e.Red e'))) :=
  if h : e.IsRedex then
    match e with
    | (DCC (App(_δ, _τ) ⟦_β⟧(f, x)))  => .some ⟨(DCC (f x)), ⟨.app⟩⟩
    | (DCC (Fst(_δ, _τ) ⟦_β⟧(a, _b))) => .some ⟨a, ⟨.fst⟩⟩
    | (DCC (Snd(_δ, _τ) ⟦_β⟧(_a, b))) => .some ⟨b, ⟨.snd⟩⟩
    | (DCC (Id(_α) x))                => .some ⟨x, ⟨.id⟩⟩
    | (DCC (`(_α, _β, x) _y))         => .some ⟨x, ⟨.quot⟩⟩
    | (DCC ((x ∘ y) z))               => .some ⟨DCC (x (y z)), ⟨.comp⟩⟩
    | (DCC (⟦β⟧⟨f, g⟩ x))             => .some ⟨(DCC ⟦β⟧((f x), (g x))), ⟨.pair⟩⟩
    | (DCC (Λ(β, x) y z))             => .some ⟨DCC (x ⟦β⟧(y, z)), ⟨.curr⟩⟩
  else do
    match e with
    | DCC Sort _m => .none
    | DCC Λ(α, β) =>
      if hr : ¬ β.HasRedex then
        let ⟨α', ⟨h⟩⟩ ← α.step?
        .some ⟨DCC Λ(α', β), ⟨.curr₁ hr h⟩⟩
      else
        let ⟨β', ⟨h⟩⟩ ← β.step?
        .some ⟨DCC Λ(α, β'), ⟨.curr₂ h⟩⟩
    | DCC Fst(α, β) =>
      if hr : ¬ β.HasRedex then
        let ⟨α', ⟨h⟩⟩ ← α.step?
        .some ⟨DCC Fst(α', β), ⟨.fst₁ hr h⟩⟩
      else
        let ⟨β', ⟨h⟩⟩ ← β.step?
        .some ⟨DCC Fst(α, β'), ⟨.fst₂ h⟩⟩
    | DCC Snd(α, β) =>
      if hr : ¬ β.HasRedex then
        let ⟨α', ⟨h⟩⟩ ← α.step?
        .some ⟨DCC Snd(α', β), ⟨.snd₁ hr h⟩⟩
      else
        let ⟨β', ⟨h⟩⟩ ← β.step?
        .some ⟨DCC Snd(α, β'), ⟨.snd₂ h⟩⟩
    | DCC App(α, β) =>
      if hr : ¬ β.HasRedex then
        let ⟨α', ⟨h⟩⟩ ← α.step?
        .some ⟨DCC App(α', β), ⟨.app₁ hr h⟩⟩
      else
        let ⟨β', ⟨h⟩⟩ ← β.step?
        .some ⟨DCC App(α, β'), ⟨.app₂ h⟩⟩
    | DCC Id(α) =>
      let ⟨α', ⟨h⟩⟩ ← α.step?
      .some ⟨DCC Id(α'), ⟨.id₁ h⟩⟩
    | DCC `(α, β, x) =>
      if hr₁ : ¬ x.HasRedex then
        if hr₂ : ¬ β.HasRedex then
          let ⟨α', ⟨h⟩⟩ ← α.step?
          .some ⟨DCC `(α', β, x), ⟨.quot₁ hr₁ hr₂ h⟩⟩
        else
          let ⟨β', ⟨h⟩⟩ ← β.step?
          .some ⟨DCC `(α, β', x), ⟨.quot₂ hr₁ h⟩⟩
      else
        let ⟨x', ⟨h⟩⟩ ← x.step?
        .some ⟨DCC `(α, β, x'), ⟨.quot₃ h⟩⟩
    | DCC (f ∘ g) =>
      if hr : ¬ g.HasRedex then
        let ⟨f', ⟨h⟩⟩ ← f.step?
        .some ⟨DCC (f' ∘ g), ⟨.comp₁ hr h⟩⟩
      else
        let ⟨g', ⟨h⟩⟩ ← g.step?
        .some ⟨DCC (f ∘ g'), ⟨.comp₂ h⟩⟩
    | DCC (Σ(α, β)) =>
      if hr : ¬ β.HasRedex then
        let ⟨α', ⟨h⟩⟩ ← α.step?
        .some ⟨DCC Σ(α', β), ⟨.sig₁ hr h⟩⟩
      else
        let ⟨β', ⟨h⟩⟩ ← β.step?
        .some ⟨DCC Σ(α, β'), ⟨.sig₂ h⟩⟩
    | DCC ⟦β⟧(a, b) =>
      if hr : ¬ b.HasRedex then
        if hr₂ : ¬ a.HasRedex then
          let ⟨β', ⟨h⟩⟩ ← β.step?
          .some ⟨DCC ⟦β'⟧(a, b), ⟨.sigβ hr₂ hr h⟩⟩
        else
          match a.step? with
          | .some ⟨a', ⟨h₁⟩⟩ =>
            .some ⟨DCC ⟦β⟧(a', b), ⟨.sigl hr h₁⟩⟩
          | .none => .none
      else
        match b.step? with
        | .some ⟨b', ⟨h₁⟩⟩ =>
          .some ⟨DCC ⟦β⟧(a, b'), ⟨.sigr h₁⟩⟩
        | .none => .none
    | DCC ⟦β⟧⟨a, b⟩ =>
      if hr : ¬ b.HasRedex then
        if hr₂ : ¬ a.HasRedex then
          let ⟨β', ⟨h⟩⟩ ← β.step?
          .some ⟨DCC ⟦β'⟧⟨a, b⟩, ⟨.pairβ hr₂ hr h⟩⟩
        else
          match a.step? with
          | .some ⟨a', ⟨h₁⟩⟩ =>
            .some ⟨DCC ⟦β⟧⟨a', b⟩, ⟨.pairl hr h₁⟩⟩
          | .none => .none
      else
        match b.step? with
        | .some ⟨b', ⟨h₁⟩⟩ =>
          .some ⟨DCC ⟦β⟧⟨a, b'⟩, ⟨.pairr h₁⟩⟩
        | .none => .none
    | DCC (f x) =>
      if hr : ¬ x.HasRedex then
        match f.step? with
        | .some ⟨f', ⟨h₁⟩⟩ =>
          .some ⟨DCC (f' x), ⟨.congrFun hr h h₁⟩⟩
        | .none => .none
      else
        match x.step? with
        | .some ⟨x', ⟨h₁⟩⟩ =>
          .some ⟨DCC (f x'), ⟨.congrArg h h₁⟩⟩
        | .none => .none
    | _ => .none

theorem Step?.sound (_h : step? e = .some ⟨e', ⟨hr⟩⟩) : Red e e' := hr

theorem Red.complete (h : Red e e') : step? e = .some ⟨e', ⟨h⟩⟩ := by
  induction h with
  | app =>
    unfold step?
    simp [IsRedex.app]
  | id =>
    unfold step?
    simp [IsRedex.id]
  | fst =>
    unfold step?
    simp [IsRedex.fst]
  | snd =>
    unfold step?
    simp [IsRedex.snd]
  | quot =>
    unfold step?
    simp [IsRedex.quot]
  | comp =>
    unfold step?
    simp [IsRedex.comp]
  | pair =>
    unfold step?
    simp [IsRedex.pair]
  | curr =>
    unfold step?
    simp [IsRedex.curr]
  | sigl hredex hr ih =>
    rename_i b a a' β
    have h : ¬ (β.mk a b).IsRedex := fun h => by cases h
    unfold step?
    simp [coupl_not_redex, hredex, hr.HasRedex, ih]
  | sigr hr ih =>
    rename_i b a a' β
    have h := hr.HasRedex
    unfold step?
    simp_all
  | pairl hredex hr ih =>
    rename_i b a a' β
    have h : ¬ (β.pair a b).IsRedex := fun h => by cases h
    unfold step?
    simp [pair_not_redex, hredex, hr.HasRedex, ih]
  | pairr hr ih =>
    rename_i b a a' β
    have h := hr.HasRedex
    unfold step?
    simp_all
  | curr₁ hredex hr ih₁ =>
    rename_i β α α'
    unfold step?
    simp [curr_not_redex, hredex, ih₁]
  | curr₂ hr ih₁ =>
    rename_i β α α'
    unfold step?
    simp [curr_not_redex, hr.HasRedex, ih₁]
  | sig₁ hredex hr ih₁ =>
    rename_i β α α'
    unfold step?
    simp [sig_not_redex, hredex, ih₁]
  | sig₂ hr ih₁ =>
    rename_i β α α'
    unfold step?
    simp [sig_not_redex, hr.HasRedex, ih₁]
  | sigβ hr ih₁ ih₂ ih₃ =>
    unfold step?
    simp [coupl_not_redex, ih₁, hr, ih₃]
  | pairβ hr ih₁ ih₂ ih₃ =>
    unfold step?
    simp [pair_not_redex, ih₁, hr, ih₃]
  | app₁ hredex hr ih₁ =>
    rename_i β α α'
    unfold step?
    simp [app_not_redex, hredex, ih₁]
  | app₂ hr ih₁ =>
    rename_i β α α'
    unfold step?
    simp [app_not_redex, hr.HasRedex, ih₁]
  | comp₁ hredex hr ih₁ =>
    rename_i β α α'
    unfold step?
    simp [comp_not_redex, hredex, ih₁]
  | comp₂ hr ih₁ =>
    rename_i β α α'
    unfold step?
    simp [comp_not_redex, hr.HasRedex, ih₁]
  | fst₁ hredex hr ih₁ =>
    rename_i β α α'
    unfold step?
    simp [fst_not_redex, hredex, ih₁]
  | fst₂ hr ih₁ =>
    rename_i β α α'
    unfold step?
    simp [fst_not_redex, hr.HasRedex, ih₁]
  | snd₁ hredex hr ih₁ =>
    rename_i β α α'
    unfold step?
    simp [snd_not_redex, hredex, ih₁]
  | snd₂ hr ih₁ =>
    rename_i β α α'
    unfold step?
    simp [snd_not_redex, hr.HasRedex, ih₁]
  | id₁ hr ih₁ =>
    unfold step?
    simp [id_not_redex, ih₁]
  | quot₁ hredex hr ih₁ ih₂ =>
    rename_i β α α'
    unfold step?
    simp [quot_not_redex, hredex, hr, ih₂]
  | quot₂ hr ih₁ ih₂ =>
    rename_i β α α'
    unfold step?
    simp [quot_not_redex, hr, ih₁.HasRedex, ih₂]
  | quot₃ ih₁ ih₂ =>
    rename_i β α α'
    unfold step?
    simp [quot_not_redex, ih₁.HasRedex, ih₂]
  | congrFun =>
    rename_i hr _
    have h := hr.HasRedex
    unfold step?
    simp_all
  | congrArg =>
    rename_i hr _
    have h := hr.HasRedex
    unfold step?
    simp_all

instance ParRed.instDecidable : Decidable (ParRed A B) :=
  if h : A.red_par.fst = B then
    .isTrue (h.symm ▸ (A.red_par.snd.down))
  else
    .isFalse (fun h => by simp [h.complete] at *)

theorem red_none : step? e = .none → ¬ Red e e' := fun h ha => by
  simp [ha.complete] at *

instance Red.instDecidable : Decidable (Red A B) :=
  if heq : (step? A).isSome then
    if heq' : ((step? A).get heq).fst = B then
      .isTrue (heq' ▸ ((step? A).get heq).snd.down)
    else
      .isFalse (fun h => by simp [h.complete] at *)
  else
    have h : (step? A) = none := by
      simp_all only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]

    have h := red_none (e' := B) h
    .isFalse (fun h => by simp [h.complete] at *)

end Expr
