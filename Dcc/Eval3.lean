import Dcc.Ast3

namespace CcExpr

inductive IsRedex : CcExpr → Prop
  | app    : IsRedex (CC (App(_δ, _τ) (f, x)))
  | fst    : IsRedex (CC (Fst(_δ, _τ) (a, b)))
  | snd    : IsRedex (CC (Snd(_δ, _τ) (a, b)))
  | comp   : IsRedex (CC ((x ∘ y) z))
  | dpair  : IsRedex (CC (⟨f, g⟩ x))
  | curr   : IsRedex (CC (Λ(x) y z))

@[simp] theorem coup_not_redex : ¬ IsRedex (CC (a, b)) := fun h => by
  cases h

inductive HasRedex : CcExpr → Prop
  | single : IsRedex a  → HasRedex a
  | left   : HasRedex f → HasRedex (CC (f x))
  | right  : HasRedex x → HasRedex (CC (f x))
  | coupl  : HasRedex a → HasRedex (CC (a, b))
  | coupr  : HasRedex b → HasRedex (CC (a, b))

def is_redex (e : CcExpr) : Option (PLift e.IsRedex) :=
  match e with
  | (CC (App(_δ, _τ) (_f, _x)))  => .some ⟨.app⟩
  | (CC (Fst(_δ, _τ) (_a, _b)))  => .some ⟨.fst⟩
  | (CC (Snd(_δ, _τ) (_a, _b)))  => .some ⟨.snd⟩
  | (CC ((_x ∘ _y) _z))          => .some ⟨.comp⟩
  | (CC (⟨_f, _g⟩ _x))           => .some ⟨.dpair⟩
  | (CC (Λ(_x) _y _z))           => .some ⟨.curr⟩
  | _                            => .none

theorem IsRedex.sound (_h : CcExpr.is_redex e = .some he) : IsRedex e := he.down

theorem IsRedex.complete (h : IsRedex e) : is_redex e = .some (.up h) := by
  match h with
  | .snd | .fst | .comp | .curr | .app | .dpair =>
    simp only [is_redex]

theorem IsRedex.sound' (_h : is_redex e = .none) : ¬ IsRedex e := fun h => by
  have h := h.complete
  simp_all only [reduceCtorEq]

instance IsRedex.instDecidable : Decidable (IsRedex e) :=
  if h : e.is_redex.isSome then
    .isTrue (e.is_redex.get h).down
  else
    .isFalse (fun h => absurd h (IsRedex.sound' (by simp_all only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none])))

def has_redex (e : CcExpr) : Option (PLift e.HasRedex) :=
  if h : IsRedex e then
    .some ⟨.single h⟩
  else
    match e with
    | (CC (x, y)) => match _heq₂ : x.has_redex, _heq₃ : y.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.coupl h⟩
      | _, .some ⟨h⟩ => .some ⟨.coupr h⟩
      | _, _ => .none
    | (CC (f x)) => match _heq₂ : f.has_redex, _heq₃ : x.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.left h⟩
      | _, .some ⟨h⟩ => .some ⟨.right h⟩
      | _, _ => .none
    | _e => .none

@[simp] theorem HasRedex.sound (_h : CcExpr.has_redex e = .some he) : HasRedex e := he.down

theorem HasRedex.complete (h : HasRedex e) : has_redex e = .some (.up h) := by
  induction h with
  | single h =>
    unfold has_redex
    simp only [h, ↓reduceDIte]
  | coupr h_redex h_redex_eq =>
    unfold has_redex
    simp only [coup_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | coupl h_redex h_redex_eq =>
    unfold has_redex
    simp only [coup_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
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

inductive Red : CcExpr → CcExpr → Prop
  | app      : Red (CC (App(_δ, _τ) (f, x))) (CC (f x))
  | fst      : Red (CC (Fst(_δ, _τ) (a, b))) a
  | snd      : Red (CC (Snd(_δ, _τ) (a, b))) a
  | comp     : Red (CC ((x ∘ y) z)) (CC (x (y z)))
  | dpair    : Red (CC (⟨f, g⟩ x))  (CC ((f x), (g x)))
  | curr     : Red (CC (Λ(x) y z)) (CC (x (y, z)))
  | compl    : ¬ HasRedex b → Red a a' → Red (CC (a, b)) (CC (a', b))
  | compr    : Red b b'     → Red (CC (a, b)) (CC (a, b'))
  | congrFun : ¬ HasRedex x → ¬ IsRedex (CC (f x)) → Red f f' → Red (CC (f x)) (CC (f' x))
  | congrArg  : ¬ IsRedex (CC (f x)) → Red x x' → Red (CC (f x)) (CC (f x'))

@[simp] theorem Expr.HasRedex.complete' (h : ¬ HasRedex e) : has_redex e = .none := by
  have h : ¬ ∃ h, e.has_redex = .some ⟨h⟩ := fun ⟨hp, heq⟩ => by
    have h : e.HasRedex := HasRedex.sound heq
    contradiction
  cases h₂ : e.has_redex with
  | none => rfl
  | some val => exfalso; exact h ⟨val.down, by simp_all only [IsEmpty.exists_iff, not_false_eq_true]⟩

end CcExpr
