import Dcc.CC.Ast

namespace Expr

inductive IsRedex : Expr → Prop
  | app    : IsRedex (DCC (App(_δ, _τ) ⟦f, x⟧))
  | fst    : IsRedex (DCC (Fst(_δ, _τ) ⟦a, b⟧))
  | snd    : IsRedex (DCC (Snd(_δ, _τ) ⟦a, b⟧))
  | comp   : IsRedex (DCC ((x ∘ y) z))
  | pair  : IsRedex (DCC (⟨f, g⟩ x))
  | curr   : IsRedex (DCC (Λ(x) y z))
  | pi     : IsRedex (DCC (Π(B) A x))

inductive HasRedex : Expr → Prop
  | single : IsRedex a  → HasRedex a
  | left   : HasRedex f → HasRedex (DCC (f x))
  | right  : HasRedex x → HasRedex (DCC (f x))
  | sigl   : HasRedex a → HasRedex (DCC ⟦a, b⟧)
  | sigr   : HasRedex b → HasRedex (DCC ⟦a, b⟧)

def is_redex (e : Expr) : Option (PLift e.IsRedex) :=
  match e with
  | (DCC (App(_δ, _τ) ⟦_f, _x⟧))  => .some ⟨.app⟩
  | (DCC (Fst(_δ, _τ) ⟦_a, _b⟧))  => .some ⟨.fst⟩
  | (DCC (Snd(_δ, _τ) ⟦_a, _b⟧))  => .some ⟨.snd⟩
  | (DCC ((_x ∘ _y) _z))          => .some ⟨.comp⟩
  | (DCC (⟨_f, _g⟩ _x))           => .some ⟨.pair⟩
  | (DCC (Λ(_x) _y _z))           => .some ⟨.curr⟩
  | (DCC (Π(_x) _y _z))           => .some ⟨.pi⟩
  | _                            => .none

theorem IsRedex.sound (_h : Expr.is_redex e = .some he) : IsRedex e := he.down

theorem IsRedex.complete (h : IsRedex e) : is_redex e = .some (.up h) := by
  match h with
  | .pi | .snd | .fst | .comp | .curr | .app | .pair =>
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
    | (DCC ⟦x, y⟧) => match _heq₂ : x.has_redex, _heq₃ : y.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.sigl h⟩
      | _, .some ⟨h⟩ => .some ⟨.sigr h⟩
      | _, _ => .none
    | (DCC (f x)) => match _heq₂ : f.has_redex, _heq₃ : x.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.left h⟩
      | _, .some ⟨h⟩ => .some ⟨.right h⟩
      | _, _ => .none
    | _e => .none

@[simp] theorem HasRedex.sound (_h : Expr.has_redex e = .some he) : HasRedex e := he.down

@[simp] theorem sig_not_redex : ¬ IsRedex (DCC ⟦a, b⟧) := fun h => by
  cases h

theorem HasRedex.complete (h : HasRedex e) : has_redex e = .some (.up h) := by
  induction h with
  | single h =>
    unfold has_redex
    simp only [h, ↓reduceDIte]
  | sigr h_redex h_redex_eq =>
    unfold has_redex
    simp only [sig_not_redex, ↓reduceDIte]
    rw [h_redex_eq]
    split
    repeat simp_all
  | sigl h_redex h_redex_eq =>
    unfold has_redex
    simp only [sig_not_redex, ↓reduceDIte]
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

@[simp] theorem HasRedex.complete' (h : ¬ HasRedex e) : has_redex e = .none := by
  have h : ¬ ∃ h, e.has_redex = .some ⟨h⟩ := fun ⟨hp, heq⟩ => by
    have h : e.HasRedex := HasRedex.sound heq
    contradiction
  cases h₂ : e.has_redex with
  | none => rfl
  | some val => exfalso; exact h ⟨val.down, by simp_all only [Option.some.injEq, sound, not_true_eq_false]⟩

inductive Red : CcExpr → CcExpr → Prop
  | app      : Red (DCC (App(_δ, _τ) ⟦f, x⟧)) (DCC (f x))
  | fst      : Red (DCC (Fst(_δ, _τ) ⟦a, b⟧)) a
  | snd      : Red (DCC (Snd(_δ, _τ) ⟦a, b⟧)) a
  | comp     : Red (DCC ((x ∘ y) z)) (DCC (x (y z)))
  | pair    : Red (DCC (⟨f, g⟩ x))  (DCC ⟦(f x), (g x)⟧)
  | curr     : Red (DCC (Λ(x) y z)) (DCC (x ⟦y, z⟧))
  | pi       : Red (DCC (Π(B) A x)) (DCC (B ⟦A, x⟧))
  | sigl     : ¬ HasRedex b → Red a a' → Red (DCC ⟦a, b⟧) (DCC ⟦a', b⟧)
  | sigr     : Red b b'     → Red (DCC ⟦a, b⟧) (DCC ⟦a, b'⟧)
  | congrFun : ¬ HasRedex x → ¬ IsRedex (DCC (f x)) → Red f f' → Red (DCC (f x)) (DCC (f' x))
  | congrArg  : ¬ IsRedex (DCC (f x)) → Red x x' → Red (DCC (f x)) (DCC (f x'))

inductive Size : Expr → ℕ → Prop
  | sort   : Size (DCC Sort m) 1
  | id     : Size (DCC Id(_α)) 1
  | comp   : Size f m → Size g n → Size (DCC (f ∘ g)) (m + n).succ
  | mk     : Size f m → Size g n → Size (DCC ⟦f, g⟧) (m + n).succ
  | pair   : Size f m → Size g n → Size (DCC ⟨f, g⟩) (m + n).succ
  | fst    : Size (DCC Fst(_α, _β)) 1
  | snd    : Size (DCC Snd(_α, _β)) 1
  | curr   : Size x m → Size (DCC Λ(x)) m.succ
  | pi     : Size x m → Size (DCC Π(x)) m.succ
  | appl   : Size (DCC App(_α, _β)) 1
  | app    : Size f m → Size x n → Size (DCC (f x)) (m + n)
  | sig    : Size (DCC Σ a, b) 1

def size (e : Expr) : ((n : ℕ) × (PLift (Size e n))) :=
  match e with
  | DCC Sort _m => ⟨1, ⟨.sort⟩⟩
  | DCC Σ _a, _b => ⟨1, ⟨.sig⟩⟩
  | DCC Id(_α)  => ⟨1, ⟨.id⟩⟩
  | DCC (f ∘ g) =>
    let ⟨m, ⟨h₁⟩⟩ := f.size
    let ⟨n, ⟨h₂⟩⟩ := g.size
    ⟨(m + n).succ, ⟨.comp h₁ h₂⟩⟩
  | DCC ⟦a, b⟧ =>
    let ⟨m, ⟨h₁⟩⟩ := a.size
    let ⟨n, ⟨h₂⟩⟩ := b.size
    ⟨(m + n).succ, ⟨.mk h₁ h₂⟩⟩
  | DCC ⟨a, b⟩ =>
    let ⟨m, ⟨h₁⟩⟩ := a.size
    let ⟨n, ⟨h₂⟩⟩ := b.size
    ⟨(m + n).succ, ⟨.pair h₁ h₂⟩⟩
  | DCC Fst(_α, _β) => ⟨1, ⟨.fst⟩⟩
  | DCC Snd(_α, _β) => ⟨1, ⟨.snd⟩⟩
  | DCC Λ(x) =>
    let ⟨m, ⟨h⟩⟩ := x.size
    ⟨m.succ, ⟨.curr h⟩⟩
  | DCC Π(x) =>
    let ⟨m, ⟨h⟩⟩ := x.size
    ⟨m.succ, ⟨.pi h⟩⟩
  | DCC App(_α, _β) => ⟨1, ⟨.appl⟩⟩
  | DCC (f x) =>
    let ⟨m, ⟨h₁⟩⟩ := f.size
    let ⟨n, ⟨h₂⟩⟩ := x.size
    ⟨(m + n), ⟨.app h₁ h₂⟩⟩

theorem Size.sound (_h : Expr.size e = ⟨n, ⟨h⟩⟩) : Size e n := h

theorem Size.complete (h : Size e n) : size e = ⟨n, .up h⟩ := by
  induction h with
  | sig | sort | id | fst | snd | appl => rfl
  | curr h ih =>
    unfold size
    rw [ih]
  | pi h ih =>
    unfold size
    rw [ih]
  | comp h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | mk h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | pair h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | app h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]

inductive TySize : Expr → ℕ → Prop
  | id     : TySize α m
    → TySize (DCC Id(α)) m.succ
  | comp   : TySize f m
    → TySize g n
    → TySize (DCC f ∘ g) (m + n).succ
  | pair   : TySize f m
    → TySize g n
    → TySize (DCC ⟨f, g⟩) (m + n).succ
  | fst    : TySize α m
    → TySize β n
    → TySize (DCC Fst(α, β)) (m + n).succ
  | snd    : TySize α m
    → TySize β n
    → TySize (DCC Snd(α, β)) (m + n).succ
  | curr   : TySize x m → TySize (DCC Λ(x)) m.succ
  | pi     : TySize x m → TySize (DCC Π(x)) m.succ
  | sig    : TySize α m → TySize β n → TySize (DCC Σ α, β) (m + n).succ
  | appl   : TySize α m
    → TySize β n
    → TySize (DCC App(α, β)) (m + n).succ
  | mk     : TySize a m → TySize b n → TySize (DCC ⟦a, b⟧) (m + n).succ
  | sort   : TySize (DCC Sort _m) 1
  | app    : TySize f m → TySize x n → TySize (DCC (f x)) (m + n)

def ty_size (e : Expr) : ((n : ℕ) × (PLift (TySize e n))) :=
  match e with
  | DCC Sort _m => ⟨1, ⟨.sort⟩⟩
  | DCC Id(α)  =>
    let ⟨m, ⟨h⟩⟩ := α.ty_size
    ⟨m.succ, ⟨.id h⟩⟩
  | DCC (f ∘ g) =>
    let ⟨m, ⟨h₁⟩⟩ := f.ty_size
    let ⟨n, ⟨h₂⟩⟩ := g.ty_size
    ⟨(m + n).succ, ⟨.comp h₁ h₂⟩⟩
  | DCC ⟦a, b⟧ =>
    let ⟨m, ⟨h₁⟩⟩ := a.ty_size
    let ⟨n, ⟨h₂⟩⟩ := b.ty_size
    ⟨(m + n).succ, ⟨.mk h₁ h₂⟩⟩
  | DCC ⟨a, b⟩ =>
    let ⟨m, ⟨h₁⟩⟩ := a.ty_size
    let ⟨n, ⟨h₂⟩⟩ := b.ty_size
    ⟨(m + n).succ, ⟨.pair h₁ h₂⟩⟩
  | DCC Σ a, b =>
    let ⟨m, ⟨h₁⟩⟩ := a.ty_size
    let ⟨n, ⟨h₂⟩⟩ := b.ty_size
    ⟨(m + n).succ, ⟨.sig h₁ h₂⟩⟩
  | DCC Fst(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.ty_size
    let ⟨n, ⟨h₂⟩⟩ := β.ty_size
    ⟨(m + n).succ, ⟨.fst h₁ h₂⟩⟩
  | DCC Snd(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.ty_size
    let ⟨n, ⟨h₂⟩⟩ := β.ty_size
    ⟨(m + n).succ, ⟨.snd h₁ h₂⟩⟩
  | DCC Λ(x) =>
    let ⟨m, ⟨h⟩⟩ := x.ty_size
    ⟨m.succ, ⟨.curr h⟩⟩
  | DCC Π(x) =>
    let ⟨m, ⟨h⟩⟩ := x.ty_size
    ⟨m.succ, ⟨.pi h⟩⟩
  | DCC App(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.ty_size
    let ⟨n, ⟨h₂⟩⟩ := β.ty_size
    ⟨(m + n).succ, ⟨.appl h₁ h₂⟩⟩
   | DCC (f x) =>
    let ⟨m, ⟨h₁⟩⟩ := f.ty_size
    let ⟨n, ⟨h₂⟩⟩ := x.ty_size
    ⟨(m + n), ⟨.app h₁ h₂⟩⟩

theorem TySize.sound (_h : Expr.ty_size e = ⟨n, ⟨h⟩⟩) : TySize e n := h

theorem TySize.complete (h : TySize e n) : ty_size e = ⟨n, .up h⟩ := by
  induction h with
  | sort => rfl
  | curr h ih =>
    unfold ty_size
    rw [ih]
  | pi h ih =>
    unfold ty_size
    rw [ih]
  | id h ih =>
    unfold ty_size
    rw [ih]
  | comp h₁ h₂ ih₁ ih₂ =>
    unfold ty_size
    rw [ih₁, ih₂]
  | mk h₁ h₂ ih₁ ih₂ =>
    unfold ty_size
    rw [ih₁, ih₂]
  | pair h₁ h₂ ih₁ ih₂ =>
    unfold ty_size
    rw [ih₁, ih₂]
  | fst h₁ h₂ ih₁ ih₂ =>
    unfold ty_size
    rw [ih₁, ih₂]
  | snd h₁ h₂ ih₁ ih₂ =>
    unfold ty_size
    rw [ih₁, ih₂]
  | sig h₁ h₂ ih₁ ih₂ =>
    unfold ty_size
    rw [ih₁, ih₂]
  | appl h₁ h₂ ih₁ ih₂ =>
    unfold ty_size
    rw [ih₁, ih₂]
  | app h₁ h₂ ih₁ ih₂ =>
    unfold ty_size
    rw [ih₁, ih₂]

end Expr
