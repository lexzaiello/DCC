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

inductive Size : CcExpr → ℕ → Prop
  | sk     : Size (.sk _e)     1
  | sort   : Size (CC Sort m) 1
  | id     : Size (CC Id(_α)) 1
  | id'    : Size (CC Id) 1
  | comp   : Size f m → Size g n → Size (CC (f ∘ g)) (m + n).succ
  | coup   : Size f m → Size g n → Size (CC (f, g)) (m + n).succ
  | pair   : Size f m → Size g n → Size (CC ⟨f, g⟩) (m + n).succ
  | fst    : Size (CC Fst(_α, _β)) 1
  | fst'   : Size (CC Fst) 1
  | snd    : Size (CC Snd(_α, _β)) 1
  | snd'   : Size (CC Snd) 1
  | curr   : Size x m → Size (CC Λ(x)) m.succ
  | app_e  : Size (CC App(_α, _β)) 1
  | app_e' : Size (CC App) 1
  | app    : Size f m → Size x n → Size (CC (f x)) (m + n)

def size (e : CcExpr) : ((n : ℕ) × (PLift (Size e n))) :=
  match e with
  | .sk _e     => ⟨1, ⟨.sk⟩⟩
  | CC Sort _m => ⟨1, ⟨.sort⟩⟩
  | CC Id(_α)  => ⟨1, ⟨.id⟩⟩
  | CC Id => ⟨1, ⟨.id'⟩⟩
  | CC (f ∘ g) =>
    let ⟨m, ⟨h₁⟩⟩ := f.size
    let ⟨n, ⟨h₂⟩⟩ := g.size
    ⟨(m + n).succ, ⟨.comp h₁ h₂⟩⟩
  | CC (a, b) =>
    let ⟨m, ⟨h₁⟩⟩ := a.size
    let ⟨n, ⟨h₂⟩⟩ := b.size
    ⟨(m + n).succ, ⟨.coup h₁ h₂⟩⟩
  | CC ⟨a, b⟩ =>
    let ⟨m, ⟨h₁⟩⟩ := a.size
    let ⟨n, ⟨h₂⟩⟩ := b.size
    ⟨(m + n).succ, ⟨.pair h₁ h₂⟩⟩
  | CC Fst(_α, _β) => ⟨1, ⟨.fst⟩⟩
  | CC Fst => ⟨1, ⟨.fst'⟩⟩
  | CC Snd(_α, _β) => ⟨1, ⟨.snd⟩⟩
  | CC Snd => ⟨1, ⟨.snd'⟩⟩
  | CC Λ(x) =>
    let ⟨m, ⟨h⟩⟩ := x.size
    ⟨m.succ, ⟨.curr h⟩⟩
  | CC App(_α, _β) => ⟨1, ⟨.app_e⟩⟩
   | CC App => ⟨1, ⟨.app_e'⟩⟩
   | CC (f x) =>
    let ⟨m, ⟨h₁⟩⟩ := f.size
    let ⟨n, ⟨h₂⟩⟩ := x.size
    ⟨(m + n), ⟨.app h₁ h₂⟩⟩

theorem Size.sound (_h : CcExpr.size e = ⟨n, ⟨h⟩⟩) : Size e n := h

theorem Size.complete (h : Size e n) : size e = ⟨n, .up h⟩ := by
  induction h with
  | sk | sort | id | id' | fst | fst' | snd | snd' | app_e | app_e' => rfl
  | curr h ih =>
    unfold size
    rw [ih]
  | comp h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | coup h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | pair h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | app h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]

inductive Judge : CcExpr → CTy → Prop
  | id    : Judge (CC Id(α)) (CTY α → α)
  | comp  : Judge g (CTY α → β)
    → Judge f (CTY β → γ)
    → Judge (CC f ∘ g) (CTY α → γ)
  | pair  : Judge f (CTY α → τ₁)
    → Judge g (CTY α → τ₂)
    → Judge (CC ⟨f, g⟩) (CTY α → (τ₁ × τ₂))
  | fst   : Judge (CC Fst(α, β)) (CTY (α × β) → α)
  | snd   : Judge (CC Snd(α, β)) (CTY (α × β) → β)
  | curr  : Judge x (CTY (α × β) → γ) → Judge (CC Λ(x)) (CTY α → (β → γ))
  | app_e : Judge (CC App(δ, τ)) (CTY (((δ → τ) × δ) → τ))
  | coup  : Judge a α → Judge b β → Judge (CC (a, b)) (CTY α × β)
  | app   : Judge f (CTY α → β) → Judge x α → Judge (CC (f x)) β
  | sk    : Judge (.sk _e) (CTY Base)
  | sort  : Judge (CC Sort _m) (CTY Base)

end CcExpr

namespace CTy

inductive Size : CTy → ℕ → Prop
  | base  : Size (CTY Base) 1
  | arrow : Size α m → Size β n → Size (CTY α → β) (m + n).succ
  | prod  : Size α m → Size β n → Size (CTY α × β) (m + n).succ

def size (t : CTy) : ((n : ℕ) × (PLift (Size t n))) :=
  match t with
  | CTY (α → β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size

    ⟨(m + n).succ, ⟨.arrow h₁ h₂⟩⟩
  | CTY (α × β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size

    ⟨(m + n).succ, ⟨.prod h₁ h₂⟩⟩
  | CTY Base => ⟨1, ⟨.base⟩⟩

theorem Size.sound (_h : size e = ⟨n, ⟨h⟩⟩) : Size e n := h

theorem Size.complete (h : Size e n) : size e = ⟨n, .up h⟩ := by
  induction h with
  | base => rfl
  | arrow h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | prod h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]

end CTy

namespace CcExpr

inductive TySize : CcExpr → ℕ → Prop
  | id     : CTy.Size α m
    → TySize (CC Id(α)) m.succ
  | id'    : TySize (CC Id) 1
  | comp   : TySize f m
    → TySize g n
    → TySize (CC f ∘ g) (m + n).succ
  | pair   : TySize f m
    → TySize g n
    → TySize (CC ⟨f, g⟩) (m + n).succ
  | fst    : CTy.Size α m
    → CTy.Size β n
    → TySize (CC Fst(α, β)) (m + n).succ
  | fst'   : TySize (CC Fst) 1
  | snd    : CTy.Size α m
    → CTy.Size β n
    → TySize (CC Snd(α, β)) (m + n).succ
  | snd'   : TySize (CC Snd) 1
  | curr   : TySize x m → TySize (CC Λ(x)) m.succ
  | app_e  : CTy.Size α m
    → CTy.Size β n
    → TySize (CC App(δ, τ)) (m + n).succ
  | app_e' : TySize (CC App) 1
  | coup   : TySize a m → TySize b n → TySize (CC (a, b)) (m + n).succ
  | sk     : TySize (.sk _e) 1
  | sort   : TySize (CC Sort _m) 1
  | app    : TySize f m → TySize x n → TySize (CC (f x)) (m + n)

def ty_size (e : CcExpr) : ((n : ℕ) × (PLift (TySize e n))) :=
  match e with
  | .sk _e     => ⟨1, ⟨.sk⟩⟩
  | CC Sort _m => ⟨1, ⟨.sort⟩⟩
  | CC Id(α)  =>
    let ⟨m, ⟨h⟩⟩ := α.size
    ⟨m.succ, ⟨.id h⟩⟩
  | CC Id => ⟨1, ⟨.id'⟩⟩
  | CC (f ∘ g) =>
    let ⟨m, ⟨h₁⟩⟩ := f.ty_size
    let ⟨n, ⟨h₂⟩⟩ := g.ty_size
    ⟨(m + n).succ, ⟨.comp h₁ h₂⟩⟩
  | CC (a, b) =>
    let ⟨m, ⟨h₁⟩⟩ := a.ty_size
    let ⟨n, ⟨h₂⟩⟩ := b.ty_size
    ⟨(m + n).succ, ⟨.coup h₁ h₂⟩⟩
  | CC ⟨a, b⟩ =>
    let ⟨m, ⟨h₁⟩⟩ := a.ty_size
    let ⟨n, ⟨h₂⟩⟩ := b.ty_size
    ⟨(m + n).succ, ⟨.pair h₁ h₂⟩⟩
  | CC Fst(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    ⟨(m + n).succ, ⟨.fst h₁ h₂⟩⟩
  | CC Fst => ⟨1, ⟨.fst'⟩⟩
  | CC Snd(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    ⟨(m + n).succ, ⟨.snd h₁ h₂⟩⟩
  | CC Snd => ⟨1, ⟨.snd'⟩⟩
  | CC Λ(x) =>
    let ⟨m, ⟨h⟩⟩ := x.ty_size
    ⟨m.succ, ⟨.curr h⟩⟩
  | CC App(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    ⟨(m + n).succ, ⟨.app_e h₁ h₂⟩⟩
   | CC App => ⟨1, ⟨.app_e'⟩⟩
   | CC (f x) =>
    let ⟨m, ⟨h₁⟩⟩ := f.ty_size
    let ⟨n, ⟨h₂⟩⟩ := x.ty_size
    ⟨(m + n), ⟨.app h₁ h₂⟩⟩

end CcExpr
