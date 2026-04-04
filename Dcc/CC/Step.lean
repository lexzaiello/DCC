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
  | pi     : IsRedex (DCC (Π(m, n) A B x))

inductive HasRedex : Expr → Prop
  | single : IsRedex a  → HasRedex a
  | left   : HasRedex f → HasRedex (DCC (f x))
  | right  : HasRedex x → HasRedex (DCC (f x))
  | sigl   : HasRedex a → HasRedex (DCC ⟦β⟧(a, b))
  | sigr   : HasRedex b → HasRedex (DCC ⟦β⟧(a, b))

def is_redex (e : Expr) : Option (PLift e.IsRedex) :=
  match e with
  | (DCC (App(_δ, _τ) ⟦_β⟧(_a, _b))) => .some ⟨.app⟩
  | (DCC (Fst(_δ, _τ) ⟦_β⟧(_a, _b))) => .some ⟨.fst⟩
  | (DCC (Snd(_δ, _τ) ⟦_β⟧(_a, _b))) => .some ⟨.snd⟩
  | (DCC (Id(_α) _x))                => .some ⟨.id⟩
  | (DCC (`(_α, _β, _x) _y))             => .some ⟨.quot⟩
  | (DCC ((_x ∘ _y) _z))             => .some ⟨.comp⟩
  | (DCC (⟦_β⟧⟨_f, _g⟩ _x))          => .some ⟨.pair⟩
  | (DCC (Λ(_β, _x) _y _z))          => .some ⟨.curr⟩
  | (DCC (Π(_m, _n) _α _β _x))       => .some ⟨.pi⟩
  | _                                => .none

theorem IsRedex.sound (_h : Expr.is_redex e = .some he) : IsRedex e := he.down

theorem IsRedex.complete (h : IsRedex e) : is_redex e = .some (.up h) := by
  match h with
  | .quot | .id | .pi | .snd | .fst | .comp | .curr | .app | .pair =>
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
    | (DCC ⟦_β⟧(x, y)) => match _heq₂ : x.has_redex, _heq₃ : y.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.sigl h⟩
      | _, .some ⟨h⟩ => .some ⟨.sigr h⟩
      | _, _ => .none
    | (DCC (f x)) => match _heq₂ : f.has_redex, _heq₃ : x.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.left h⟩
      | _, .some ⟨h⟩ => .some ⟨.right h⟩
      | _, _ => .none
    | _e => .none

@[simp] theorem HasRedex.sound (_h : Expr.has_redex e = .some he) : HasRedex e := he.down

@[simp] theorem sig_not_redex : ¬ IsRedex (DCC ⟦_β⟧(_a, _b)) := fun h => by
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

/-
Π(m, n) A B x -> B ⟦Id(Sort m)⟧(a, x)
-/

inductive Red : Expr → Expr → Prop
  | app      : Red (DCC (App(_δ, _τ) ⟦β⟧(f, x))) (DCC (f x))
  | fst      : Red (DCC (Fst(_δ, _τ) ⟦β⟧(a, b))) a
  | snd      : Red (DCC (Snd(_δ, _τ) ⟦β⟧(a, b))) a
  | id       : Red (DCC (Id(_α) x)) x
  | quot     : Red (DCC (`(_α, _β, x) y)) x
  | comp     : Red (DCC ((x ∘ y) z)) (DCC (x (y z)))
  | pair     : Red (DCC (f x)) a'
    → Red (DCC (g x)) b'
    → Red (DCC (⟦β⟧⟨f, g⟩ x))  (DCC ⟦β⟧(a', b'))
  | curr     : Red (DCC (Λ(β, x) y z)) (DCC (x ⟦β⟧(y, z)))
  | sigl     : ¬ HasRedex b → Red a a' → Red (DCC ⟦β⟧(a, b)) (DCC ⟦β⟧(a', b))
  | sigr     : Red b b'     → Red (DCC ⟦β⟧(a, b)) (DCC ⟦β⟧(a, b'))
  | congrFun : ¬ HasRedex x → ¬ IsRedex (DCC (f x)) → Red f f' → Red (DCC (f x)) (DCC (f' x))
  | congrArg : ¬ IsRedex (DCC (f x)) → Red x x' → Red (DCC (f x)) (DCC (f x'))

inductive Size : Expr → ℕ → Prop
  | sort   : Size (DCC Sort m) 1
  | id     : Size (DCC Id(_α)) 1
  | quot   : Size (DCC `(_α, _β, _x)) 1
  | comp   : Size f m → Size g n → Size (DCC (f ∘ g)) (m + n).succ
  | coup   : Size f m → Size g n → Size (DCC ⟦β⟧(f, g)) (m + n).succ
  | pair   : Size f m → Size g n → Size (DCC ⟦β⟧⟨f, g⟩) (m + n).succ
  | fst    : Size (DCC Fst(_α, _β)) 1
  | snd    : Size (DCC Snd(_α, _β)) 1
  | curr   : Size x m → Size (DCC Λ(β, x)) m.succ.succ
  | pi     : Size (DCC Π(_m, _n)) 1
  | appl   : Size (DCC App(_α, _β)) 1
  | app    : Size f m → Size x n → Size (DCC (f x)) (m + n)
  | sig    : Size (DCC Σ(_α, _β)) 1

def size (e : Expr) : ((n : ℕ) × (PLift (Size e n))) :=
  match e with
  | DCC Sort _m => ⟨1, ⟨.sort⟩⟩
  | DCC Σ(_α, _β) => ⟨1, ⟨.sig⟩⟩
  | DCC Id(_α)  => ⟨1, ⟨.id⟩⟩
  | DCC `(_α, _β, _x)  => ⟨1, ⟨.quot⟩⟩
  | DCC (f ∘ g) =>
    let ⟨m, ⟨h₁⟩⟩ := f.size
    let ⟨n, ⟨h₂⟩⟩ := g.size
    ⟨(m + n).succ, ⟨.comp h₁ h₂⟩⟩
  | DCC ⟦_β⟧(a, b) =>
    let ⟨m, ⟨h₁⟩⟩ := a.size
    let ⟨n, ⟨h₂⟩⟩ := b.size
    ⟨(m + n).succ, ⟨.coup h₁ h₂⟩⟩
  | DCC ⟦_β⟧⟨a, b⟩ =>
    let ⟨m, ⟨h₁⟩⟩ := a.size
    let ⟨n, ⟨h₂⟩⟩ := b.size
    ⟨(m + n).succ, ⟨.pair h₁ h₂⟩⟩
  | DCC Fst(_α, _β) => ⟨1, ⟨.fst⟩⟩
  | DCC Snd(_α, _β) => ⟨1, ⟨.snd⟩⟩
  | DCC Λ(_β, x) =>
    let ⟨m, ⟨h⟩⟩ := x.size
    ⟨m.succ.succ, ⟨.curr h⟩⟩
  | DCC Π(_m, _n) =>
    ⟨1, ⟨.pi⟩⟩
  | DCC App(_α, _β) => ⟨1, ⟨.appl⟩⟩
  | DCC (f x) =>
    let ⟨m, ⟨h₁⟩⟩ := f.size
    let ⟨n, ⟨h₂⟩⟩ := x.size
    ⟨(m + n), ⟨.app h₁ h₂⟩⟩

theorem Size.sound (_h : Expr.size e = ⟨n, ⟨h⟩⟩) : Size e n := h

theorem Size.complete (h : Size e n) : size e = ⟨n, .up h⟩ := by
  induction h with
  | pi | quot | sig | sort | id | fst | snd | appl => rfl
  | curr h ih =>
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

/-
Π B A x

(Σ A (= x))

Π B A x

B receives ⟦x, refl x⟧

refl x : (x = x)

refl x : = A x x

need explicit α and β argument for couples,
but this is super annoying.

would be nicer if we could instead elevate a couple
to a sigma pair?

we could just have the default β argument
be fun _ => B

how does this change how pairs work?
I think we would need the β argument here too.

⟨f, g⟩ x = ⟦f x, g x⟧

Sigma.mk α β x y

id : Π

Π A B x = ⟦Id(Sort m)⟧(A, x)

α → β = Π(m, n) A `(Σ α, Id(α))
-/

def arrow (α β : Expr) (m n : Level) : Expr :=
  DCC (Π(m, n) α `(Sort n, Σ(Sort m, Id(Sort m)), β))

def Pi.type (m n : Level) : Expr :=
  arrow (DCC Sort m)
    (arrow
      (arrow
        (DCC (Σ(Sort m, Id(Sort m))))
        (DCC Sort n) m.succ n.succ)
      (DCC Sort n) n.succ n.succ) m.succ n.succ

def Pi.type₁ (m n : Level) : Expr :=
  arrow
    (arrow
      (DCC (Σ(Sort m, Id(Sort m))))
        (DCC Sort n) m.succ n.succ)
      (DCC Sort n) n.succ n.succ

inductive Judge : Expr → Expr → Prop
  | id    : Judge α (DCC (Sort m))
    → Judge (DCC Id(α)) (arrow α α m m)
  -- g : Π β A
  | comp  : Judge g (arrow α β m n)
    → Judge f (DCC (Π(n, o) β γ))
    → Judge (DCC f ∘ g) (DCC (Π(m, o) α (γ ∘ g)))
  -- f  : α → τ₁
  -- α  : Sort m
  -- τ₁ : Sort n
  -- β : τ₁ → Sort o
  -- g : DCC (Π(m, o) α (β ∘ f ∘ Snd(Sort m, Id(Sort m))))
  -- β :
  -- ⟦β⟧⟨a, b⟩ : α → (Σ τ₁ β)
  -- this is essentially substitution in the category of contexts
  -- y₀ : B₀, y₁ : B₁(y₀)
  | pair  : Judge β (arrow τ₁ (DCC Sort o) n o.succ)
    → Judge f (arrow α τ₁ m n)
    → Judge g (DCC (Π(m, o) α (β ∘ f ∘ Snd(Sort m, Id(Sort m)))))
    → Judge (DCC ⟦β⟧⟨f, g⟩) (arrow α (DCC Σ(τ₁, β)) m (max n o))
  -- fst(α, β) : (Σ α β) → α
  | fst   : Judge α (DCC Sort m)
    → Judge β (arrow α (DCC Sort n) m n.succ)
    → Judge (DCC Fst(α, β)) (arrow (DCC Σ(α, β)) α (max m n) m)
  /- snd(α, β) : 
  -/
  | snd   : Judge α (DCC Sort m)
    → Judge β (arrow α (DCC Sort n) m n.succ)
    → Judge (DCC Snd(α, β)) (DCC (Π(max m n, n)
    Σ(α, β) (β ∘ Fst(α, β) ∘ Snd(Sort (max m n), Id(Sort (max m n))))))
  /-
    App f x types are nondependent.
    At least, x does not depend on x. need to bake that into ⟦β⟧
    x : Π(max m n, o) (Σ α, β) γ
    γ : (Σ α, β) → Sort o
    γ : arrow (DCC (Σ(m, n) α β)) (DCC Sort o) (max m n) o.succ
    (Π(m, o) α 
      (App(Pi.type₁ n o, arrow (`(#(Pi.type₁ n o), arrow (DCC (Σ(m, n) α β)) (DCC Sort o) (max m n) o.succ))) ∘
        ⟦`(#(Pi.type₁ n o), arrow (DCC (Σ(m, n) α β)) (DCC Sort o) (max m n) o.succ)⟧⟨Π(n, o) ∘ β ∘ Snd(Sort m, Id(Sort m)), `((Σ(m.succ, m) (Sort m) Id(Sort m)), γ)⟩))
    Λ(x) : Π(m, o) α (
      App(?, ?)
        ∘ ⟦`(#(arrow (DCC Sort o), Sort o)⟧⟨Π(n, o) ∘ (β ∘ Snd(Sort m, Id(Sort m))), `((Σ(m.succ, m) (Sort m) (Id(Sort m))), γ)⟩
      β ∘ Snd(Sort m, Id(Sort m))
  -/
  | curr  : Judge x (DCC (Π(max m n, o) Σ(α, β) γ))
    → Judge (DCC Λ(β, x)) (DCC (Π(m, o) α
      (App(`(Sort o.succ, #(arrow (DCC Σ(α, β)) (DCC Sort o) (max m n) o.succ), Sort o),
        #(arrow (DCC Σ(α, β)) (DCC Sort o) (max m n) o.succ)) ∘
        ⟦`(Sort o.succ, #(Pi.type₁ n o), #(arrow (DCC Σ(α, β)) (DCC Sort o) (max m n) o.succ))⟧⟨
          Π(n, o) ∘ β ∘ Snd(Sort m, Id(Sort m)),
          `(#(arrow (DCC Σ(α, β)) (DCC Sort o) (max m n) o.succ), Σ(Sort m, Id(Sort m)), γ)⟩)))
  /-
    App(γ, β) : (Π(max o n, o)
      (Σ(o, n) (Π(n, o) β γ) `((Π(n, o) β γ), β))
      (γ ∘ (Snd((Π(n, o) β γ), `((Π(n, o) β γ), β)) ∘ Snd(Sort (max o n), Id(Sort (max o n))))))
  -/
  | app_e : Judge β (DCC Sort n)
    → Judge γ (arrow β (DCC (Sort o)) n o.succ)
    → Judge (DCC App(γ, β)) (DCC (Π(max o n, o)
      Σ((Π(n, o) β γ), `(Sort n, (Π(n, o) β γ), β))
      (γ ∘ (Snd((Π(n, o) β γ), `(Sort n, (Π(n, o) β γ), β)) ∘ Snd(Sort (max o n), Id(Sort (max o n)))))))
  /-
    a : α
    b : β a
    ⟦β⟧(a, b) : Σ α β
  -/
  | coup  : Judge a α
    → Judge b (DCC (β a))
    → Judge (DCC ⟦β⟧(a, b)) (DCC Σ(α, β))
  -- Can derive dependent quotation
  | quot  : Judge α (DCC Sort m)
    → Judge β (DCC Sort m)
    → Judge x α
    → Judge (DCC `(α, β, x)) (arrow α (arrow β α n m) m m)
  | app   : Judge f (DCC (Π(m, n) α β)) → Judge x α
    → Judge (DCC (f x)) (DCC (β ⟦Id(Sort m)⟧(α, x)))
  | sort  : Judge (DCC Sort m) (DCC Sort m.succ)

inductive TySize : Expr → ℕ → Prop
  | id     : TySize α m
    → TySize (DCC Id(α)) m.succ
  | comp   : TySize f m
    → TySize g n
    → TySize (DCC f ∘ g) (m + n + 1)
  | pair   : TySize β m
    → TySize a n
    → TySize b o
    → TySize (DCC ⟦β⟧⟨a, b⟩) (m + n + o).succ
  | fst    : TySize α m
    → TySize β n
    → TySize (DCC Fst(α, β)) (m + n + 1)
  | snd    : TySize α m
    → TySize β n
    → TySize (DCC Snd(α, β)) (m + n + 1)
  | curr   : TySize β m → TySize x n → TySize (DCC Λ(β, x)) (m + n).succ
  | pi     : TySize (DCC Π(m, n)) 1
  | sig    : TySize α m → TySize β n → TySize (DCC Σ(α, β)) (m + n).succ
  | appl   : TySize α m
    → TySize β n
    → TySize (DCC App(α, β)) (m + n + 1)
  | coup   : TySize β m → TySize a n → TySize b o → TySize (DCC ⟦β⟧(a, b)) (m + n + o).succ
  | quot   : TySize α m → TySize β n → TySize (DCC `(α, β, x)) (m + n).succ
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
    ⟨m + n + 1, ⟨.comp h₁ h₂⟩⟩
  | DCC ⟦β⟧(a, b) =>
    let ⟨m, ⟨h₁⟩⟩ := β.ty_size
    let ⟨n, ⟨h₂⟩⟩ := a.ty_size
    let ⟨o, ⟨h₃⟩⟩ := b.ty_size
    ⟨(m + n + o).succ, ⟨.coup h₁ h₂ h₃⟩⟩
  | DCC `(α, β, _x) =>
    let ⟨m, ⟨h₁⟩⟩ := α.ty_size
    let ⟨n, ⟨h₂⟩⟩ := β.ty_size
    ⟨(m + n).succ, ⟨.quot h₁ h₂⟩⟩
  | DCC ⟦β⟧⟨a, b⟩ =>
    let ⟨m, ⟨h₁⟩⟩ := β.ty_size
    let ⟨n, ⟨h₂⟩⟩ := a.ty_size
    let ⟨o, ⟨h₃⟩⟩ := b.ty_size
    ⟨(m + n + o).succ, ⟨.pair h₁ h₂ h₃⟩⟩
  | DCC Σ(a, b) =>
    let ⟨m, ⟨h₁⟩⟩ := a.ty_size
    let ⟨n, ⟨h₂⟩⟩ := b.ty_size
    ⟨(m + n).succ, ⟨.sig h₁ h₂⟩⟩
  | DCC Fst(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.ty_size
    let ⟨n, ⟨h₂⟩⟩ := β.ty_size
    ⟨(m + n + 1), ⟨.fst h₁ h₂⟩⟩
  | DCC Snd(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.ty_size
    let ⟨n, ⟨h₂⟩⟩ := β.ty_size
    ⟨(m + n + 1), ⟨.snd h₁ h₂⟩⟩
  | DCC Λ(β, x) =>
    let ⟨m, ⟨h₁⟩⟩ := β.ty_size
    let ⟨n, ⟨h₂⟩⟩ := x.ty_size
    ⟨(m + n).succ, ⟨.curr h₁ h₂⟩⟩
  | DCC Π(m, n) =>
    ⟨1, ⟨.pi⟩⟩
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
  | quot h₁ h₂ ih₁ ih₂ =>
    unfold ty_size
    rw [ih₁, ih₂]
  | curr h₁ h₂ ih₁ ih₂ =>
    unfold ty_size
    rw [ih₁, ih₂]
  | pi => unfold ty_size; rfl
  | id h ih =>
    unfold ty_size
    rw [ih]
  | comp h₁ h₂ ih₁ ih₂ =>
    unfold ty_size
    rw [ih₁, ih₂]
  | coup h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    unfold ty_size
    rw [ih₁, ih₂, ih₃]
  | pair h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    unfold ty_size
    rw [ih₁, ih₂, ih₃]
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

namespace Red

theorem ty_size_decreasing : Red e e' → e'.ty_size.fst < (Expr.ty_size e).fst := by
  intro hred
  induction hred with
  | app | comp | snd | fst | sigr | sigl | pi | curr =>
    simp [Expr.ty_size]
    grind
  | id =>
    simp [Expr.ty_size]
  | pair =>
    simp [ty_size] at *
    
    sorry

end Red

end Expr
