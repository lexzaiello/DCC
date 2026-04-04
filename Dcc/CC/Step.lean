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
  | _                                => .none

theorem IsRedex.sound (_h : Expr.is_redex e = .some he) : IsRedex e := he.down

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

theorem no_zero_size' : size e ≠ ⟨0, ⟨h⟩⟩ := by
  intro ha
  have h := h.no_zero
  simp_all only [ne_eq, not_true_eq_false]

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

/-
Π(m, n) A B x -> B ⟦Id(Sort m)⟧(a, x)
-/

inductive Red : Expr → Expr → Prop
  | refl_sig  : Red (DCC Σ(a, b)) (DCC Σ(a, b))
  | refl_app  : Red (DCC App(_δ, _τ)) (DCC App(_δ, _τ))
  | refl_fst  : Red (DCC Fst(_δ, _τ)) (DCC Fst(_δ, _τ))
  | refl_snd  : Red (DCC Snd(_δ, _τ)) (DCC Snd(_δ, _τ))
  | refl_id   : Red (DCC Id(_α)) (DCC Id(_α))
  | refl_pi   : Red (DCC Π(m, n)) (DCC Π(m, n))
  | refl_quot : Red (DCC `(_α, _β, x)) (DCC `(_α, _β, x))
  | refl_curr : Red (DCC Λ(_β, _x)) (DCC Λ(_β, _x))
  | refl_pair : Red (DCC ⟦β⟧⟨_f, _g⟩) (DCC ⟦β⟧⟨_f, _g⟩)
  | refl_sort : Red (DCC Sort m) (DCC Sort m)
  | refl_comp : Red (DCC f ∘ g)  (DCC f ∘ g)
  | app       : Red (DCC (f x)) e' → Red (DCC (App(_δ, _τ) ⟦β⟧(f, x))) e'
  | fst       : Red a a' → Red (DCC (Fst(_δ, _τ) ⟦β⟧(a, b))) a'
  | snd       : Red b b' → Red (DCC (Snd(_δ, _τ) ⟦β⟧(a, b))) b'
  | id        : Red x x' → Red (DCC (Id(_α) x)) x'
  | quot      : Red x x' → Red (DCC (`(_α, _β, x) y)) x'
  | comp      : Red (DCC (x (y z))) e' → Red (DCC ((x ∘ y) z)) e'
  | pair      : Red (DCC (f x)) a'
    → Red (DCC (g x)) b'
    → Red (DCC (⟦β⟧⟨f, g⟩ x)) (DCC ⟦β⟧(a', b'))
  | curr      : Red (DCC (x ⟦β⟧(y, z))) e' → Red (DCC (Λ(β, x) y z)) e'
  | sigl      : ¬ HasRedex b → Red a a' → Red (DCC ⟦β⟧(a, b)) (DCC ⟦β⟧(a', b))
  | sigr      : Red b b'     → Red (DCC ⟦β⟧(a, b)) (DCC ⟦β⟧(a, b'))
  | congrFun  : ¬ HasRedex x → ¬ IsRedex (DCC (f x)) → Red f f' → Red (DCC (f x)) (DCC (f' x))
  | congrArg  : ¬ IsRedex (DCC (f x)) → Red x x' → Red (DCC (f x)) (DCC (f x'))

def red_par (e : Expr) : ((e' : Expr) × PLift (Red e e')) :=
  if h : e.IsRedex then
    match e with
    | DCC (App(_δ, _τ) ⟦β⟧(f, x)) =>
      have _h : (f.app x).size.fst < ((_δ.appl _τ).app (β.mk f x)).size.fst := by
        simp only [size, Nat.succ_eq_add_one]
        grind
      let ⟨e', ⟨h⟩⟩ := (DCC (f x)).red_par
      ⟨e', ⟨.app h⟩⟩
    | DCC (Fst(_α, _β) ⟦_γ⟧(a, b)) =>
      have _h : a.size.fst < ((_α.fst _β).app (_γ.mk a b)).size.fst := by
        simp only [size, Nat.succ_eq_add_one]
        grind
      let ⟨a', ⟨h⟩⟩ := a.red_par
      ⟨a', ⟨.fst h⟩⟩
    | DCC (Snd(_α, _β) ⟦_γ⟧(a, b)) =>
      have _h : b.size.fst < ((_α.snd _β).app (_γ.mk a b)).size.fst := by
        simp only [size, Nat.succ_eq_add_one]
        grind
      let ⟨b', ⟨h⟩⟩ := b.red_par
      ⟨b', ⟨.snd h⟩⟩
    | DCC (`(_α, _β, x) y) =>
      have _h : x.size.fst < ((_α.quot _β x).app y).size.fst := by
        simp only [size, Nat.succ_eq_add_one]
        grind
      let ⟨x', ⟨h⟩⟩ := x.red_par
      ⟨x', ⟨.quot h⟩⟩
    | DCC (Id(_α) x) =>
      have _h : x.size.fst < (_α.id.app x).size.fst := by
        simp only [size, Nat.succ_eq_add_one, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
      let ⟨x', ⟨h⟩⟩ := x.red_par
      ⟨x', ⟨.id h⟩⟩
    | DCC ((f ∘ g) x) =>
      have _h : (f.app (g.app x)).size.fst < ((f.comp g).app x).size.fst := by
        simp [size]
        grind
      let ⟨e', ⟨h⟩⟩ := (DCC (f (g x))).red_par
      ⟨e', ⟨.comp h⟩⟩
    | DCC (⟦β⟧⟨f, g⟩ x) =>
      have _h₁ : (f.app x).size.fst < ((β.pair f g).app x).size.fst := by
        simp only [size, Nat.succ_eq_add_one, add_lt_add_iff_right]
        grind
      have _h₂ : (g.app x).size.fst < ((β.pair f g).app x).size.fst := by
        simp only [size, Nat.succ_eq_add_one, add_lt_add_iff_right]
        grind
      let ⟨a', ⟨h₁⟩⟩ := red_par (DCC (f x))
      let ⟨b', ⟨h₂⟩⟩ := red_par (DCC (g x))
      ⟨DCC ⟦β⟧(a', b'), ⟨.pair h₁ h₂⟩⟩
    | DCC (Λ(β, x) y z) =>
      have _h : (x.app (β.mk y z)).size.fst < (((β.curr x).app y).app z).size.fst := by
        simp [size]
        grind
      let ⟨e', ⟨h⟩⟩ := red_par (DCC (x ⟦β⟧(y, z)))
      ⟨e', ⟨.curr h⟩⟩
  else
    match e with
    | DCC Sort m       => ⟨DCC Sort m, ⟨.refl_sort⟩⟩
    | DCC App(_δ, _τ)  => ⟨DCC App(_δ, _τ), ⟨.refl_app⟩⟩
    | DCC Fst(_δ, _τ)  => ⟨DCC Fst(_δ, _τ), ⟨.refl_fst⟩⟩
    | DCC Snd(_δ, _τ)  => ⟨DCC Snd(_δ, _τ), ⟨.refl_snd⟩⟩
    | DCC Id(_α)       => ⟨DCC Id(_α), ⟨.refl_id⟩⟩
    | DCC Λ(_β, _x)    => ⟨DCC Λ(_β, _x), ⟨.refl_curr⟩⟩
    | DCC App(_β, _x)  => ⟨DCC App(_β, _x), ⟨.refl_app⟩⟩
    | DCC ⟦_β⟧⟨_a, _b⟩ => ⟨DCC ⟦_β⟧⟨_a, _b⟩, ⟨.refl_pair⟩⟩
    | DCC Σ(a, b)      => ⟨DCC Σ(a, b), ⟨.refl_sig⟩⟩
    | DCC Π(m, n)      => ⟨DCC Π(m, n), ⟨.refl_pi⟩⟩
    | DCC `(α, β, x)   => ⟨DCC `(α, β, x), ⟨.refl_quot⟩⟩
    | DCC f ∘ g        => ⟨DCC f ∘ g, ⟨.refl_comp⟩⟩
    | DCC ⟦β⟧(a, b)    =>
      if h₁ : ¬ b.HasRedex then
        have _h : a.size.fst < (β.mk a b).size.fst := by
          simp [size]
          grind
        let ⟨a', ⟨h₂⟩⟩ := a.red_par
        ⟨DCC ⟦β⟧(a', b), ⟨.sigl h₁ h₂⟩⟩
      else
        have _h : b.size.fst < (β.mk a b).size.fst := by
          simp [size]
          grind
        let ⟨b', ⟨h₂⟩⟩ := b.red_par
        ⟨DCC ⟦β⟧(a, b'), ⟨.sigr h₂⟩⟩
    | DCC (f x) =>
      have h₁ : ¬ (DCC (f x)).IsRedex := by
        simp_all
      if h₂ : ¬ x.HasRedex then
        have _h : f.size.fst < (f.app x).size.fst := by
          simp [size]
          
        let ⟨f', ⟨h⟩⟩ := f.red_par
        ⟨DCC (f' x), ⟨.congrFun h₂ h₁ h⟩⟩
      else
        let ⟨x', ⟨h⟩⟩ := x.red_par
        ⟨DCC (f x'), ⟨.congrArg h₁ h⟩⟩
termination_by e.size.fst

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

end Expr
