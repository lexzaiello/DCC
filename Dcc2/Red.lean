import Dcc2.Ast
import Mathlib.Tactic

/-
Our size measure can actually be more complex with this setup.

The size can actually potentially be a proper function for Comb.
That is, the size should be determined by Γ, not just adding the components together.
-/

/-
Unification works the same as before, OTT/univalent/my style, except we do not use holes.

We do, but we say every type is either inhabited, in which case we can produce a hole, or
it is isomoprhic to 𝟘.

Unification reflexivity is the same as usual, however.

Except that now we can decide = within a program.

u : Level    A : Sort u  v : Level  s : Level
B : (X Y : A) → (heq : X = Y)      → Sort v
C : (X Y : A) → (hneq : X = Y → 𝟘) → Sort s
case_true  : (X Y : A) → (heq : X = Y)      → B X Y heq
case_false : (X Y : A) → (hneq : X = Y → 𝟘) → C X Y hneq
--------------------------------------------------------------
$ Comb.dom (, (, 1 =.decide) u A v s B C case_true case_false)
 := (Σ (`A (Sort u) A))

u : Level    A : Sort u  v : Level  s : Level
B : (X Y : A) → (heq : X = Y)      → Sort v
C : (X Y : A) → (hneq : X = Y → 𝟘) → Sort s
case_true  : (X Y : A) → (heq : X = Y)      → B X Y heq
case_false : (X Y : A) → (hneq : X = Y → 𝟘) → C X Y hneq
--------------------------------------------------------------
$ Comb.cod (, (, 1 =.decide) u A v s B C case_true case_false)
 := $ (, (, 1 =.decide) ? ? ? (Level.succ v) (Level.succ s) ? ? B C)

$ (, (, 1 =.decide) u A v s B C case_true case_false) (, X X) := case_true

harcode assume no congruence on X.
we will fix later.

There is a design fork:
- do we want to go the η affine extensional route
  - obviously, we can match on 𝟙₂ and 𝟘₂, so if both f : 𝟚 → B and g : 𝟚 → B,
    then our hole could not possibly check all values.
    Because we also have ℕ. And we can recurse on ℕ and match it.
  - every combinator has a way to substitute its domain, mutating Γ
    - such that it is invertible and f is the same ($ Comb.subst (, ($ Comb.subst (, c A')) ($ Comb.dom c))) = c
    - we show that a given relation r on r (f x) B ↔ r (f.subst Hole hole) C
      - That is, we show that holes preserve behavior?
    
  - every combinator comes equipped with an extensionality principle.
    $ Comb.η : (× (c : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c)))
    $ Comb.ext (Id (: 1 Level) Hole) : (Σ (f : Hole → hole) (heq : (f Hole.mk) = hole.mk), η f = (Id (: 1 Level) Hole))
    - Substitute the context such that A becomes hole?
    - Define extensionality principle on the hole domain, then
      substitute context recursively to preseve the shape
      so we see everything that's going on and say that the η-reductions
      are the same.
  - equality of functions is defined as β + η
- or the OTT route

Function extensionality is possible because we have affine types, and parametricity applies with respect to the domain since
we cannot actually perform case analysis on the type itself. We need some way to substitute the domain into a hole,
then η-reduce based on the resutling shape, then substitute back.

We may not actually need to generate the right shape exactly. Substitution does all we need.
Plus parametricity.

  $ Comb.subst : (Σ (c : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c))) (Σ (u' : Level), (A' : Sort u))) →
    (Σ (Δ : Comb.sig (.succ n) c), Comb.dom (, Fst c Δ) = A')
  $ Comb.subst_inv : (x : (Σ (c : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c))) (Σ (u' : Level), (A' : Sort u)))) → Comb.subst x = Fst x

  - Comb.subst should be invertible.

  $ Comb.η : (Σ (c : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c))) (x : Hole) (e' : Comb.cod (, c x)) (heq : ($ ($ (, (, 2 "=") Hole) ($ β ($ c ))) → (Σ (c : Comb (.succ n)), (Δ : Comb.sig (.succ n) c))

things to do:
- quotation
- projection
- composition
- =.decide so that unify works natively
  =.decide should work on lists

size should also be definable on terms themselves in the calculus.

Full normal form is with $ β : (Σ (u : Level) (τ : Sort u), τ) → (Σ (u : Level) (τ : Sort u), τ)

Things to do:
- Want to separate head reductions into an inductive (don't require any assumptions)
- Make congrArg universal with View$ and ViewCurr, guard these in head reductions
- β for base types
- Comb.subst for Id
- Comb.subst_inv for Id
- Comb.η for Id case

we cannot substitute Fst always because its domain will always be of the form Σ ...
Hole is a predicate on types.

A Hole has to represent all possible behavior. does it?
not really.

It just means some operations are η-reducible through recursion and others are not.

Why did function extensionality fail in the past?
Because we did not show that it was total. It did not cover all possible combinators.

However, Fst and Snd always do different things. Do they?
Fst (, x x) = Snd (, x x)

All combinators should come with a proof that all functions of the same domain
that produce the same result are coercible into each other.

The coercion is important.

Because not every type can come with a hole.
A combinator is only definable if it passes funext.

Id always passes funext.
I really want to make substitution + parametricity work.

Substitution should not mean producing the same combinator with a different domain.
It should just mean inhabiting a function of the new domain, such that the
inhabitant can be reversed back into the original.

And this is done by just keeping the original? nah.

The basic case is Bool.Cases

why can't we just naively plug in a hole?
because that doesn't type-check.

because holes aren't inhabitants of everything.

not every combinator is parametric, and not every combinator needs to be parametric.
We can have a predicate Comb.Isparametric

If it is parametric, then funext obviously holds.
If it is not parametric, then it is reducible to asking if it's a recursor.

  - If it's a recursor, it's reducible to asking if it's computably enumerable
      - e.g., we can test all bool cases
    - however, the maximum depth we definitely can determine from the usage of the recursor
      it's not infinite. Its type might say a statement about all natural numbers
      but a human cannot explicitly handle all of them, so the question is bounded by the size.
      To a degree.
      - The only cases where a different thing can happen need to be explicitly written

So comb.subst for everything parametric, meaning we can change the domain to Hole
That we can prove extensionality for easily.

If parametricity is decidable, I am fine with having just that and leaving the rest out.
As long as we have extensional equality reflection.
That is fine.

TODO: β + η so we can get the type-checker working.

Oh question. How will holes work? η-reduction as well?
idk.

e.g., Id _ A

_ : Hole, so this doesn't align with the signature.
We will figure it out.

Also how will we unify different Σ types together?
Also will figure that out.
-/

class ProofEq (r : Expr → Expr → Type) where
  proof_eq : ∀ (h₁ h₂ : r A B), h₁ = h₂

class Deterministic (r : Expr → Expr → Type) where
  unique : ∀ {A B C} (_h₁ : r A B) (_h₂ : r A C), B = C

class PushHead (r : Expr → Expr → Type) where
  push_head : (r B C) → (r A B) → (r A C)

open ProofEq
open Deterministic
open PushHead

namespace Dsl


scoped syntax "Comb.u_dom" : expr
scoped syntax "Comb.u_cod" : expr
scoped syntax "Comb.dom"   : expr
scoped syntax "Comb.cod"   : expr
scoped syntax "Comb.type"  : expr
scoped syntax "Id"         : expr
scoped syntax "Snd"        : expr
scoped syntax "Sort₀"      : expr
scoped syntax "Σ₀"         : expr
scoped syntax "Id₀"        : expr
scoped syntax "Comb.sig"   : expr
scoped syntax "Quot"       : expr
scoped syntax "Snd"        : expr

macro_rules
  | `(DCC' Comb.sig) => `(DCC' (,_ (,Comb 1 ((' Comb.sig) 1)) (∗ 0)))
  | `(DCC' Σ₀) => `(DCC' (,Comb.sig (,Comb 1 ((' Σ) 1)) (∗ 0)))
  | `(DCC' Sort₀) => `(DCC' (,Comb.sig (,Comb 1 ((' Sort) 1)) (∗ 0)))
  | `(DCC' Comb.u_dom)   => `(DCC' (,Comb.sig (,Comb 1 ((' Comb.u_dom) 1)) (∗ 0)))
  | `(DCC' Comb.u_cod)   => `(DCC' (,Comb.sig (,Comb 1 ((' Comb.u_cod) 1)) (∗ 0)))
  | `(DCC' Comb.dom)     => `(DCC' (,Comb.sig (,Comb 1 ((' Comb.dom) 1)) (∗ 0)))
  | `(DCC' Comb.cod)     => `(DCC' (,Comb.sig (,Comb 1 ((' Comb.cod) 1)) (∗ 0)))
  | `(DCC' (Snd _ _ _ $B:expr)) => `(DCC' (,Comb.sig (,Comb 1 ((' Snd)) 1) (,_ (,_ _ _) $B)))
  | `(DCC' Comb.type)    => `(DCC' (,Comb.sig (,Comb 1 ((' Comb.type) 1)) (∗ 0)))
  | `(DCC' (Quot $u:expr $A:expr $v:expr $B:expr $x:expr)) => `(DCC (,Comb.sig (,Comb 1 ((' Quot) 1)) (,_ (,(Snd _ _ _ Sort₀) (,Sort₀ $u $A) $x) (,Sort₀ $v $B))))
  | `(DCC' (Id $u:expr $A:expr)) => `(DCC' (,Comb.sig (,Comb 1 ((' Id) 1)) (,Sort₀ $u $A)))

end Dsl

/-
($ Comb.sig (,Comb 1 ((' Quot) 1))) = Σ (Quot (Σ (v : Level) (B : Sort v)) (Σ (Σ (u : Level) (A : u)) (x : A)))
-/
def CombName.sig₁ (c : CombName) : Expr :=
  open Dsl in match c with
  | .sort | .comb_type | .comb_dom | .comb_cod | .comb_u_cod | .comb_u_dom | .comb_sig | .sigma => DCC (𝟙 0)
  | .id => DCC (Σ Sort₀)
  | .quot => DCC (Σ 

@[grind]
def CombName.weight (c : CombName) : ℕ :=
  match c with
  | .id => 5
  | .sort | .comb_type | .comb_dom | .comb_cod | .comb_u_cod | .comb_u_dom | .comb_sig | .sigma => 1

@[grind .]
theorem weight_pos : 0 < CombName.weight e := by
  cases e <;> grind

namespace Expr

@[grind]
def raw_size (e : Expr) : ℕ :=
  open Dsl in match e with
  | DCC' (Σ x) => x.raw_size
  | DCC' (Σ⁻¹ x) => x.raw_size.succ
  | DCC' (Π _a _b _c _d)
  | DCC' (Level.max _f _g _x)
  | DCC' Hole => 1
  | DCC' (∗ x)
  | DCC' (𝟙 x)
  | DCC' (ℕ.succ x) | DCC' (Level.succ x) => x.raw_size.succ
  | DCC' (Sort u) => u.raw_size
  | DCC' Λ => 2
  | DCC' $
  | DCC' ('#(_c))
  | DCC' (: 0 Level)
  | DCC' (: 0 ℕ)
  | DCC' 𝟘
  | DCC' 𝟘₂
  | DCC' 𝟙₂
  | DCC' 𝟚
  | DCC' Level
  | DCC' (? _x)
  | DCC' ℕ => 1
  | DCC' (,B x y) => B.raw_size + x.raw_size + y.raw_size
  | DCC' Comb => 2
  | .app f x => f.raw_size + x.raw_size
  | DCC' _ => 1

@[grind]
def size (e : Expr) : ℕ :=
  open Dsl in match e with
  | DCC' ('#(c)) => c.sig₁.raw_size + c.weight
  | DCC' (Σ x) => x.size
  | DCC' (Σ⁻¹ x) => x.size.succ
  | DCC' (Π _a _b _c _d)
  | DCC' (Level.max _f _g _x)
  | DCC' Hole => 1
  | DCC' (∗ x)
  | DCC' (𝟙 x)
  | DCC' (ℕ.succ x) | DCC' (Level.succ x) => x.size.succ
  | DCC' (Sort u) => u.size
  | DCC' Λ => 2
  | DCC' $
  | DCC' (: 0 Level)
  | DCC' (: 0 ℕ)
  | DCC' 𝟘
  | DCC' 𝟘₂
  | DCC' 𝟙₂
  | DCC' 𝟚
  | DCC' Level
  | DCC' (? _x)
  | DCC' ℕ => 1
  | DCC' (,_B x y) => x.size + y.size
  | DCC' Comb => 2
  | .app f x => f.size + x.size
  | DCC' _ => 1

@[aesop safe forward, aesop safe apply, grind .]
theorem raw_size_pos : 0 < raw_size e := by
  induction e
  any_goals (grind only [raw_size])

@[aesop safe forward, aesop safe apply, grind .]
theorem size_pos : 0 < size e := by
  induction e
  any_goals (grind)
  · simp [size]
    exact .inr weight_pos

class Decreasing (r : Expr → Expr → Type) where
  decreasing : r A B → Expr.size B < Expr.size A

open Decreasing

open Dsl in
inductive ViewApp : Expr → Type
  | app     : ViewApp (DCC ($ f x))
  | curr    : ViewApp (DCC (Λ x y z))
  | sig_inv : ViewApp (DCC (Σ⁻¹ x))

def view_app (e : Expr) : Option (ViewApp e) :=
  open Dsl in match e with
  | DCC ($ _f _x) => .some .app
  | DCC (Λ _x _y _z) => .some .curr
  | DCC (Σ⁻¹ _x) => .some .sig_inv
  | _ => .none

@[aesop safe apply]
def ViewApp.complete (h : ViewApp e) : view_app e = .some h := by
  cases h <;> simp [view_app]

open Dsl in
inductive Red.Head : Expr → Expr → Type
  | sort          : Red.Head (DCC ($ (,B₁ (,B₂ 1 ((' Sort) 1)) (∗ 0)) x)) (DCC (Sort x))
  | id            : Red.Head (DCC ($ (Id u A) x)) x
  | id_u_dom      : Red.Head (DCC ($ Comb.u_dom (Id u A))) u
  | id_u_cod      : Red.Head (DCC ($ Comb.u_cod (Id u A))) u
  | id_dom        : Red.Head (DCC ($ Comb.dom (Id u A))) A
  | id_cod        : Red.Head (DCC ($ Comb.cod (,B₁ (Id u A) __x))) A
  | id_sig        : Red.Head (DCC ($ Comb.sig (,B₁ 1 (' Id)))) (DCC (Σ Sort₀))
  | comb_ty       : Red.Head (DCC ($ Comb.type (,B₁ (,B₂ n f) Γ)))
                     (DCC ((Π Comb.u_dom
                             Comb.dom
                             Comb.u_cod
                             (Λ (Comb.cod)))
                           (,B₁ (,B₂ n f) Γ)))
deriving Repr

@[aesop safe apply]
theorem Red.Head.decreasing (h : Red.Head A B) : size B < size A := by
  induction h
  any_goals (grind)
  · simp [size, CombName.weight, CombName.sig₁]
    ring_nf
    grind

def step_head? (e : Expr) : Option (Σ e', Red.Head e e') :=
  open Dsl in match e with
  | (DCC ($ (,_B₁ (,_B₂ 1 ((' Sort) 1)) (∗ 0)) _x)) => .some ⟨_, .sort⟩
  | (DCC' ($ (Id _u _A) _x)) => .some ⟨_, .id⟩
  | (DCC' ($ Comb.u_dom (Id _u _A))) => .some ⟨_, .id_u_dom⟩
  | (DCC' ($ Comb.u_cod (Id _u _A))) => .some ⟨_, .id_u_cod⟩
  | (DCC' ($ Comb.dom (Id _u _A))) => .some ⟨_, .id_dom⟩
  | (DCC ($ Comb.cod (,_B₁ (Id _u _A) __x))) => .some ⟨_, .id_cod⟩
  | (DCC ($ Comb.sig (,_B₁ 1 (' Id)))) => .some ⟨_, .id_sig⟩
  | (DCC ($ Comb.type (,_B₁ (,_B₂ _n _f) _Γ)))=> .some ⟨_, .comb_ty⟩
  | _ => .none

@[aesop safe apply]
def Red.Head.complete (h : Red.Head A B) : step_head? A = .some ⟨B, h⟩ := by
  cases h <;> simp [step_head?]

instance : Decreasing Red.Head := ⟨Red.Head.decreasing⟩
instance : Deterministic Red.Head := ⟨fun h₁ h₂ => by
  cases h₁.complete.symm.trans h₂.complete
  rfl⟩
instance : ProofEq Red.Head := ⟨fun h₁ h₂ => by
  cases h₁.complete.symm.trans h₂.complete
  rfl⟩

open Dsl in
inductive Red : Expr → Expr → Type
  | sig_inv          : Red (DCC (Σ⁻¹ (Σ B))) B
  | head             : (ViewApp x → False)    → Red.Head (DCC ($ (,B c Γ) x)) e' → Red (DCC ($ (,B c Γ) x)) e'
  | curr             : Red (DCC (Λ f x y)) (DCC ($ f (,(Σ⁻¹ ($ Comb.dom f)) x y)))
  | congr_fun        : Red (DCC ($ f x)) f'   → Red (DCC ($ ($ f x) y)) (DCC ($ f' y))
  | congr_fun'       : Red (DCC (Λ f x y)) f' → Red (DCC ($ (Λ f x y) z)) (DCC ($ f' z))
  | congr_arg        : Red (DCC ($ x y)) x'   → Red (DCC ($ (,B c Γ) ($ x y))) (DCC ($ (,B c Γ) x'))
  | congr_arg'       : Red (DCC (Λ x y z)) x' → Red (DCC ($ (,B c Γ) (Λ x y z))) (DCC ($ (,B c Γ) x'))
deriving Repr

@[aesop safe apply]
theorem Red.decreasing (h : Red A B) : size B < size A := by
  induction h
  any_goals (grind)
  case head h => exact h.decreasing

inductive RedChoiceReflTrans (r : Expr → Expr → Type) [∀ x y, Repr (r x y)] : Expr → Expr → Type
  | refl : RedChoiceReflTrans r A A
  | head : r A B → RedChoiceReflTrans r B C → RedChoiceReflTrans r A C
deriving Repr

def RedChoiceReflTrans.single [∀ x y, Repr (r x y)] (h : r A B) : RedChoiceReflTrans r A B := .head h .refl

def RedChoiceReflTrans.trans [∀ x y, Repr (r x y)] (h₁ : RedChoiceReflTrans r A B) (h₂ : RedChoiceReflTrans r B C) : RedChoiceReflTrans r A C :=
  match h₁ with
  | .refl => h₂
  | .head hr hrt => .head (by assumption) (.trans hrt h₂)

instance [∀ x y, Repr (r x y)] : PushHead (RedChoiceReflTrans r) := ⟨flip RedChoiceReflTrans.trans⟩

def decreasing? {r : Expr → Expr → Type} [∀ x y, Repr (r x y)] [Decreasing r] (hrt : RedChoiceReflTrans r A B) : size B ≤ size A := by
  induction hrt with
  | refl => grind
  | head hr hrt ih =>
    have h := decreasing hr
    grind

instance {r : Expr → Expr → Type} [∀ x y, Repr (r x y)] [ProofEq r] [Decreasing r] [Deterministic r] : ProofEq (RedChoiceReflTrans r) :=
  ⟨fun h₁ h₂ => by
    induction h₁ with
    | refl =>
      cases h₂ with
      | refl => rfl
      | head hr hrt =>
        have h_dec₁ := decreasing hr
        have h_dec₂ := decreasing? hrt
        grind
    | head hr hrt ih =>
      cases h₂ with
      | refl =>
        cases ih hrt
        have h_dec₁ := decreasing hr
        have h_dec₂ := decreasing? hrt
        grind
      | head hr hrt =>
        expose_names
        cases unique hr_1 hr
        cases ih hrt
        cases ih hrt_1
        cases proof_eq hr hr_1
        rfl⟩

@[grind]
def IsNorm (r : Expr → Expr → Type) (A : Expr) := ∀ ⦃B : Expr⦄, r A B → False

def IsNorm.elim (h : IsNorm r A) (hr : r A B) : False := h hr

inductive RedChoiceNormReflTrans (r : Expr → Expr → Type) [∀ x y, Repr (r x y)] : Expr → Expr → Type
  | mk : (hrt : RedChoiceReflTrans r A B) → (hn : IsNorm r B) → RedChoiceNormReflTrans r A B
deriving Repr

def IsNorm.elim_refl (h : IsNorm r A) [∀ x y, Repr (r x y)] (hr : RedChoiceReflTrans r A B) : A = B := by
  induction hr with
  | refl => rfl
  | head hr hrt ih =>
    exact (h.elim hr).elim

def IsNorm.elim_refl_norm (h : IsNorm r A) [∀ x y, Repr (r x y)] (hr : RedChoiceNormReflTrans r A B) : A = B :=
  h.elim_refl hr.1

instance {r : Expr → Expr → Type} [∀ x y, Repr (r x y)] [ProofEq r] [Decreasing r] [Deterministic r] : Deterministic (RedChoiceNormReflTrans r) :=
  ⟨fun ⟨h₁, hn₁⟩ ⟨h₂, hn₂⟩ => by
    expose_names
    induction h₁ generalizing C with
    | refl =>
      cases hn₁.elim_refl_norm x_1
      rfl
    | head hr hrt ih =>
      cases h₂ with
      | refl => cases hn₂.elim (by assumption)
      | head hr₂ hrt₂ =>
        cases unique hr hr₂
        cases proof_eq hr hr₂
        exact ih ⟨hrt, hn₁⟩ ⟨hrt₂, hn₂⟩ hn₁ hrt₂ hn₂⟩

def RedChoiceNormReflTrans.ext
  {r : Expr → Expr → Type}
  [∀ x y, Repr (r x y)]
  [ProofEq r]
  [Decreasing r]
  [Deterministic r]
  (hrt₁ : RedChoiceReflTrans r A B)
  (hrt₂ : RedChoiceReflTrans r A B)
  (hn₁  : IsNorm r B := by assumption)
  (hn₂  : IsNorm r B := by assumption) : (RedChoiceNormReflTrans.mk hrt₁ hn₁) = (RedChoiceNormReflTrans.mk hrt₂ hn₂) := by
  cases unique (RedChoiceNormReflTrans.mk hrt₁ hn₁) (.mk hrt₂ hn₂)
  cases proof_eq hrt₁ hrt₂
  rfl

instance
  {r : Expr → Expr → Type}
  [∀ x y, Repr (r x y)]
  [ProofEq r]
  [Decreasing r]
  [Deterministic r] : ProofEq (RedChoiceNormReflTrans r) := ⟨fun ⟨h₁, hn₁⟩ ⟨h₂, hn₂⟩ => by
    cases RedChoiceNormReflTrans.ext h₁ h₂
    rfl⟩

def RedChoiceNormReflTrans.heq {r : Expr → Expr → Type}
  [∀ x y, Repr (r x y)]
  [ProofEq r]
  [Decreasing r]
  [Deterministic r]
  (heq : B = C) (h₁ : RedChoiceNormReflTrans r A B) (h₂ : RedChoiceNormReflTrans r A C) : h₁ ≍ h₂ := by
  cases heq
  cases proof_eq h₁ h₂
  rfl

def step? (e : Expr) : Option (Σ e', Red e e') :=
  open Dsl in match e with
  | (DCC (Σ⁻¹ (Σ B))) => .some ⟨_, .sig_inv⟩
  | (DCC' (Λ _f _x _y)) => .some ⟨_, .curr⟩
  | (DCC ($ ($ f x) _y)) => do
    .some ⟨_, .congr_fun (← step? (DCC ($ f x))).snd⟩
  | (DCC ($ (Λ f x y) _z)) => do
    .some ⟨_, .congr_fun' (← step? (DCC (Λ f x y))).snd⟩
  | (DCC ($ (,B c Γ) x)) =>
    if heq : x.view_app.isSome then
      match x with
      | (DCC ($ x y)) => do
        .some ⟨_, .congr_arg (← step? (DCC ($ x y))).2⟩
      | (DCC (Λ x y z)) => do
        .some ⟨_, .congr_arg' (← step? (DCC (Λ x y z))).2⟩
      | _ => .none
    else do
      .some ⟨_, .head (fun h => by simp_all [h.complete]) (← step_head? (DCC ($ (,B c Γ) x))).2⟩
  | _ => .none

def Red.complete (h : Red A B) : step? A = .some ⟨B, h⟩ := by
  induction h with
  | head ih h =>
    expose_names
    have heq : view_app x = .none := by
      apply Option.eq_none_iff_forall_ne_some.mpr
      intro h
      exact (ih h).elim
    have heq' := h.complete
    unfold step?
    cases h with
    | _ => simp [heq, heq']
  | _ => simp_all [step?, view_app]; try grind

instance : Decreasing Red := ⟨Red.decreasing⟩
instance : Deterministic Red := ⟨fun h₁ h₂ => by
  cases h₁.complete.symm.trans h₂.complete
  rfl⟩
instance : ProofEq Red := ⟨fun h₁ h₂ => by
  cases h₁.complete.symm.trans h₂.complete
  rfl⟩

def reduce (e : Expr) : Σ' (e' : Expr), RedChoiceNormReflTrans Red e e' :=
  match heq : step? e with
  | .some ⟨e', h⟩ =>
    have _h_dec := h.decreasing
    let ⟨_, hrt, hn⟩ := (reduce e')
    ⟨_, .head h hrt, hn⟩
  | .none => ⟨_, .refl, (fun _ h => by simp_all [h.complete])⟩
termination_by e.size

def RedChoiceNormReflTrans.complete (hrt : RedChoiceNormReflTrans Red A B) : reduce A = ⟨B, hrt.1, hrt.2⟩ :=
  match B, hrt with
  | _, ⟨.refl, hn⟩ => by
    unfold reduce
    split
    · exact (hn (by assumption)).elim
    · rfl
  | _, ⟨.head hr hrt, hn⟩ => by
    have heq := hr.complete
    unfold reduce
    split
    case h_1 heq' =>
      cases heq'.symm.trans heq
      have heq' := (RedChoiceNormReflTrans.mk hrt hn).complete
      simp_all
      apply RedChoiceNormReflTrans.heq
      grind
    · grind

def RedChoiceReflTrans.conf (h₁ : RedChoiceReflTrans Red A B) (h₂ : RedChoiceReflTrans Red A C) : Σ D, RedChoiceReflTrans Red B D × RedChoiceReflTrans Red C D :=
  match h₁ with
  | .refl => ⟨_, h₂, .refl⟩
  | .head hr₁ hrt₁ =>
    match h₂ with
    | .refl => ⟨_, .refl, .head hr₁ hrt₁⟩
    | .head hr₂ hrt₂ =>
      have heq := unique hr₁ hr₂
      RedChoiceReflTrans.conf (heq ▸ hrt₁) hrt₂

open Dsl in
#eval (DCC ($* (Id (: 1 Level) (Sort 0)) (∗ 0)))
open Dsl in
#eval (reduce (DCC ($* (Id (: 1 Level) (Sort 0)) (∗ 0)))).1
open Dsl in
#eval (reduce (DCC ($* (Id (: 1 Level) (Sort 0)) (∗ 0)))).2.1

open Dsl in
#eval (reduce (DCC ($* (Id (: 1 Level) (Sort 0)) ($* (Id (: 1 Level) (Sort 0)) (∗ 0))))).1

end Expr

namespace Dsl

open Expr in
macro_rules
  | `($A:expr →ᵦ $B:expr) => `(RedChoiceNormReflTrans Red (DCC $A) (DCC $B))

end Dsl
