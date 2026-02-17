import Mathlib

/-
Representations of our core inference rules in Lean, with some proofs about them.
-/

/-
Cons / sigma / composition:
(:: f g) x = (:: f(x), g(x)(f(x)))

This is a core data structure in the paper.
fst / snd correspond to left and right sigma elimination.

fst ((:: f g) x) = fst (:: f(x), g(x)) = f(x)
snd ((:: f g) x) = snd (:: f(x), g(x)) = g(x)

Note that snd also corresponds to the S combinator and cut elimination.

Curry has a concept of Ξ / restricted generality
in illative combinatory logic with the inference rule:

Δ ⊢ ΞXY      Δ ⊢ XU
-------------------
       Δ ⊢ YU
-/

/-
(:: f g) is not necessarily a "substitutable" sigma.

In our calculus, we use judgments as a primitive data-structure.

(∶ T x) represents a typing judgment as data.
(:: (∶ Tf f) (∶ Tg g)) is a sigma / cons expression, full written out.

As demonstrated below, substitution is only defined on sigma when
Tf and Tg as themselves functions.

Otherwise, the sigma may still be a dependent pair, but a term "x"
cannot be substituted into it.
-/

--                                      ↓                ↓ - (:: f(x) g(x))
@[ext]
structure Ξ.{m, n, o} {α : Sort m} (P : α → Sort n) (Q : α → Sort o) where
  X    : ∀ (x : α), P x -- X U
  himp : ∀ (x : α), P x → Q x
  -- ^ Note: restricted generality supposes this as an axiom to introduce Ξ
  -- we don't have a witness of g as below. this is what makes ours more "constructive"

def Ξ.elim'.{m, n, o} {α : Sort m} {P : α → Sort n} {Q : α → Sort o}
  (c : Ξ.{m, n, o} P Q) (x : α) : Q x := c.himp x (c.X x)

@[ext]
structure Cons.{m, n} (P : Sort m) (Q : P → Sort n) where
  f : P
  g : Q f

def Cons.curry.{m, n, o} {α : Sort m} {P : α → Sort n} {Q : ∀ (x : α), P x → Sort o}
  (c : Cons (∀ (x : α), P x) (fun f => ∀ (x : α), Q x (f x)))
  (x : α) : Cons (P x) (Q x) := ⟨c.f x, c.g x⟩ -- (:: f(x) g(x))

def Cons.fst : Cons P Q → P := Cons.f
def Cons.snd : ∀ (c : Cons P Q), Q c.f := Cons.g

def Ξ.of_cons.{m, n} {α : Sort m} {P : α → Sort n} {Q : ∀ (x : α), P x → Sort o}
  (C : Cons (∀ (x : α), P x) (fun f => ∀ (x : α), Q x (f x))) : (Ξ P (fun x => Q x (C.f x))) :=
  ⟨C.f, fun x _ => C.g x⟩

def Cons.of_Ξ.{m, n} {α : Sort m} {P : α → Sort n} {Q : α → Sort o}
  (Ξ : Ξ P Q) : Cons (∀ (x : α), P x) (fun _f => ∀ (x : α), Q x) :=
    ⟨Ξ.X, fun x => Ξ.himp x (Ξ.X x)⟩

/-
We want a proof that Ξ is not constructive, while cons is.

This might not be particularly useful if we don't model Ξ exactly as curry does.
-/

def Ξ_iff_Cons.toFun.{m, n, o} (α : Sort m) (P : α → Sort n) (Q : α → Sort o) (Ξ : Ξ P Q) :
  Cons (∀ (x : α), P x) (fun _f => ∀ (x : α), Q x) :=
  ⟨fun x => Ξ.X x, fun x => Ξ.himp x (Ξ.X x)⟩

def Ξ_iff_Cons.invFun.{m, n, o} (α : Sort m) (P : α → Sort n) (Q : α → Sort o)
  (C : Cons (∀ (x : α), P x) (fun _f => ∀ (x : α), Q x)) : Ξ P Q :=
  ⟨fun x => C.f x, fun x _y => C.g x⟩

def Ξ_iff_Cons.right_inv (α : Sort m) (P : α → Sort n) (Q : α → Sort o) :
  Function.RightInverse (Ξ_iff_Cons.invFun α P Q) (Ξ_iff_Cons.toFun α P Q) :=
  by intro; first | rfl

/-
When α is a Type, we cannot produce a witness of g, since himp
is nonconstructive.

For example, Q may be "Nonempty α". In this case, conversion back and forth
is lossy, since our witness (x : α) is not carried back and forth.

P, for example, might be Inhabited α. Inhabited α implies Nonempty α,
but not the other way around.
-/
def Ξ.iff_Cons.no_left_inv.{m} : ¬ (∀ (α : Type (m + 1)) (P : α → Sort (max 1 (m + 2))) (Q : α → Prop),
  Function.LeftInverse (Ξ_iff_Cons.invFun α P Q) (Ξ_iff_Cons.toFun α P Q)) := by
  simp

  let P := fun (_ : Type m) => Inhabited (Type m)
  let Q := fun (_ : Type m) => Nonempty (Type m)

  let Xi : Ξ P Q := ⟨fun _ => Inhabited.mk (Sort m), fun x y => Nonempty.intro default⟩

  refine ⟨Type m, P, Q, ?_⟩
  simp [Function.LeftInverse]
  refine ⟨Xi, ?_⟩

  intro h_xi_eq
  let h_c_eq := Ξ_iff_Cons.right_inv (Type m) P Q (Ξ_iff_Cons.toFun _ _ _ Xi)

  unfold Ξ_iff_Cons.toFun at *
  unfold Ξ_iff_Cons.invFun at *

  

  sorry

def Ξ_iff_Cons.{m, n, o} (α : Sort m) (P : α → Sort n) (Q : α → Sort o) :
  (Ξ P Q) ≃ (Cons (∀ (x : α), P x) (fun f => ∀ (x : α), Q x)) where
  toFun Ξ := ⟨fun x => Ξ.X x, fun x => Ξ.himp x (Ξ.X x)⟩
  invFun C := ⟨fun x => C.f x, fun x y => C.g x⟩
  left_inv Ξ := by
    cases Ξ
    simp
    funext
    sorry
    /-
      NOTE: lean fails to derive left_inv because we don't have a witness to Y
      in Curry's Ξ, like in Cons. In Cons, g is the witness. This is what makes ours
      more constructive.
    -/

