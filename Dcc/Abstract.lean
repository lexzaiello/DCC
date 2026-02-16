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
structure Ξ.{m, n, o} {α : Sort m} (P : α → Sort n) (Q : α → Sort o) where
  X    : ∀ (x : α), P x -- X U
  himp : ∀ (x : α), P x → Q x
  -- ^ Note: restricted generality supposes this as an axiom to introduce Ξ
  -- we don't have a witness of g as below. this is what makes ours more "constructive"

def Ξ.elim'.{m, n, o} {α : Sort m} {P : α → Sort n} {Q : α → Sort o}
  (c : Ξ.{m, n, o} P Q) (x : α) : Q x := c.himp x (c.X x)

structure Cons.{m, n} (P : Sort m) (Q : P → Sort n) where
  f : P
  g : Q f

def Cons.curry.{m, n, o} {α : Sort m} {P : α → Sort n} {Q : ∀ (x : α), P x → Sort o}
  (c : Cons (∀ (x : α), P x) (fun f => ∀ (x : α), Q x (f x)))
  (x : α) : Cons (P x) (Q x) := ⟨c.f x, c.g x⟩ -- (:: f(x) g(x))

def Cons.fst : Cons P Q → P := Cons.f
def Cons.snd : ∀ (c : Cons P Q), Q c.f := Cons.g

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

