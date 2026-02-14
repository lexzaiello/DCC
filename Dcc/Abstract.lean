/-
Representations of our core inference rules in Lean, with some proofs about them.
-/

/-
Cons / sigma / composition:
(:: f g) x = (:: f(x), g(f(x)))

This is a core data structure in the paper.
fst / snd correspond to left and right sigma elimination.

fst (:: f g) x = fst (:: f(x), g(f(x))) = f(x)
snd (:: f g) x = snd (:: f(x), g(f(x))) = g(x)

Curry has a concept of Ξ / restricted generality
in illative combinatory logic with the inference rule:

Δ ⊢ ΞXY      Δ ⊢ XU
-------------------
       Δ ⊢ YU

Note that this specific rule is designed to prevent Curry's paradox.
-/
def Ξ.elim {α : Type} {P : α → Prop} {Q : α → Prop}
  (Ξ : ∀ (x : α), P x → Q x)
  (X : ∀ (x : α), P x) (U : α) : Q U := by
  exact Ξ _ (X U)

/-
P1) ΞXY requires that P(U) implies Q(U)
P2) XU is a proof of P(U)
The conclusion YU is a proof of Q(U) derived from P1, P2
-/

/-
In our calculus, we have a somewhat similar notion of sigma composition
and left / right elimination / projection.

(:: f g) x = (:: f(x), g(f(x)))
fst (:: f g) x = fst (:: f(x), g(f(x))) = f(x)
snd (:: f g) x = snd (:: f(x), g(f(x))) = g(x)

Here are the elimination rules written out:
-/

/-
(:: f g) x = (:: f(x), g(f(x)))
-/
def Cons.elim_right {α : Type} {P : α → Prop} {Q : ∀ {x : α}, P x → Prop}
  (f : ∀ (x : α), P x) (g : ∀ {x : α}, Q (f x)) (x : α) : Q (f x) := by
  apply g

def Cons.elim_left {α : Type} {P : α → Prop} {Q : ∀ {x : α}, P x → Prop}
  (f : ∀ (x : α), P x) (_g : ∀ {x : α}, Q (f x)) (x : α) : P x := by
  apply f

/-
A proof that Ξ implies elim_right and elim_left.
-/
theorem Xi_imp_cons_elim {α : Type} {P : α → Prop} {Q₁ : α → Prop}
  (Ξ : ∀ (x : α), P x → Q₁ x)
  (X : ∀ (x : α), P x) : ∃ (Q : ∀ {x : α}, P x → Prop) (_g : ∀ {x : α}, Q (X x)),
  ∀ (x : α), Q (X x) ∧ P x := ⟨fun {x} _hp => Q₁ x
    , fun {x} => Ξ _ (X x)
    , fun x => ⟨Ξ _ (X x), X _⟩⟩

/-
A proof that elim_right and elim_left implies Ξ.

Note that the Ξ hypothesis is not required. It is subsumed by the types of
P, Q, f, and g.

This vaguely suggests that our rules are more powerful.
-/
theorem cons_elim_imp_Xi {α : Type} {P : α → Prop} {Q : ∀ {x : α}, P x → Prop}
  (f : ∀ (x : α), P x) (g : ∀ {x : α}, Q (f x)) : ∃ (Q₁ : α → Prop) (_Ξ : ∀ (x : α), P x → Q₁ x),
  ∀ (x : α), Q₁ x := ⟨fun x => Q (f x), fun _X _hp => g, fun _X => g⟩

theorem Xi_iff_cons {α : Type} {P : α → Prop} (X : ∀ (x : α), P x) :
  (∃ (Q₁ : α → Prop), ∀ (x : α), P x → Q₁ x) ↔
  (∃ (Q : ∀ {x : α}, P x → Prop) (_g : ∀ {x : α}, Q (X x)), ∀ (x : α), Q (X x) ∧ P x) := by
  constructor
  intro ⟨Q₁, Ξ⟩
  exact ⟨fun {X} hp => Q₁ X, fun {x} => Ξ _ (X x), fun x => ⟨Ξ _ (X x), X x⟩⟩
  intro ⟨Q, g, helim⟩
  exact ⟨fun x => Q (X x), fun x hp => g⟩

