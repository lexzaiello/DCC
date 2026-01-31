import Mathlib.Data.Nat.Notation
import Cm.Questions.Ast

open Expr

/-
::[x, xs] π = π xs x
::[(x : α), (xs : β)] : ∀ {γ : β → α → Type} (π : ∀ (xs : β) (x : α), γ xs x), γ xs x

So we need some notation to represent ∀ {γ : β → α → Type} (π : ∀ (xs : β) (x : α), γ xs x), γ xs x

Call this Σ β xs α x.

Σ β xs α x (π : γ) = γ xs x
Σ β xs α x = ∀ {γ : β → α → Type} (π : ∀ (xs : β) (x : α), γ xs x), γ xs x

We want Σ to behave exactly as ::, but for types, so that we can use it for contexts.
And, we want to use fst read.
We want to grow the context.

As we said before, we probably don't need the types as well as the arguments in the Δ register.

Σ[::[t_in, t_out], Δ] arg =
  Σ t_out, ::[(::[arg, Δ] t_in), Δ]

::[arg, Δ] t_in
id t_in = id

id ::[Ty, nil] α

so we could change the first assert.

::[Ty, nil] α

id ::[Ty, nil] α

::[Ty, nil] α
= α nil Ty

we really just need a nil delimeter.

But we always need Δ to be a list.

Using this new definition, we can start writing types for things.

What about id?
We can just set Δ₀ = nil.
That's fine.

t_in assumes we have ::[

Note: we can sequence things nicely ::[x, f] id = f x

α argument assumes we have ::[α, Ty] in scope.
and, obviously, ::[α, Ty] t_in = t_in Ty α
t_in = nil

So we might want to flip the order.

So when we type-check, we just want to look at the head of the Δ register?

id : Σ[::[id, t_out], Ty] α
  = Σ[t_out, ::[(::[α, Ty] id), Ty]]
  = Σ[t_out, ::[α, Ty]]

id : Σ[::[id, ::[nil, id]], Ty]

what if we apply fst to Ty?
That won't do anything.

We could change the sigma evaluation rule.
Make it nil delimeted.

we could do something like Δ = ::[arg₁, nil]
Δ' = ::[::[arg₂, arg₁], nil]

Ok, what about const's type?

our sigma rule feels too restrictive.
We need a nil case, as well for the asserts.
-/

inductive IsStepStar {rel : Expr → Expr → Prop} : Expr → Expr → Prop
  | refl  : IsStepStar e e
  | trans : rel e₁ e₂
    → IsStepStar e₂ e₃
    → IsStepStar e₁ e₃

inductive IsBetaEq {s : Expr → Expr → Prop} : Expr → Expr → Prop where
  | rel   : s e₁ e₂ → IsBetaEq e₁ e₂
  | refl  : IsBetaEq e e
  | symm  : IsBetaEq e₁ e₂ → IsBetaEq e₂ e₁
  | trans : IsBetaEq e₁ e₂ → IsBetaEq e₂ e₃ → IsBetaEq e₁ e₃

inductive IsStep : Expr → Expr → Prop
  | sapp   : IsStep ($ ::[x, f], fn) ($ fn, f, x)
  | nil    : IsStep ($ nil, α, x) α
  | id     : IsStep ($ Expr.id, _α, x) x
  | const' : IsStep ($ const', _α, _β, x, y) x
  | left   : IsStep f f'
    → IsStep ($ f, x) ($ f', x)
  | right  : IsStep x x'
    → IsStep ($ f, x) ($ f, x')

inductive IsStepN : ℕ → Expr → Expr → Prop
  | one  : IsStep e e' → IsStepN 1 e e'
  | succ : IsStep e e'' → IsStepN n e'' e'''
    → IsStepN n.succ e e'''

inductive valid_judgment : Expr → Expr → Prop
  /- TODO: Remove this in the actual calculus
     this module is just for answering reseach questions -/
  | ty    : valid_judgment Ty Ty
  | sigma : valid_judgment Σ[Γ, Δ] Ty
  | id    : valid_judgment id Σ[::[id, nil, id, nil], ::[Ty, nil]]
  | app'  : valid_judgment f Σ[::[t_out, nil], ::[α, Δs]]
    → valid_judgment x α
    → valid_judgment ($ f, x) t_out
  | app   : valid_judgment f Σ[::[t_in, ::[x, xs]], ::[α, Δs]]
    → valid_judgment x α
    → IsStep ($ ::[arg, Δ], t_in) t'
    → valid_judgment ($ f, x) Σ[::[x, xs], ::[::[t', Δ], nil]]

theorem id_α_well_typed : valid_judgment α Ty → valid_judgment ($ id, α) Σ[::[nil, id, nil],
  ::[::[($ ::[α, Ty], id), Ty], nil]] := by
  intro h_t
  apply valid_judgment.app
  apply valid_judgment.id
  exact h_t
  apply IsStep.sigma

example : valid_judgment α Ty → valid_judgment x α → valid_judgment ($ id, α, x) α := by
  intro h_t h_t_x
  apply valid_judgment.app
  exact (@id_α_well_typed α h_t)
  
  sorry

