import Mathlib.Data.Nat.Notation
import Cm.Questions.Ast

open Expr

/-
::[x, xs] π = π xs x
::[(x : α), (xs : β)] : ∀ {γ : β → α → Type} (π : ∀ (xs : β) (x : α), γ xs x), γ xs x

So we need some notation to represent ∀ {γ : β → α → Type} (π : ∀ (xs : β) (x : α), γ xs x), γ xs x

Call this Σ β xs α x.

Σ β xs α x (π : γ) = γ xs x

Σ is just notation for the type of ::[x, xs]

Notably, Σ seems to coincide with our idea of ::[Δ, Γ]

So it feels like the rule for application is:

((f : t) (x : α))

Σ denotes a very dependent type?

Σ x T denotes (x : T x)

::[(x : α), (xs : β)]

(x : nil α) this is a normal type assertion?

wait holy moly.

Σ Ty : nil Ty

α → α

Function application rule?
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
  | fst    : IsStep ($ fst, _α, _β, fn, ::[x, f]) ($ fn, x)
  | snd    : IsStep ($ snd, _α, _β, fn, ::[x, f]) ($ fn, f, x)
  | nil    : IsStep ($ nil, α, x) α
  | id     : IsStep ($ Expr.id, _α, x) x
  | const' : IsStep ($ const', _α, _β, x, y) x
  | sigma  : IsStep ($ Σ', β, xs, α, x, γ) ($ γ, xs, x)
  | left   : IsStep f f'
    → IsStep ($ f, x) ($ f', x)
  | right  : IsStep x x'
    → IsStep ($ f, x) ($ f, x')

inductive valid_judgment : Expr → Expr → Prop
  /- TODO: Remove this in the actual calculus
     this module is just for answering reseach questions -/
  | ty    : valid_judgment Ty Ty
  | sigma : valid_judgment x α → valid_judgment xs β
    → valid_judgment ::[x, xs] ($ Σ', β, xs, α, x)
