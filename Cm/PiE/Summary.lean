/-
Summary of our types:
id : ∀ (x : α), α → α
both : ∀ (α : Type) (β : α → Type) (γ : α → Type)
  (f : (∀ (x : α), β x)) (g : (∀ (x : α), γ x))
  (l : α), (β l × γ l)
const α β (x : α) (y : β x) : α
nil.{[m, n]} {α : Type m} : ∀ (x : α), Type n
Unit : Type
apply : ∀ (α : Type) (β : α → Type) : ∀ (l : ((∀ (x : α), β x) × α)), l.fst l.snd
π : ∀ (α : Type) (β : Type) (γ : α → Type) (δ : β → Type)
  (f : ∀ (x : α), γ x) (g : ∀ (x : β), δ x)
  (l : α × β), ((γ l.fst) × (δ l.snd))
eq : ∀ (α : Type) (β : α → Type) (f : ∀ (x : α), β x) (g : ∀ (x : α), β x) (x : α) (y : α), β x

const' : ∀ (α : Type m) (β : Type n), α → β → α
both'  : ∀ (α : Type m) (β : Type n) (γ : Type o) (f : α → β) (g : α → γ), α → (β × γ)

:: : {α : Type} {β : α → Type} (x : α) (xs : β x), ((x : α) × β x)
-/

/-
Notes on pairs now that we have sigma pairs:

It feels like we should be able to remove the const' and both' special case / nondependent
versions of both and const, now that nil {α : Type} : α → Unit

:: (x : α) (nil α) - this "completes" the chain of dependency in the sigma.

can we remove const' altogether?
const' : (α : Type) → (β → Type) (x : α) → (y : β) → α

const : ∀ (α : Type) (β : α → Type) (x : α) (y : β x), α

both' is just both with β = (nil (α : Type m) (Type n)),
and y :
nil.{[m, n]} (α : Type m) (β : Type n) (x : α) = β

downgrading :: (x : α) (xs : ∀ (x : α), β x) to :: (x : α) (xs : β)
:: (x : α) (:: (xs : β) (

Currying with apply:
f$ apply ::[::[f, a], x] = f$ apply ::[f, a, x]
-/
