/-
Summary of our types:
id : ∀ (x : α), α → α
both : ∀ (α : Type) (β : α → Type) (γ : α → Type)
  (f : (∀ (x : α), β x)) (g : (∀ (x : α), γ x))
  (l : α), (β l × γ l)
const α β (x : α) (y : β x) : α
nil : Unit
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
More notes on pairs.
It seems like it might be nice to upgrade our pairs to dependent pairs / sigmas.

we could express apply more succinctly, then.

f$ (f$ apply ::[α, β]) ::[f, x]
f$ (f$ (f$ apply α) β) ::[f, x]

:: {α : Type} {β : α → Type} [(x : α), (xs : β x)] : ((x : α) × (β x))

f$ apply ::[::[α, β], ::[f, x]]

the ::[α, β] looks a lot like a sigma type.

((α : Ty m) × (α → Ty n))

this seems like potentially a worthwhile upgrade, but it could make type inference harder?
easier?

we'll see. This doesn't really require any changes, except in eval.
we just need to change the eval rule for apply.

I like this approach way more, ngl.


-/
