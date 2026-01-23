/-
π does list projection and the type of elements in its list must be fixed,
so π is only polymorphic.

π α β     (f : α → β) (g : (List α) → (List β))             : List α → List β

similarly, both is only polymorphic since it needs to form a new list as well.
HOWEVER, it does not pattern match on the list, so f and g receive the same
term, so it is actually dependent.
Note, however, that it does not apply the terms to each other as in the SK combiantor
calculus. The common pattern to do this is both (quote apply) id where quote = (:: const ·).
both (quote apply) id x = (:: apply (id x))

both α (β : α → Type) (f : ∀ (x : α), β x) (g : ∀ (x : α), List (β x)) (x : α), (List (β x))

-- TODO: list.cons

Note: since const here is dependent, it can achieve the above (:: both (:: (quote apply) id)) pattern,
which completes the S pattern in SK.

const α β (x : α) (y : β x) : α

Pretty standard.
id α : α → α

Nil itself forms a list.
nil α : List α

f and g in eq receive different values, since eq is checking definitional equality.
TODO: is this level of dependency allowed? Note that x and y must have the same type.
Does it make sense to check definitional equality across types?
Do we want this power? Does it add anything? If eq is just doing definitional equality,
the terms should have the same type if they are syntactically equal anyway.

eq α (β : α → Type) (f : ∀ (x : α), β x) (g : ∀ (x : α), β x) (x : α) (y : α) : β x

apply (:: f x) = apply f to x
apply : ∀ (α : Type) (β : α → Type) : ∀ (l : ((∀ (x : α), β x) × α)), l.fst l.snd

cons is never partially applied, so it can be fully inferred with no extra types.
cons {α : Type} : α → (List α) → (List α)

What about type universe hierarchy?
Pretty standard.
Type.n : Type n.succ
Prop : Type 0

can we avoid app altogether and just use lists?

probably not.
apply is what we use to apply a list, I think.

The question is, do we want to use Lists, or something "more" polymorphic?
Instead of List α, we could use tuples.

nil : Unit
:: (a : α) nil : (α × Unit)
-/

inductive Expr where
  | nil  : Expr → Expr
  | cons : Expr → Expr → Expr
  | app  : Expr → Expr → Expr
