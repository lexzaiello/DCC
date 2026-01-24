import Cm.PiE.Ast

open Expr

/-
Question on currying:
- I want to make the arguments for the base combinators fully uncurried.

Summary of our types:
id : ∀ (x : α), α → α
both : ∀ (α : Type) (β : α → Type) (γ : α → Type)
  (f : (∀ (x : α), β x)) (g : (∀ (x : α), γ x))
  (l : α), (β l × γ l)
both (:: (:: f g) l) = (:: (:: apply (:: f l)) (:: apply (:: g l)))

const α β (x : α) (y : β x) : α
id α : α → α

nil : Unit
apply : ∀ (α : Type) (β : α → Type) : ∀ (l : ((∀ (x : α), β x) × α)), l.fst l.snd
π : ∀ (α : Type) (β : Type) (γ : α → Type) (δ : β → Type)
  (f : ∀ (x : α), γ x) (g : ∀ (x : β), δ x)
  (l : α × β), ((γ l.fst) × (δ l.snd))

eq : ∀ (α : Type) (β : α → Type) (f : ∀ (x : α), β x) (g : ∀ (x : α), β x) (x : α) (y : α), β x

apply has 2 explicit type arguments, α β
id has one explicit type argument, α
both has 3 explicit type arguments, α β γ
π has 4 explicit type arguments, α β γ δ
const has 2 explicit type arguments, α β

TODO: need to decide where to curry these.
I want to follow the old style, ideally, but I'm not sure how that will play with apply.

Need to also decide where to nil delimit these, if applicable.

Note that all of these types are universe polymoprhic.
-/

inductive is_step_once : Expr → Expr → Prop
  | app_id       : is_step_once (f$ apply ::[::[id, _α], x]) x
  | app_const    : is_step_once (f$ apply ::[::[::[const, _α, _β], c], _x]) c
  | app_both     : is_step_once (f$ apply ::[::[::[both, _α, _β, _γ], ::[f, g]], x])
    ::[f$ apply ::[f, x], f$ apply ::[g, x]]
  | app_π_both   : is_step_once (f$ apply ::[::[::[π, _α, _β, _γ, _δ], ::[fx, fxs]], ::[x, xs]])
    ::[f$ apply ::[fx, x], f$ apply ::[fxs, xs]]
  | app_eq_yes   : a == b → is_step_once (f$ apply ::[::[::[::[eq, _α, _β], fn_yes, fn_no], a], b])
    (f$ apply ::[fn_yes, a])
  | app_eq_no    : a ≠ b  → is_step_once (f$ apply ::[::[::[::[eq, _α, _β], fn_yes, fn_no], a], b])
    (f$ apply ::[fn_no, b])

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

we start our derivation of the point-free types with the function application rule.
f$ apply ::[f, x] gets type-checked by applying x to the type of f,
then comparing the head of the resultant list with the known type of x.

For example, with id:
(f$ apply ::[::[id, _α], x]) ↦ x
id α : [Type, rest stuff]
id α x : [(:: const α), (:: const α)]

id.{ : ::[(:: const (Ty 
-/

inductive valid_judgment : Expr → Expr → Prop
  | cons : valid_judgment x α
    → valid_judgment xs β
    → valid_judgment ::[x, xs] (::[prod, α, β])
  | unit : valid_judgment unit (Ty 0)
  | nil  : valid_judgment nil unit
  | id   : valid_judgment 
