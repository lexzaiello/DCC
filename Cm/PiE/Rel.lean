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

const (α : Type m) (β : α → Type n) (x : α) (y : β x) : α
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

TODO: need to fill in type arguments to applies created inside step relation.
-/

inductive is_step_once : Expr → Expr → Prop
  | app_id       : is_step_once (f$ (f$ (f$ (apply m n) _fα) _fβ) ::[::[.id o, _α], x]) x
  | app_const    : is_step_once (f$ (f$ (f$ (apply m n) _fα) _fβ) ::[::[::[(const o p), _α, _β], c], _x]) c
  | app_const'   : is_step_once (f$ (f$ (f$ (apply m n) _fα) _fβ) ::[::[::[(const' o p), _α, _β], c], _x]) c
  | app_both     : is_step_once (f$ (f$ (f$ (apply m n) _fα) _fβ) ::[::[::[(both o p q), α, β, γ], ::[f, g]], x])
    ::[f$ (f$ (f$ (apply o p) α) β)  ::[f, x], f$ (f$ (f$ (apply o q) α) γ) ::[g, x]]
  | app_π_both   : is_step_once (f$ (f$ (f$ (apply m n) _fα) _fβ) ::[::[::[π o p q r, α, β, γ, δ], ::[fx, fxs]], ::[x, xs]])
    ::[f$ (f$ (f$ (apply o q) α) γ) ::[fx, x], f$ (f$ (f$ (apply p r) β) δ) ::[fxs, xs]]
  | app_eq_yes   : a == b → is_step_once
    (f$ (f$ (f$ (apply m n) _fα) _fβ) ::[::[::[::[eq o p, α, β], fn_yes, fn_no], a], b])
    (f$ (f$ (f$ (apply o p) α) β) ::[fn_yes, a])
  | app_eq_no    : a ≠ b  → is_step_once
    (f$ (f$ (f$ (apply m n) _fα) _fβ) ::[::[::[::[eq o p, α, β], fn_yes, fn_no], a], b])
    (f$ (f$ (f$ (apply o p) α) β) ::[fn_no, b])

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

id with types filled in
id m : :: both (:: (:: (const' m.succ.succ m.succ.succ) (Ty m.succ) (Ty m.succ) (Ty m)) (:: both (:: const const)))

id m : :: both (:: (:: const (Ty m)) (:: both (:: const const)))
const m n : :: both (:: (:: const (Ty m)) (::

β : α → Type
β = :: both (:: const α :: const Ty n)
point-free, with α in scope:
β = :: both (:: (quote both) (:: both (:: const (:: const (Ty n)))))

const m n : :: both (::
  (:: const (Ty m))
  (:: both (::
    (:: both (:: (quote both) (:: both (:: const (:: const (Ty n))))))
    (:: both (::
      (:: both (:: (:: const const) const)) -- x : α will later accept β and have to discard it
-/

inductive valid_judgment : Expr → Expr → Prop
  | cons : valid_judgment x α
    → valid_judgment xs β
    → valid_judgment ::[x, xs] (::[prod, α, β])
  | unit : valid_judgment unit (Ty 0)
  | nil  : valid_judgment nil unit
  | id   : valid_judgment 
