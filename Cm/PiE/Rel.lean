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
    ::[f$ (f$ (f$ (apply o p) α) β) ::[f, x], f$ (f$ (f$ (apply o q) α) γ) ::[g, x]]
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

id : (:: both (:: (:: const (Ty m)) (:: both (:: (quote both) (:: both (:: const const))))))
id α = :: (Ty m) (:: (const α) (const α))

can also redo id instead like this:
id α   : quote (:: α α)
id α x : :: α α

head is the right type.

Also, thing to remember. We assume our arguments are like ::[::[id o, α], x]
id = :: both (:: (quote (Ty m)) (:: both (:: (quote const) (:: both (:: id id)))))
after applying α, output type is
:: (const' (×' m.succ m.succ (Ty m) (Ty m)) α) (:: α α)

outermost both, α = (Ty m), β, γ = (::[const' m.succ.succ m.succ, Ty m.succ, Ty m, Ty m]), n, o = m.succ
or actually β, γ = :: [id m.succ, Ty m]
l = α, (β l × γ l) = α × α. does this reflect the const part? this is also wrong. it's not a list of α,
it's a list of Ty m containing α.
((const' (Ty m.succ) (Ty m) (Ty m)) α = (Ty m)
(Ty m) × (Ty m),

but what about the quote oth?

this is the type of the (:: both (:: const const)), (:: α α), (Ty m) × (Ty m)

(quote const) = :: const const
this receives α : Ty m, but the output type should be sorry for now since we haven't settled the type of const
although, the inner const being returned should have its type arguments filled in.
Then, it receives x : α, so α needs to be copied in again, which is unfortunate.
we could probably remove one of the quotes then.

id = :: both (:: (quote (Ty m)) (:: both (:: (quote const) (:: both (:: id id)))))
:: both (:: (quote (Ty m)) (:: both (:: (quote const) (:: both (:: id id)))))

(quote const) = :: ::[(const' m.succ m), type_of_the_inner_thing]
See here, β gets filled in with α. perfect.
the nesting might be wrong though we'll see.


-/

/-
TODO: fill these in later.
-/
def USorry : Level := 0
def TSorry : Expr:= .nil

namespace prod

/-
((α : (Type m)) × (β : (Type n))) : (Type (max (m n))).succ
-/
def type_expanded (m n : Level) : Expr :=
  Ty (max m n).succ

end prod

namespace id

/-
id : ∀ (α : Type), α → α
-/
def type' (m : Level) : Expr :=
  -- this is the resulting :: α α. Of type (Ty m) × (Ty m)
  -- we have to wrap this in a const as well though.
  let inner_both_α_α_t := ::[const' m.succ.succ m.succ
                          , Ty m.succ
                          , Ty m
                          , Ty m]
  -- :: both (:: id id) α = :: α α
  let inner_α_α := ::[
    ::[both m.succ m.succ m.succ
      , Ty m
      , inner_both_α_α_t
      , inner_both_α_α_t]
    , ::[id m.succ, Ty m]
    , ::[id m.succ, Ty m]]
  -- wraps the :: α α list in a const so (x : α) gets rejected
  -- α gets inserted as the β type argument to const
  -- and α is set to the :: α α list type ((Ty m) × (Ty m))
  let t_inner_α_α := ::[prod m m, Ty m, Ty m]
  let const_wrapper_α_α := ::[(const' m.succ m), t_inner_α_α]

  -- const ((Ty m) × (Ty m)) α : ((Ty m) × (Ty m)) → α → ((Ty m) × (Ty m))
  -- α needs to be copied into here, too.
  -- :: both (:: (quote (quote ((Ty m) × (Ty m)))) (:: both (:: (id (Ty m)) (:: (quote (quote ((Ty m) × (Ty m))))))))
  let t_t_inner_α_α := Ty m.succ
  let t_typed_const_wrapper := ::[(

  /- inner_ish α = (const' ((Ty m) × (Ty m)) α) (:: α α)
    = :: both (:: (const' t_inner_α_α) inner_α_α)
    α = (Ty m)
    β : α → Type, β α = t_typed_const_wrapper, β has α in scope anyway, so we just need to wrapped the (Ty × stuff around
  -/
  let inner_ish_both

  ::[::[both m.succ m.succ m.succ, Ty m, TSorry, TSorry]

/-
id : ∀ (α : Type), α → α
-/
def type (m : Level) : Expr :=
  ::[::[(both m.succ USorry USorry), (Ty m), TSorry, TSorry]
  , ::[::[(const' m.succ.succ m.succ.succ), (Ty m.succ), (Ty m.succ)], (Ty m)]
  , ::[(both USorry USorry USorry), TSorry, TSorry, TSorry]
  , ::[::[(const' USorry USorry), TSorry, TSorry], ::[(both USorry USorry USorry), TSorry, TSorry, TSorry]]
  , ::[(both USorry USorry USorry), TSorry, TSorry, TSorry]
  , ::[(const' USorry USorry), TSorry, TSorry]
  , ::[(const' USorry USorry), TSorry, TSorry]]

end id

/-
both : ∀ (α : Type) (β : α → Type) (γ : α → Type)
  (f : (∀ (x : α), β x)) (g : (∀ (x : α), γ x))
  (l : α), (β l × γ l)
both : (:: both (:: (quote Ty m)
  (:: both (:: (
-/
namespace both

def type (m n o : Level) : Expr :=
  

end both

inductive valid_judgment : Expr → Expr → Prop
  | cons : valid_judgment x α
    → valid_judgment xs β
    → valid_judgment ::[x, xs] (::[prod, α, β])
  | unit : valid_judgment unit (Ty 0)
  | nil  : valid_judgment nil unit
  | id   : valid_judgment (Expr.id m) <| id.type m
  
