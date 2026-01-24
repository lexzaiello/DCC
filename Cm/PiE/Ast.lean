import Mathlib.Data.Nat.Notation

open Std (Format)
open Std (ToFormat)
open Std.ToFormat (format)

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

Note: since const here is dependent, it can achieve the above (:: both (:: (quote apply) id)) pattern,
which completes the S pattern in SK.

const α β (x : α) (y : β x) : α

Pretty standard.
id α : α → α

Nil itself forms a list.
nil α : List α

f and g in eq receive different values, since eq is checking definitional equality.
Does it make sense to check definitional equality across types?
Do we want this power? Does it add anything? If eq is just doing definitional equality,
the terms should have the same type if they are syntactically equal anyway.

eq α (β : α → Type) (f : ∀ (x : α), β x) (g : ∀ (x : α), β x) (x : α) (y : α) : β x

apply (:: f x) = apply f to x
apply : ∀ (α : Type) (β : α → Type) : ∀ (l : ((∀ (x : α), β x) × α)), l.fst l.snd

cons is never partially applied, so it can be fully inferred with no extra types.
cons {α : Type} {β : Type} : α → β → (α × β)
cons's type arguments are always implicit.


can we avoid an application expr altogether?
No. we should keep it so we can use "apply".

symbols are quite bloat, but they are nice for debugging.

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

× : Type → Type → Type

can apply apply from inside a list?
unclear.

(:: both (:: (quote apply) (:: both (:: (quote f) id))))

if we make products more dependent, perhaps we can fix this.
:: apply (:: f id)
this should induce an application, I think.
otherwise, we don't have a clear way to ugprade from app to cons.
app and cons should converge in some way.

:: {α β} x xs : ((x : ∀ (x : α), β x) × (xs : α)) = x xs

keep in mind, both is more flexible now.

both : ∀ (α : Type) (β : α → Type) (γ : α → Type) (l : (((∀ (x : α), β x) × (∀ (x : α), γ x)) × (x : α))) : (l.fst.fst l.snd × l.fst.snd l.snd)
both (:: (:: f g) l) = (:: (:: apply (:: f l)) (:: apply (:: g l)))

the issue is, both here is creating another product.
application seems to be divorced form both.
Is there a way to emulate the S functionality while keeping apply the way it is?

we'll see.

the combinators are completely inert without apply.

Summary of our types:
id : ∀ (x : α), α → α
both : ∀ (α : Type) (β : α → Type) (γ : α → Type)
  (f : (∀ (x : α), β x)) (g : (∀ (x : α), γ x))
  (l : α), (β l × γ l)
const (α : Type) (β : α → Type) (x : α) (y : β x) : α
nil : Unit
Unit : Type
apply : ∀ (α : Type) (β : α → Type) : ∀ (l : ((∀ (x : α), β x) × α)), l.fst l.snd
π : ∀ (α : Type) (β : Type) (γ : α → Type) (δ : β → Type)
  (f : ∀ (x : α), γ x) (g : ∀ (x : β), δ x)
  (l : α × β), ((γ l.fst) × (δ l.snd))
eq : ∀ (α : Type) (β : α → Type) (f : ∀ (x : α), β x) (g : ∀ (x : α), β x) (x : α) (y : α), β x

Nondependent versions of const and both used to bootstrap parts of the system.
const' : ∀ (α : Type m) (β : Type n), α → β → α
both'  : ∀ (α : Type m) (β : Type n) (γ : Type o) (f : α → β) (g : α → γ), α → (β × γ)
-/

abbrev Level := ℕ

inductive Expr where
  -- for forming "lists"
  | cons   : Expr → Expr → Expr
  | app    : Expr → Expr → Expr
  -- type universe hierarchy
  | ty     : Level → Expr
  -- for forming cons types
  | unit   : Expr
  | prod   : Level → Level → Expr
  | nil    : Expr -- nil : Unit
  -- the core combinators: π, const, apply, id, eq, both
  -- these have explicit universe level arguments
  | apply  : Level → Level → Expr
  | π      : Level → Level → Level → Level → Expr
  | id     : Level → Expr
  | eq     : Level → Level → Expr
  -- dependent and nondependent const.
  | const  : Level → Level → Expr
  | const' : Level → Level → Expr
  -- Dependent and nondependent :: both, respectively
  | both   : Level → Level → Level → Expr
  | both'  : Level → Level → Level → Expr
  -- For bootstrapping types by running infer first. TODO: remove this once combinator types are determined
  | hole   : Expr
deriving BEq, DecidableEq

open Expr

syntax ident ".{" term,* "}" : term
syntax "::[" term,+ "]" : term
syntax (name := atDollar) "@$" term:max term:max term:max term:max term:max term:max : term

macro_rules
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.cons $x ::[$xs,*])

notation "?" => Expr.hole
notation "::" => Expr.cons
notation "f$" => Expr.app
notation "×'" => Expr.prod
notation "Ty" => Expr.ty

abbrev mk_quote (m n : Level) (α β x : Expr) : Expr := ::[::[const' m n, α, β], x]

/-
f$ (apply m n) ::[::[α, β], f, x] induces an application of x to f
apply : ∀ (l : (((α : Type) × (β : α → Type)) × (f : ∀ (x : α), β x) × (x : α))), f$ l.snd x
-/
abbrev mk_apply (m n : Level) (α β e : Expr) : Expr := f$ (f$ (f$ (apply m n) α) β) e

inductive Error where
  | stuck      : Expr → Error
  | no_rule    : Expr → Error
deriving BEq, DecidableEq

open Expr

/-
Foldls cons'd pairs / lists
-/
def Expr.foldl! {α : Type} (f : α → Expr → α) (init : α) : Expr → α
  | :: x xs => xs.foldl! f (f init x)
  | x => f init x

partial def Expr.fmt (e : Expr) : Format :=
  match e with
  | apply m n => "apply.{" ++ [m, n].toString ++ "}"
  | hole => "_"
  | f$ f x => .paren <| "f$ " ++ (.paren f.fmt) ++ .line ++ (.paren x.fmt)
  | eq m n => "eq.{" ++ [m, n].toString ++ "}"
  | π m n o p => "π.{" ++ [m, n, o, p].toString ++ "}"
  | (.cons x xs) =>
    "::[" ++
      (.group
        <| .nest 2
        <| Format.joinSep (xs.foldl! (fun (acc : List Std.Format) e => acc ++ [(Expr.fmt e)]) [x.fmt]) ((format ",") ++ Format.line))
    ++ "]"
  | id m => "id.{" ++ [m].toString ++ "}"
  | const m n => "const.{" ++ [m, n].toString ++ "}"
  | const' m n => "const'.{" ++ [m, n].toString ++ "}"
  | both m n o => "both.{" ++ [m, n, o].toString ++ "}"
  | both' m n o => "both'.{" ++ [m, n, o].toString ++ "}"
  | nil => "nil"
  | prod m n => "×'.{" ++ [m, n].toString ++ "}"
  | unit => "Unit"
  | Ty n => s!"Ty {n}"

def Error.fmt : Error → Format
  | .stuck e   => "got stuck evaluating: " ++ .line ++ e.fmt
  | .no_rule e => "no rule to evaluate: " ++ .line ++ e.fmt

instance Expr.instToFormat : ToFormat Expr where
  format := Expr.fmt

instance Error.instToFormat : ToFormat Error where
  format := Error.fmt

instance Error.isntToString : ToString Error where
  toString := toString ∘ Error.fmt

instance Expr.instToString : ToString Expr where
  toString := toString ∘ Expr.fmt

def unwrap_with {α : Type} (e : Error) (o : Option α) : Except Error α :=
  (o.map Except.ok).getD (.error e)

def Expr.head! : Expr → Expr
  | :: a _b => a
  | e => e

def Expr.tail! : Expr → Expr
  | :: _a b => b
  | e => e
