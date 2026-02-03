import Mathlib.Data.Nat.Notation

/-
We have seen in multiple places that it's advantageous to have some notion of a type assertion.

(Σ t x) : Prop - this is the assertion that (x : t). It can ONLY be introduced by the kernel.

Σ t x is kind of the inverse of Pi.

(Σ t x) : Prop, only produced by the kernel.

Σ t x terms are what get thrown inside the arguments context.

We want to minimize the number of special cases.

Core ingredients:
- comp, but with explicit type arguments

- Pi should denote a single argument application, not a random number.

Σ t x only get applied after the kernel checks the argument.

Σ t x doesn't make sense without both arguments. However, we ought not special case it.

It might make sense to use cons, in general, for pairs, and have different combinators that interpret
them in different ways.

This is a common pattern.

Pi l : Type

Σ ::[T, x] : Prop. Then, our context is just a bunch of nested pairs of Prop.

Since Σ is only created by the kernel, we don't need to feed it explicit types.
And, we can just type it as Prop, which is really nice.

One thing to note: I would prefer if Pi was really well-typed.

Also note: the user can(?) make Σ expressions themselves, granted they are
one of the built-in ones.
These coincide, pretty much, with the judgment rules. Can have an entire case for this.

Do we need sigma application?
At the very least, we need some mechanism to project out of a sigma pair.
Sigma pairs should be inert.

So, sigma application is just a syntactic thing.

sapp : Prop → Prop → Prop

All ingredients:
- Prop
- Ty n
- Expr.app
- cons, for composition
- pair, for just normal pairs
- Σ
- Π
- Pair
- $Σ
- projection, fst, and snd, with explicit type arguments.

What is the type of a Pair?
pairs shouldn't by default be dependent, I don't think.

At some point, we will need a way to apply Sigma's.

The only reason we can't internalize substitution with ::[] is because...

id : Π ::[comp _ _ ::[], ::[Σ ::[Ty, Ty]]]

- Will need some mechanism to grab the values inside these objects, UNLESS we design
around them first-class. Kernel should be the only one touching them.
- We want the list context to be maintaing per-Pi binder.
  I like the old Pi design, in this respect.

Once we get to a nil context, we just return the output value.

delimeter is quite problematic.

What we could do is nest Pi at each level, but this is quite ugly looking.
I like the current way.

(Pi ::[::[α, rst], Δ]) (Σ t x) = Pi ::[rst, ::[(Σ t x), Δ]]
-/

/-
Pairs are formed with ⟪a, b⟫.
Operations are sequenced with cons ::[a, b]

Pairs and cons, we almost certainly need to special case to do type inference.
-/

/-
Pi takes in ::[assertions, context]
the assertions is a list where the head element dictates
what the type of the next argument should be from the current
context.

Pi is not a combinator. It requires the list argument.

Sigma is point-free. It is universe polymorphic.
It accepts

Pi eliminates into some sort level.

With universe levels, we should almost certainly:

- Index Pair by the sorts of the type arguments
- Index Pi by the sort it eliminates into.
- Cons can stay as is.
- Sigma is point-free, so we ought to indicate the universe level of the Type argument.
...
Level 1 = Type 0
Level 0 = Prop
-/

abbrev Level := ℕ

inductive Expr where
  | ty    : Level → Expr
  | Pi    : Level → Expr → Expr -- Pi.{[m]} _ : Sort m
  | comp  : Expr  → Expr → Expr -- for composing functions. ::[f, g] x = ($ f, ($ g, x))
  | sigma : Level → Expr -- Σ T x : Prop - this is asserting that (x : T)
  | prop  : Expr -- as usual
  | pair  : Expr   → Expr → Expr
  | app   : Expr  → Expr  → Expr
  | sapp  : Expr -- assumed sapp : Prop → Prop → Prop
  | fst   : Level → Level → Expr -- takes in α β, which are the elements in the pair.
  | snd   : Level → Level → Expr -- takes in α β, which are the elements in the pair.

open Expr

def sort_to_expr : Level → Expr
  | 0 => prop
  | .succ n => ty n

syntax "⟪" term,+ "⟫"      : term
syntax "⸨" term+ "⸩"        : term

notation "Ty" => Expr.ty
notation "Prp" => Expr.prop

infixr:90 " ∘ " => Expr.comp

macro_rules
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f $x)
  | `(⸨ $f $x:term $args:term*⸩) => `(⸨ (Expr.app $f $x) $args*⸩)
  | `(⟪ $x:term ⟫) => `($x)
  | `(⟪ $x:term, $xs:term,* ⟫) => `(Expr.pair $x ⟪ $xs,* ⟫)

/-
None of the terms we introduced above have step rules except for composition, app
and sapp.
-/
inductive IsStep : Expr → Expr → Prop
  | comp   : IsStep ⸨(f ∘ g) x⸩ ⸨f ⸨g x⸩⸩
  | fst    : IsStep ⸨(fst m n) _α _β ⟪a, b⟫⸩ a
  | left   : IsStep f f'
    → IsStep ⸨f x⸩ ⸨f' x⸩
  | right  : IsStep x x'
    → IsStep ⸨f x⸩ ⸨f x'⸩

abbrev 

/-
elements in the context at start:
::[β, α]
-/
def mk_arrow (α β : Expr) (m n : Level := 0) : Expr :=
  (Pi (max m n).succ ⟪⟪⸨(fst m.succ n.succ) (Ty m) (Ty n)⸩
       , ⸨(snd m.succ n.succ) (Ty m) (Ty n)⸩⟫, ⟪α, β⟫⟫)

inductive ValidJudgment : Expr → Expr → Prop
  | sapp : 
