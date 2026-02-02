import Mathlib.Data.Nat.Notation

/-
Type assertions should be able to see their own expressions, but as pairs.

⟨snd, ⟨id, α, x⟩⟩

head of the head is the assertion for e.

⟨⟨t, xs⟩, e⟩

- Append to e as we go along, inside out. ⟨_, id⟩ -> ⟨_, ⟨x, α, id⟩⟩
- Shrink T as we go along.

⟨⟨fst, ⟨::[fst, snd], ::[fst, ::[snd, snd]]⟩⟩, Ty⟩, α looks good, so
⟨⟨::[fst, snd], ::[fst, ::[snd, snd]]⟩, ⟨α, Ty⟩⟩, ::[fst, snd] ⟨α, Ty⟩ = Ty

This looks pretty chill ngl.

Core language:

- Cons, for composition, special-cased, since we have both Expr's, so we can infer.
- fst : (Prod ....)

⟨a, b⟩ is not dependent, but Prod is

Prod is flipped? first element depends on the second.

We could type fst as just Syntax, but then we run into issues once we get to more complicate arguments.

Another idea:

We always place terms next to their types.

⟨x, α⟩

fst : ⟨⟨fst, _⟩, Prod ($ id, Ty) Ty⟩

fst : ⟨⟨fst, ::[fst, snd]⟩, Prod Ty ($ id, Ty)⟩

fst x : ⟨⟨fst, 

snd is just taking a (Prod a b) and producing b

head element always look like this, though:
Prod ($ id, Ty) Ty

snd : ⟨⟨

app rule:

elements in the list always look like ⟨x, α⟩

α is current arg assert, β is next arg assert
(((f : ⟨⟨α, β⟩, Γ⟩)
  (x : ($ α, Γ))) : ⟨β, ⟨⟨x, ($ α, Γ)⟩, Γ⟩⟩

We will have issues again with nil delimeters, maybe.
maybe not?

Core elements so far:
- composition (cons)
- pairs ⟨a, b⟩
- apps ($a, b)
-/

inductive Expr where
  | app    : Expr → Expr → Expr
  | cons   : Expr → Expr → Expr
  | pair   : Expr → Expr → Expr
  | fst    : Expr
  | snd    : Expr
  | Prod   : Expr
  | ty     : Expr
  | const  : Expr
  | const' : Expr
  | both   : Expr
  | id     : Expr
  | nil    : Expr

syntax "::[" term,+ "]"       : term
syntax "($" term,+ ")"        : term
syntax "⟪" term,+ "⟫"  : term

macro_rules
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.cons $x ::[$xs,*])
  | `(($ $x:term) ) => `($x)
  | `(($ $f:term, $x:term )) => `(Expr.app $f $x)
  | `(($ $f, $x:term, $args:term,* )) => `(($ (Expr.app $f $x), $args,*))
  | `(⟪ $x:term ⟫) => `($x)
  | `(⟪ $x:term, $xs:term,* ⟫) => `(Expr.pair $x ⟪ $xs,* ⟫)

notation "Ty" => Expr.ty

open Expr

inductive IsStep : Expr → Expr → Prop
  | fst    : IsStep ($ fst, ⟪ a, b ⟫) a
  | snd    : IsStep ($ snd, ⟪ a, b ⟫) b
  | comp   : IsStep ($ ::[f, g], x) ($ f, ($ g, x))
  | id     : IsStep ($ id _α, x) x
  | left   : IsStep f f'
    → IsStep ($ f, x) ($ f', x)
  | right  : IsStep x x'
    → IsStep ($ f, x) ($ f, x')

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | step    : IsStep e e' → DefEq e e'
  | symm    : DefEq e₁ e₂ → DefEq e₂ e₁
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ($ f, x) ($ f', x)
  | right   : DefEq x x'  → DefEq ($ f, x) ($ f, x')
  | lleft   : DefEq a a'  → DefEq ⟪ a, b ⟫ ⟪ a', b ⟫
  | lright  : DefEq b b'  → DefEq ⟪ a, b ⟫ ⟪ a, b' ⟫

def id.type : Expr :=
  ⟪ ⟪ ::[fst, fst], ::[fst, fst], ::[snd, fst] ⟫, ⟪ Ty, Ty ⟫ ⟫

/-
nil : ∀ (α : Type), α → Ty
-/
def nil.type : Expr :=
  ⟪ ⟪ ::[fst, fst], ::[fst, fst], ::[snd, snd, snd] ⟫, ⟪ Ty, Ty ⟫ ⟫

inductive ValidJudgment : Expr → Expr → Prop
  | ty  : ValidJudgment Ty Ty
  | app : ValidJudgment f ⟪ ⟪ α, β ⟫, Γ ⟫
    → ValidJudgment x ($ α, Γ)
    → ValidJudgment ($ f, x) ⟪ β, ⟪ ⟪ x, ($ α, Γ) ⟫, Γ ⟫ ⟫
  
