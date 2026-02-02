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
-/

inductive Expr where
  | app    : Expr → Expr → Expr
  | cons   : Expr → Expr → Expr
  | Pi     : Expr
  | Prod   : Expr
  | ty     : Expr
  | const  : Expr
  | const' : Expr
  | both   : Expr
  | id     : Expr
  | nil    : Expr
  | snd    : Expr

syntax ident ".{" term,* "}"  : term
syntax "::[" term,+ "]"       : term
syntax "($" term,+ ")"        : term

macro_rules
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.cons $x ::[$xs,*])
  | `(($ $x:term) ) => `($x)
  | `(($ $f:term, $x:term )) => `(Expr.app $f $x)
  | `(($ $f, $x:term, $args:term,* )) => `(($ (Expr.app $f $x), $args,*))

notation "Ty" => Expr.ty

open Expr
