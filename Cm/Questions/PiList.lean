import Mathlib.Data.Nat.Notation

/-
#1: Is it possible to merge Pi and lists?

  It would be ideal if Pi could handle the substitution on lists, but if we could make Pi from a list.

  - Pi t_in t_out map_arg
    ^
  Note that t_in depends on map_arg
  and t_out depends on map_arg

  so we are essentially substituting.

#2: Is it possible to upgrade our lists to do proper substitution?

  ::[a, b] x = ::[(a x), (b x)]. NO, see #3.

  This could be nice, since it propogates the value easier than we could with both.
  Remember: list application is a special case anyway.

#3: Can we make our "substitution" operation comport with our interpration of sigma pairs?

  ::[a, b] - a ought to depend on b, not the other way around. Cons is most efficient in this position.

  ::[(a : (β : α → Type)), (b : α)] : (β ∘ α)?

  So, substitution ought to proceed like such:

  ::[a, b] x = ::[(a (b x)), (b x)]. This way, the type dependency is preserved.

  What about nesting? Seems fine.

  The head element was updated, and the tail was updated.

#4: Can we still do composition with this semantics? Is it possible to make substitution "nicer"?
or at least behave as before?

  ::[g, f] x = fst ::[(g (f x)), (f x)]

#5: With our Prod types, or at the very least with this type dependency, would it be easier to type fst and snd?

  ::[(g : α), (f : β)]
  fst α β : Prod α β → (α fst.snd)

#6: If we form Pi from a list, then we are composing substitution in map_arg with
  substitution in t_in t_out

  Pi t_in t_out map_arg = ::[both ::[nil t_in, t_out], map_arg]

  Pi ::[(both ::[t_in, t_out]), map_arg]

  So Pi is basically just a marker that this is a Type?
  Is Prod also subsumed by this? I think so, actually.

  ::[(a : (β : α → Type)), (b : α)] : Pi ::[β, ($ id, α)]

#7: Now that we have substitution, is point-free cons necessary? Probably not, but why?
-/

inductive Expr where
  | app    : Expr → Expr → Expr
  | cons   : Expr → Expr → Expr
  | Prod   : Expr → Expr → Expr
  | Pi     : Expr
  | ty     : Expr
  | const  : Expr
  | const' : Expr
  | both   : Expr
  | id     : Expr
  | nil    : Expr

syntax ident ".{" term,* "}"  : term
syntax "::[" term,+ "]"       : term
syntax "($" term,+ ")"        : term

macro_rules
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.cons $x ::[$xs,*])
  | `(($ $x:term) ) => `($x)
  | `(($ $f:term, $x:term )) => `(Expr.app $f $x)
  | `(($ $f, $x:term, $args:term,* )) =>
    `(($ (Expr.app $f $x), $args,*))

notation "Ty" => Expr.ty

open Expr

inductive IsStep : Expr → Expr → Prop
  | sapp : IsStep ($ ::[a, b], x) ::[($ a, ($ b, x)), ($ b, x)]
  | nil    : IsStep ($ nil, α, x) α
  | id     : IsStep ($ Expr.id, _α, x) x
  | both   : IsStep ($ both, _α, _β, _γ, ::[f, g], x) ::[($f, x), ($ g, x)]
  | const' : IsStep ($ const', _α, _β, x, y) x
  | const  : IsStep ($ const, _α, _β, x, y) x
  | left   : IsStep f f'
    → IsStep ($ f, x) ($ f', x)
  | right  : IsStep x x'
    → IsStep ($ f, x) ($ f, x')
