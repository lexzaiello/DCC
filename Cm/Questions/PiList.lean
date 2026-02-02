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

  ::[a, b] x = ::[(a x), (b x)]

  This could be nice, since it propogates the value easier than we could with both.
  Remember: list application is a special case anyway.

#3: Can we make our "substitution" operation comport with our interpration of sigma pairs?

  ::[a, b] - a ought to depend on b, not the other way around. Cons is most efficient in this position.

  ::[(a : (β : α → Type)), (b : α)] : (β ∘ α)?

  So, substitution ought to proceed like such:

  ::[a, b] x = ::[(a (b x)), (b x)]. This way, the type dependency is preserved.

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
-/

inductive Expr where
  | app : Expr → Expr → Expr
  | ty  : Expr
  
