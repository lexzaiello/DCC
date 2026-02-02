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

  ::[(a : (β : α → Type)), (b : α)] : ::[β, α]?

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

#8: Should fst and snd be in head or tail position?
  - Our pairs might not necessarily be functions. We should prefer head position.
  It's also easier to use, and bridges the gap.

#9: What about grabbing fst after an operation. Can we do that easily?

  ::[fst, my_op] x = ::[(fst (my_op x)), my_op x]

  Kind of. At some point, we will need something like S for terms. What's bridging this gap for us?
  We can embed applications with composition quite easily.

  We could also make fst be cleverer by substituting into a list.

Core design changes:
- ::[a, b] x = ::[a (b x), b x] - list substitution works more as expected now.
And, it acts like composition out of the box.
  - Pair and Pi are just syntax markers. That's all. Pi l arg = Pi (l arg). Pair l arg = Pair (l arg). For the kernel to interpret.
  - Can still do composition
- Explicit fst and snd combinators are important. And, we can express their types more easily, now.
  - fst ::[a, b] arg = a (b arg)
  - snd ::[a, b] arg = b arg
  - Bridge from lists to app terms.
- Prod and Pi coincide exactly with substitution now.
- fst and snd are in head position, not tail position.

Remaining questions:
- Can we make Pi point-free? Answer: no, it's a useful syntactic marker. Same with Prod.
- We might benefit from a "take" combinator.
- How will we type sigma pairs? ::[(x : (α : β → Type)), (xs : β)] : Pair ::[α, β]
- Will we still need separate app rules for Pi vs Pair? Probably. I think it makes sense. These are very discrete things.

Does both still preserve the type dependency? Seems like not really. Not sure about this one. Will find the answer though.
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
  | fst    : Expr
  | snd    : Expr

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
  | sapp   : IsStep ($ ::[a, b], x) ::[($ a, ($ b, x)), ($ b, x)]
  | fst    : IsStep ($ fst, α, β, γ, ::[a, b], arg) ($ a, ($ b, arg))
  | snd    : IsStep ($ snd, α, β, γ, ::[a, b], arg) ($ b, arg)
  | nil    : IsStep ($ nil, α, x) α
  | id     : IsStep ($ Expr.id, _α, x) x
  -- both α β γ (f : γ) (g : β) (arg : α) = ::[($ const', ($ γ, arg), ($ β, arg), ($ f, arg)), g] arg
  | both   : IsStep ($ both, _α, β, γ, f, g, x) ::[($ const', ($ γ, arg), ($ β, arg), ($ f, arg)), ($ g, arg)]
  | const' : IsStep ($ const', _α, _β, x, y) x
  | const  : IsStep ($ const, _α, _β, x, y) x
  | left   : IsStep f f'
    → IsStep ($ f, x) ($ f', x)
  | right  : IsStep x x'
    → IsStep ($ f, x) ($ f, x')

syntax ident ".{" term,* "}"  : term
syntax "::[" term,+ "]"       : term
syntax "($" term,+ ")"        : term

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | step    : IsStep e e' → DefEq e e'
  | symm    : DefEq e₁ e₂ → DefEq e₂ e₁
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ($ f, x) ($ f', x)
  | right   : DefEq x x'  → DefEq ($ f, x) ($ f, x')
  | lright  : DefEq f f'  → DefEq ::[x, f] ::[x, f']
  | lleft   : DefEq x x'  → DefEq ::[x, f] ::[x', f]
  | subst   : DefEq ($ ($ Pi, bdy), x) ($ ($Pi, bdy₂), x)
    → DefEq ($ Pi, bdy) ($ Pi, bdy₂)

/-
Cons is typed, by default, as Pair ::[α, β]
Pi expects any list, but it expects specifically t_in and t_out registers, at least.

Another thought on both:
both α β γ (f : γ) (g : β) (arg : α) = ::[($ const', ($ γ, arg), ($ β, arg), ($ f, arg)), g] arg
γ : α → Type
β : α → Type
γ arg
β arg

Does this both rule work as expected?
Maybe not?

Can we stil derive Pi?

It feels like by default we should assume that there is dependency from
map_arg -> t_in -> t_out.

And if we don't want it, we use both.

This way, Pi is not complex at all.

Pi : ∀ {map_arg : α → β} {t_in : β → γ} {t_out : γ → δ}, Prod ::[t_out, ::[t_in, map_arg]] → Type



since prod members are preserved, we can assume

- fst ::[a, b] arg = a (b arg)
- snd ::[a, b] arg = b arg

t_out:   Pi l, fst l
t_in:    Pi l, fst (snd l)
map_arg: NOT NECESSARY NOW. we get dependency by default.

So, Pi : Prod ::[t_out, t_in] → Type

Prod : ∀ {α : Type} {β : α → Type} {γ : Type → Type}, Prod ::[γ, β] → Type

So, how do we make this arrow?

Prod ::[t_out, t_in] → Type = Prod ::[($ nil, Type), Prod ::[t_out, t_in]]
-/

inductive ValidJudgment : Expr → Expr → Prop
  | Pi : ValidJudgment Pi ($ Prod, ::[($ nil, Type), ($ Prod, ::[t_out, t_in])])
