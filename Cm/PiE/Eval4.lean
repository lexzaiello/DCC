import Cm.PiE.Ast

open Expr

/-
sigma is the opposite of app.

app is curried application.

Feels like our evaluation rules should probably work with sigma arguments, then.

(.app (f : t_f) (x : α)) : ::[x, t_f].snd.fst.snd

if sigma is the opposite of application, then what is the opposite of:

(.app (.app f x) y)?

::[y, x, f]

need some way to convert this^ into (.app (.app f x) y)

::[y, x, f].? = (.app ::[x, f].? f)

maybe want to show this as a sigma type instead?
feels like this operation should produce another sigma type

wait this is interesting.

::[y, x, f].snd.fst =

::[y, x, f].? = (.app (.app f x) y)

::[a, b].snd = (.app b a),
but we need to nest. so there is either two separate rules,
or just one smart recursive one.
but we need to permit terminal applications as well.

::[a, b].snd = (.app b a)
::[a, ::[b, c]].snd = (.app

snd should produce another sigma pair that we can follow,
or something that isn't a sigma pair

::[a, ::[b, c]].snd

interesting.
maybe we need an evaluation rule for sigma pairs?

or maybe we can use nil as the terminal value?

interesting.

::[a, ::[b, c]].snd

::[a, ::[b, nil?]].snd =
.app (::[b, nil?].snd) a


::[b, nil?].snd = .app b nil = b

perfecto
we can have an eval rule for nil that makes this work well.
this is kind of a special case.

terminal app here feels weird.
::[x, ::[α, (id 0)]] : ((x : α) × ((y : β) × (f : ∀ (x : α) (y : β), t x y)))

id 0 in terminal position will not have the same evaluation rule.
maybe we add a special case for .snd for nested sigma, but this doesn't correspond exactly to the type.

nesting feels fine, but we can use our wonky nil delimiter idea potentially.

nil α x = α
nil : ∀ (α : Ty) (x : α), α

::[x, ::[α, (id 0)]] : ((x : α) × ((y : β) × (f : ∀ (x : α) (y : β), t x y)))

::[x, ::[α, ((id 0) : ]].snd : 

l.snd : ∀ (l : ((x : α) × ((y : β) × xs
-/

/-
(.app f x) as usual. this is a curried application.
::[x, f].snd = .app (f x) where f is not a nested sigma pair
::[y, ::[x, f]].snd = .app ::[x, f].snd y = (.app (.app f x) y) where f is not a sigma

we could leave snd as just application,
and add just put a .snd nested inside,
maybe,
but I want to be able to recurse

(y : β) × (x : (t : β → Type))

does this work with nested sigma types?

interesting. this does feel like the nil delimiter should work.
but a nested sigma pair probably wouldn't.

((x : α) × (y : (β : α → Type)) : Type)
(y : β) × (x : (t : β → Type))

partially applied sigma pair? this could be it
partially applied application?

sigma type application is first class, so we should handle that first.
we want to recover unapplied argument: TODO

::[y, ::[x, .app f]]

::[x, f].snd = .app f.snd x

where f is a terminal value
::[nil, f].snd this is a nondependent pair.
if we can derive them, then we're golden,
since .snd will produce a constant f, then.

::[f, nil].snd = .app (nil.snd f)
nil feels like it should be a sigma pair type
that just outputs the constant argument.

perfect.

equations:

::[x, f].snd = .app f.snd x

nil.snd = nil?
this implies that nil is a sigma type pair,
but applying it to something feels like a different type.

nil.snd has no evaluation rule.
nil.snd = id but with the type filled in.

(nil α).snd = 

nil.snd = nil
::[x, ::[f, nil]].snd
  = .app ::[f, nil].snd x
  = (.app nil.snd f)
  = f
(

Reductions:

::[x, f].snd = .app f.snd x
(nil.{[m]} α).snd = .app (id m) α

we assume currying by default.

snd takes explicit type arguments.
need some way to denote the result of applying the inner value

snd α ? ((x : α) × (β : α → Type))

perhaps β is the entire type of f?
if f is also a sigma pair...

need some type to denote .snd beta reduction
without an infinite chain

clearly, sigma application should apply to the types.
no easy way to recover the universe arguments
from β



to type check ::[x, f].snd:

Sigma.snd.{[m, n]} : ∀ (α : Type) (β : α → Type m) (l : ((x : α) × (y : β)))

but then we don't know how to fill in the nested snd's types.

sigma.snd was difficult to write, since it took explicit type arguments.

β refers to the reduced type of f,
snd should beta reduce internally,
so it probably doesn't matter what the types are.
dummy values.

the second universe for nested snd is obviously n.

but what about the first?
and what about the nested α argument?

nested snd's β should just be a constant β.


new nil eval rule doesn't vibe with "closing the loop" in a dependent type,
but we will figure it out.
-/

def do_step_apply : Expr → Except Error Expr
  | ($ (fst _m _n), _α, _β, ::[a, _b]) => pure a
  | ($ (snd m n), α, β, ::[x, f]) =>
    let ret_inner_t := ($ (const m.succ n), (Ty m), β, α)
    let reduce_f := ($ (snd m n), α, ret_inner_t, f)
    pure ($ reduce_f, x)
  | ($ (snd _m _n), _α, _β, ($ (nil o), α)) => pure ($ (id o), α)
  | ($ (.id _o), _α, x) => pure x
  | ($ (.const _o _p), _α, _β, c, _x) => pure <| c
  | ($ (.both o p q), α, β, γ, f, g, x) => -- TODO: not sure whether to nest ::[f, g] here, or leave flat
    pure <| ::[($ (snd o p), α, β, ::[x, f]), ($ (snd o q), α, γ, ::[x, g])]
  | ($ (.eq o p), α, β, fn_yes, fn_no, a, b) =>
    if a == b then
      pure <| ($ (snd o p), α, β, ::[a, fn_yes])
    else
      pure <| ($ (snd o p), α, β, ::[b, fn_no])
  | e => .error <| .no_rule e

def run (e : Expr) : Except Error Expr := do
  do_step_apply e <|> (match e with
  | ($ f, x) => (do
    let f' ← run f
    let x' ← run x
    pure <| ($ f', x')) <|> (do
    let f' ← run f
    pure <| ($ f', x)) <|> (do
    let x' ← run x
    pure <| ($ f, x'))
  | e => .error <| .stuck e)

def try_step_n (n : ℕ) (e : Expr) : Except Error Expr :=
  match n with
  | .zero => pure e
  | .succ n =>
    match run e with
    | .ok e' => try_step_n n e' <|> (pure e')
    | .error e => .error e

example : try_step_n 100 ($ (snd 0 0), Ty 0, Ty 0, ::[id 2, ($ (nil 0), (Ty 0))]) = (.ok (id 2)) := rfl

example : try_step_n 100 ($ (id 2), (Ty 1), (Ty 0)) = (.ok (Ty 0)) := rfl

/-
Sigma application ending in a terminal application with nil
-/
example : try_step_n 100 ($ (snd 0 0), (Ty 1), (Ty 1), ::[Ty 0, Ty 1, ::[id 2, ($ (nil 0), (Ty 0))]]) = (.ok (Ty 0)) := rfl


