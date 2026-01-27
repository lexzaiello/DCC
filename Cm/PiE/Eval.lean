import Cm.PiE.Ast

open Expr

def do_step_apply (e : Expr) (with_logs : Bool := False) : Except Error Expr := do
  if with_logs then
    dbg_trace e

  match e with
  | ($ ::[x, f], fn) => pure ($ fn, f, x)
  | ($ (nil _m), α, _x) => pure α
  | ($ (.id _o), _α, x) => pure x
  | ($ (.const _o _p), _α, _β, c, _x)
  | ($ (.const' _o _p), _α, _β, c, _x) => pure <| c
  | ($ (.both _o _p _q), _α, _β, _γ, f, g, x) =>
    pure <| ::[($ f, x), ($ g, x)]
  | ($ (.eq _o _p), _α, _β, fn_yes, fn_no, a, b) =>
    if a == b then
      pure <| ($ fn_yes, a)
    else
      pure <| ($ fn_no, b)
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

example : try_step_n 100 ($ (id 2), (Ty 1), (Ty 0)) = (.ok (Ty 0)) := rfl

/-
currying:
snd id = ($ ::[x, f] (id ?)) = ($ f, x)
-/

example : try_step_n 100 ($ ::[(symbol "self"), ($ id 0, (symbol "sorry"))], ($ (id 0), (symbol "sorry")))
   = (.ok (symbol "self")) := rfl

/-
id.{[m]} : ∀ (α : Type m), α → α

which style of type-checking is the kernel going to use?

I feel like we ought to include the entire context, and select what we need.

snd (fst id) normalizes the first component.

what if we want to normalize the first component as well?

is this really necessary? unclear.

We should keep the entire context in each step, though.

after applying one argument, we should get a snd that
includes the argument α

id.{[m]} : ∀ (α : Type m), α → α

this is kind of like rendering a type, I think.

to type-check id:

- need to return type m, but still keep the α.

can do this by appending α to Type m, probably.

t_id = ($ cons, Ty m)

snd id t_id ::[α, t_id]
= id t_id α
= t_id α
= ::[Ty m, α]

for the id type, we accept a Ty m



fst = Ty m, snd = α.

so we need to do some manipulation.

need to select snd, then put it in a future cons.
need to wrap it.

snd

fst =

t id needs to do the work to wrap α in a const.

is function composition still ::?

(f ∘ g) x = ($ f, ($ g, x)

(f ∘ g) x = ::[x, ::[g, f]] =

snd id ::[x, ::[g, f]] = ::[g, f] x

swap order of

::[g, f] x = ($ f, g) x

need parens around g and x



snd (snd id) ::[f, ::[g, x]]
= (snd id) ::[g, x] f
= 

t_id = 

id.{[m]}



type-check an application:

snd (snd id) ::[α, ::[id, id]] = ::[id, id] α

snd (snd id) ::[α, ::[::[

snd (fst id) ::[α, ::[id, id]]
  = (fst id) ::[id, id] α
  = id α

snd (fst id) is the normalization step now. no extra snd.

snd (fst id) is the normalization step, but this means we can only normalize
if we know the number of items in the list.

t_α = ($ (const' m.succ.succ m.succ), Ty m.succ, Ty m id)

snd (snd (const' ? ? )) ::[α, ::[($ (const' m.succ.succ m.succ), Ty m.succ, Ty m id), t_rest]]
  = (snd (const' ? ?)) ::[($ (const' m.succ.succ m.succ), Ty m.succ, Ty m id), t_rest] α
  = t_rest α

this is after applying α.

so, we lose the previous assertion, and receive it in t_rest for substitution

we want to make ::[(const (Ty m) α α), (const (Ty m) α α)]

t_rest α = ::[(const (Ty m) α α), (const (Ty m) α α)]

t_rest α x = snd (fst id) ::[x, ::[(const (Ty m) α α), (const (Ty m) α α)]]
= (fst id) ::[(const (Ty m) α α), (const (Ty m) α α)] x
= id (const (Ty m) α α) x
= α

snd (snd (const' ? ?)) ::[x, ::[(const (Ty m) α α), (const (Ty m) α α)]]
  = (snd (const' ? ?)) ::[(const (Ty m) α α), (const (Ty m) α α)] x
  = (const (Ty m) α α)

but how do we make the const (Ty m) α α part?

we need to duplicate for this, potentially.
but we can get around this if we keep the context around.

instead of snd (snd (const' ? ?)),
if we do



t_rest = ::[

t_rest = 

for t_rest, we want to be 

  feels like we should be able to swap out id here or something.
  or just make t_rest discard the first thing.

this version of snd keeps our assertions context, which is whack.
we now have no way to yeet out the fst part.
snd also accepts the first part.

or we can just have t_rest be okay with this.

t_rest =

id : ∀ (α : Type m), α → α

it's pretty useful to be able to reference (α : Type m)
the term being bound and its type.

::[term, ty]

ctx = ::[::[term₁, ty₁], ::[term₂, ty₂], ::[term₃, ty₃]]

oh interesting.

maybe we want to store the argument terms and types in separate lists.

::[::[term₁, term₂, term₃], ::[ty₁, ty₂, ty₃]]

this is slightly harder to work with for the type-checker, I think.

we're basically filling in the next available slot.

arguments / assertions register idea was kinda nice high key.

::[::[ass₁, ass₂, ass₃], ::[arg₁, arg₂, arg₃]]

so, to type-check ($ (f : t), (x : α)) ::[α, t.fst].snd

thing I'm confused about as well:
very unclear what the advantage is of using list notation here.
well, it's actually very necessary for the assertions list.
that actually is data.

and the assertions do depend on each other.

so we assume we have the entire context with positional arguments.

I think maybe the play is we receive the arguments in the order that they were appended to the context.

so, t_x receives ::[x, α]

t_id = ::[($ const' m.succ.succ m.succ, Ty m.succ, Ty m, Ty m), snd fst, snd fst]

snd fst part is not typed. should fill in types.

what is γ in snd? type of substitution in f.

snd fst receives ::[x, α]

oh shit wait we should use nil here.

::[($ const' m.succ.succ m.succ, Ty m.succ, Ty m, Ty m), nil, nil]

nil will just give us α

type-checking application rules:


($ snd, α, t_id

($ (snd ::[α, t_id]) = 

id : ::[

t_id α = ::[

t_id.{[m]} : 


t_id.{[m]} = ::[
-/

def id.type (m : Level) : Expr :=
  ::[($ nil m.succ, (Ty m)), nil m, nil m]

/-
Test reduction:

snd (fst id) ::[Ty 1, id.type 2]
= (fst id) ::[($ nil m.succ, (Ty m)), nil m, nil m] (Ty 1)
= id ($ nil 3, (Ty 2)) (Ty 1)
= Ty 2

nice.

::[($ nil m.succ, (Ty m)), nil m, nil m]
($ snd? (snd? cons), ::[(Ty 1), id.type 2])

= (snd? cons) ::[($ nil m.succ, (Ty m)), nil m, nil m] (Ty 1)
= ::[::[nil m, nil m], ($ nil m.succ, (Ty m))]

snd? (fst? id?) ::[(Ty 1), ::[($ nil m.succ, (Ty m)), nil m, nil m]]
= (fst? id?) ::[($ nil m.succ, (Ty m)), nil m, nil m] (Ty m)
= ($ nil m.succ, (Ty m))

snd? (snd? id?) ::[(Ty 1), ::[($ nil m.succ, (Ty m)), nil m, nil m]]
= (snd? id?) ::[($ nil m.succ, (Ty m)), nil m, nil m] (Ty 1)
= id? ::[nil m, nil m] ($ nil m.succ, (Ty m)) (Ty 1)

this is kinda whack.

we should restructure the list itself.

ok this is whack.
we want an arguments register.

id? ::[nil m, nil m] ($ nil m.succ, (Ty m)) (Ty 1)

this stuff on the right.
we want to accumulate it as arguyments.
acc as arguments is just yeeting the ($ nil m.succ, (Ty m))

I don't want to restructure the list.
just delete the ($ nil m.succ, (Ty m)), since we can't use const

we need to restructure the list itself.
second argument is going to receive α as well,
but also the previous head?

we change the output getter formula.

snd? (snd? id?) ::[(Ty 1), ::[($ nil m.succ, (Ty m)), nil m, nil m]]

cons ::[nil m, nil m] ($ nil m.succ, (Ty m)) (Ty 1)

(const' 0 0 ?  id? ::[nil m, nil m] ($ nil m.succ, (Ty m)) (Ty 1)

= 
::[nil m, nil m]

interesting. so we forward the entire context,
but it's' not actually applied. strange.

feels like fst and snd should be able to foldl in both directions.
hmmmm.

($ snd? (snd? id?), ::[(Ty 1), ::[($ nil m.succ, (Ty m)), nil m, nil m]])

= snd? id? ::[($ nil m.succ, (Ty m)), nil m, nil m] (Ty 1)
= id ::[nil m, nil m] ($ nil m.succ, (Ty m)) (Ty 1)
= ::[nil m, nil m]

ok wait cooking again?

instead of nil in here what if we use fst and snd?

it would be really awesome if we could just emulate our arguments register in full.

just like keep stacking things on it
so that we can receive all of them.

arguments register kind of is like application,
but potentially harder to work with.

oh wait cool idea.

($ snd? (snd? id?), ::[(Ty 1), ::[($ nil m.succ, (Ty m)), nil m, nil m]])
we get (Ty 1) as an argument.

we need to set up the type-checking rules so as to remove old
dead registers.

at the very least, the old registers should be included in a list as data.

($ snd? (snd? id?), ::[(Ty 1), id.type 2])
= (snd? id?) ::[($ nil m.succ, (Ty m)), nil m, nil m] (Ty 1)
= ::[nil m, nil m] ($ nil m.succ, (Ty m)) (Ty 1)
=

(snd? id?) ::[($ nil m.succ, (Ty m)), nil m, nil m] (Ty 1)
can chagne id here to const something.

snd? (const ? ?) ::[($ nil m.succ, (Ty m)), nil m, nil m] (Ty 1)
  = (const ? ?) ::[nil m, nil m] ($ nil m.succ, (Ty m)) (Ty 1)


feels like there are places where we would want access to our context,
but it might make it harder to traverse, since our snd / fst calls
will need to be well-typed.

oh interesting idea:

- we would like to avoid explicit types inside our type expressions
the challenge comes from using snd as a function.

what if instead we could plug our "selector" into the sigma type.

This way, we don't have to make the selector well-typed,
the sigma type itself does.

lists are applications,
so the types of the elements are inferred.

can we store the inferred type somewhere?
or do some kind of trick to shortcut generating the type?

::[(x : α), (f : (β : α → Type))] : (

another note:
the sigma pair should not constrain its members to be strictly
pure, depend

we should have some mechanism for just lining up some "selector"
with the elements in the pair.

how do we switch between fst and snd?

::[

it feels like we should be able to dynamically upgrade a pair type
into a sigma type by offloading the constraints for application
to the user somehow.

Ok, interesting.

feels like the selector is determining which things it depends on
in the context.

kinda just like normal ∀ (x : α) (y : β)

::[(x : α), (y : β)] - this is a context

how do things in the context depend on each other?

I quite liked our assertions vs arguments idea.

it was working quite well.

sigma types = red herring?

fst corresponds to the actual type of the first argument.
snd corresponds to substitution.

substitution needs to work nicer.

our current design is fine,
but it would be nice if we could
abstract out snd and fst
so as to not require explicit type arguments.

| ($ (fst _m _n), _α, _β, _γ, fn, ::[a, _b]) => pure ($ fn, a)
| ($ (snd _m _n), _α, _β, _γ, fn, ::[x, f]) => pure ($ fn, f, x)

α and β here seem kind of duplicates.

($ ::[x, f] fn) = ($ fn, f, x)

this handles the snd case,
but it doesn't handle the fst case.

fst wants just x
fst feels like syntax sugar, potentially,
for const ? ?

| ($ (fst _m _n), _α, _β, _γ, fn, ::[a, _b]) => pure ($ fn, a)
| ($ (snd _m _n), _α, _β, _γ, fn, ::[x, f]) => pure ($ fn, f, x)

($ ::[x, f] fn) = ($ fn, f, x)

-- simulating `fst` to get just x.
($ ::[x, f] (const ? ? (id ?))) = ($ (const ? ? (id ?)), f, x)
= ($ (id ?), x) = x

-- simulating `snd` like before.
-- we want ($ fn, f, x)
-- this is due to the new eval rule
($ ::[x, f] fn) = ($ fn, f, x)

γ : 

::[(x : α), (f : β)] : (∀ (γ : ∀ (x : α) (f : β)
-/

-- need γ placeholder

def id? : Expr := ($ Expr.id 0, Ty 0)

#eval try_step_n 100 ($ snd? (snd? id?), ::[(Ty 1), id.type 2])

#eval try_step_n 100 ($ snd? (fst? id?), ::[(Ty 1), id.type 2])

-- (x : α). need to get the substituted context.
#eval try_step_n 100 ($ snd? (snd? cons), ::[(Ty 1), id.type 2])

#eval try_step_n 100 ($ snd? (fst? id?), ::[(Ty 1), id.type 2])

example : try_step_n 100 (snd! ∘ fst! ∘ snd! <| ::[(Ty 1), id.type 2]) = (.ok (Ty 2)) := rfl

#eval try_step_n 100 (snd? <| ::[(Ty 0), (snd? ∘ snd? <| ::[(Ty 1), id.type 2])])

namespace hole

/-
id.{[m]} : ∀ (α : Type m), α → α

todo: need a nil here
t_id = ::[:: (Ty m), ::[($ cons, ::[id (Ty m), id (Ty m)]), nil]]

::[α, t_id].snd = (.app t_id.snd α) = ::[α, id (Ty m), id (Ty m)]

::[α, id (Ty m), id (Ty m)].snd = (.app ::[id (Ty m), id (Ty m)].snd α)
= (.app (id (Ty m)) (id (Ty m))).app α
= (id (Ty m)).app α

::[::[:: (Ty m), stuff]

::[x, f].snd = (.app f.snd x)
id.{[m]} : ::[
-/

end hole
