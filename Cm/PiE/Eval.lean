import Cm.PiE.Ast

open Expr

def do_step_apply (e : Expr) (with_logs : Bool := False) : Except Error Expr := do
  if with_logs then
    dbg_trace e

  match e with
  | ($ ::[x, f], fn) => pure ($ fn, f, x)
  | ($ (nil _o), α, _x) => pure α
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
::[(x : α), (f : β)] {γ : α → β → Type}: (f : γ) → γ f x
-/

/-
Using this, new id type:

assuming (id.{[m]} : t_id.{[m]}) and (α : Ty m) (x : α)

snd (fst id) = ($ ::[α, ::[($ nil m.succ, (Ty m)), stuf]], (const ? ? (id ?)))
= (const ? ? (id ?)) ::[($ nil m.succ, (Ty m)), stuf] α
=

interesting.
disadvantage to new eval rule is our selector goes after,
but we put it before.
composition becomes slightly more difficult.

can we put fn after? does that work?
wait.

can we make the fn selector itself a list?

snd (fst id) = ($ ::[α, ::[($ nil m.succ, (Ty m)), stuf]], (const ? ? (id ?)))
= (const ? ? (id ?)) ::[($ nil m.succ, (Ty m)), stuf] α

interesting.

snd (fst id) = ($ ::[($ nil m.succ, (Ty m)), stuf], (const ? ? ?))
= (const ? ? ?) stuf ($ nil m.succ, (Ty m))
= ? ($ nil m.succ, (Ty m))

($ nil m.succ, (Ty m)) = fn in list app

[?x, ?f] can be a list now.

($ ($ nil m.succ, (Ty m)), ?f, ?x)

we can make ($ nil m.succ, (Ty m)) literally just id?
or get the head of the list?

thinking we pass in a nil delimited list.
I think we ought to remove nil eval rule.
nil is just list delimiter.

snd (fst id) = ($ ::[($ nil m.succ, (Ty m)), stuf], (const ? ? ?))

? = ::[α, nil]

($ nil m.succ, (Ty m)) =

observations:
- supply arguments δ as a nil delimited list so we can use list operations on it
- first element in id type list just selects the head.
- first element in id type is supposed to output (Ty m)
- second element in id type

procedure for type-checking:
- since output values in the context don't depend on the context itself,
we can just offload substitution to the kernel.

id.{[m]} : t_id.{[m]}

to check:
($ t_id.{[m]}, (const ? ? (id ?)))
= ($ (const ? ? (id ?)), t_id.tail, t_id.head)
= ($ id ?, t_id.head)

now have:
t_id.head

t_id.head = ($ const' m.succ.succ m.succ, (Ty m.succ), Ty m, Ty m)

t_id.tail = stuff

($ t_id.head, α) = Ty m

- to get tail:
($ t_id.{[m]}, (const ? ?))
= ($ ($ const ? ?), t_id.tail, t_id.head)
= t_id.tail


t_id.{[m]} = ::[($ const' m.succ.succ m.succ, (Ty m.succ), Ty m, Ty m), 


::[::[α, nil], ::[(const ? ? (id ?)), stuff]]

($ ::[::[α, nil], ::[(const ? ? (id ?)), stuff]], (const ? ? (id ?)))
= (const ? ? (id ?)), ::[(const ? ? (id ?)), stuff], ::[α, nil]
= 

? = ::[

($ ::[x, f] (const ? ? (id ?))) = ($ (const ? ? (id ?)), f, x)
= ($ (id ?), x) = x


($ ::[x, f] (const ? ? (id ?))) = ($ (const ? ? (id ?)), f, x)
= ($ (id ?), x) = x

simulating fst
($ ::[x, f] (const ? ? (id ?))) = ($ (const ? ? (id ?)), f, x)
= ($ (id ?), x) = x

t_id.{[m]} = ::[($ nil m.succ, (Ty m)), stuf]

::[α, ::[($ nil m.succ, (Ty m)), stuf]] 

t_id.{[m]}
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

first assert just outputs Type m
second assert accepts α
and creates ::[($ const? m.succ, Type m
we may need to copy α
to create a const that deletes Ty mid.{[m]} : ::[($ const? m.succ.succ m.succ, Type m.succ, Type m, Type m),

or we will need to copy α into two nil's.
we will need both for this.

(:: both (:: (cons (nil m)) (cons (nil m))))

($ (both 0 0 0), ?, ?, ?,

both f g x = ::[(f x), (g x)]
both : ∀ (α : Type) (β : α → Type) (γ : α → Type) (f : β) (g : γ) (x : α), (× (β x) (γ x))

α : Ty m
β α = α → Ty m = ::[$ nil m.succ, 
γ α = α → Ty m

($ both m m.succ m.succ, (Ty m), ((cons (nil m)),  (cons (nil m)))

this is going to be mad annoying to get to be well-typed.

we can get α into the head argument position pretty easily,
but we can't get it into the return type position as easily.

it would be pretty useful if the context retained ALL our arguments.

we can do this by making a future context with α,
and adding x to it.

we can do this very sneakily by making ::[α, α]

would be ideal if when type-checking,
we feed the argument in at the top-level

check in ::[t_in, t_out]

Note: our "selector" makes this possible.

($ const' (m.getD 0) (n.getD 0), (α.getD ?), (β.getD ?), ($ (id (o.getD 0)), (γ.getD ?)))

we can almost certainly swap id here with a selector.
the selector could be a ::[]
selector is ctx sigma.

assuming all of our in and out asserts receive the entire context:

id.{[m]} : ::[

($ ::[x, f] (const ? ? (id ?))) = ($ (const ? ? (id ?)), f, x)
= ($ (id ?), x) = x

note that simulating fst takes this id argument.
this is our selector.

id.{[m]} : ::[($ nil m.succ m, Type m),
  
-/

-- need γ placeholder

/-
Expression to get the head of an assertions list.
-/
def func_type_head? (m n o : Option Level := .none) (α β γ : Option Expr := .none) : Expr :=
  ($ const' (m.getD 0) (n.getD 0), (α.getD ?), (β.getD ?), ($ (id (o.getD 0)), (γ.getD ?)))

/-
Generic over the selector.
($ selector, head_assert)

($ my_asserts ($ select_fn_type_head?, my_selector))
= ($ my_selector, head_assert)
-/
def select_fn_type_head? (m n : Option Level := .none) (α β : Option Expr := .none) : Expr :=
  ($ const' (m.getD 0) (n.getD 0), (α.getD ?), (β.getD ?))

def select_fn_tail? (m n : Option Level := .none) (α β : Option Expr := .none) : Expr :=
  ($ 


#eval try_step_n 100 <| ($ ::[symbol "in", symbol "out"], func_type_head?)

/-
Expression to get the tail of an assertions list.
-/
def func_type_out? (m n : Option Level := .none) (α β : Option Expr := .none) : Expr :=
  ($ const' (m.getD 0) (n.getD 0), (α.getD ?), (β.getD ?))

#eval try_step_n 100 <| ($ ::[symbol "in", symbol "out"], func_type_out?)

def test_check (t_f t_arg arg : Expr) : Except Error Expr := do
  let out ← try_step_n 100 ($ ($ t_f, func_type_head?), arg)
  let ret ← try_step_n 100 ($ ($ t_f, func_type_out?), arg)

  if t_arg == out then
    .error <| .mismatch_arg out t_arg
  else
    pure ret

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
