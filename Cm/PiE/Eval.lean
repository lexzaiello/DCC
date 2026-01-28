import Cm.PiE.Ast

open Expr

/-
snd rule feels kinda wrong ngl.

::[x, f] fn = ($ fn, f, x)

feels like this should actually be

($ ($ f, fn), x)

::[y, ::[x, f]] id
= ($ ($ ::[x, f], id) y)
=

× α β. this is something where projection produces

old snd
snd fn ::[x, f] = ($ fn, f, x)

So our current evaluation rule should be fine.
It's just whether we can recurse or not.

But, this answers our sigma type question, pretty much.

::[(x : α), (f : β)] : {γ : α → β → Type} (∀ (f : β) (x : α), γ f x)

I think we can also do sigma fst.

::[x, f] (const' ...)
= (const' ...) f x = x. this is right

sigma snd is just id, since that's application.
-/

#eval repr ::[($ symbol "f", symbol "x"), ($ symbol "g", symbol "x")]

/-
Expr.app
  (.app .cons (.app f x))
  (.app g x)
-/

inductive is_step : Expr → Expr → Prop
  | sapp   : is_step ($ ::[x, f], fn) ($ fn, f, x)
  | nil    : is_step ($ (nil _o), α, _x) α
  | id     : is_step ($ (.id _o), _α, x) x
  | const  : is_step ($ (.const _o _p), _α, _β, c, _x) c
  | const' : is_step ($ (.const' _o _p), _α, _β, c, _x) c
  | both   : is_step ($ (.both _o _p _q), _α, _β, _γ, f, g, x) ::[($ f, x), ($ g, x)]
  | eq_yes : a == b → is_step ($ (.eq _o _p), _α, _β, fn_yes, fn_no, a, b)
    (.app fn_yes a)
  | eq_no  : a ≠ b → is_step ($ (.eq _o _p), _α, _β, fn_yes, fn_no, a, b)
    (.app fn_no b)
  | left   : is_step f f'
    → is_step ($ f, x) ($ f', x)
  | right  : is_step x x'
    → is_step ($ f, x) ($ f, x')

#eval repr (::[symbol "a", symbol "b"])

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

#eval try_step_n 100 ($ ::[(symbol "x"), (symbol "f")], ($ (Expr.id 0), (.symbol "α")))

example : try_step_n 100 ($ (id 2), (Ty 1), (Ty 0)) = (.ok (Ty 0)) := rfl

/-
currying:
snd id = ($ ::[x, f] (id ?)) = ($ f, x)
-/

example : try_step_n 100 ($ ::[(symbol "self"), ($ id 0, (symbol "sorry"))], ($ (id 0), (symbol "sorry")))
   = (.ok (symbol "self")) := rfl

/-
Tricky thing with writing assertions is that our combinators are 
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

/-
Notes:
- for id type, grow the context with α intact.

- making the assert for x is quite simple.
we need some way to make sure that snd = fst.

-- this is fst
-- for id, we plug in ::[α, nil]

If we make each step of the assertion
take the entire context,
we can very idiomatically traverse it.
this is definitely ideal.

then, α assert becomes (fst id)

we can almost certainly defer this to the meta layer.
no reason to over complicate.

we need to be able to represent the grown context with the out_t
such that we can plug in the next argument.

($ ::[x, f] (const ? ? (id ?))) = ($ (const ? ? (id ?)), f, x)
= ($ (id ?), x) = x

id = ::[α, nil]

($ ::[t_in, t_out] (const ? ? (::[α, nil])))
= ($ (const ? ? (::[α, nil])), t_out, t_in)
= ($ ::[α, nil], t_in)
t_in = fst
= α

for t_out, we don't handle the traversal at runtime.
just pattern match it out.

need some way to append to the context,
then run.

assuming we got here
($ ::[t_in', t_out] (const ? ? (::[α, nil])))

and assuming next arg is in scope

Two conflicting designs:
- whole context design. this one is kind of hard to do curried
- curried design. this one we could do by eliding next.

curried design feels the simplest, where we pass the
context through the entire list.

"substitution" operation.
just apply the argument to every assertion in the list
at each step.

::[ass₁, ::[ass₂, ass₃]]

feels like we should be able to index the context
and pop off a list.
but then, we need to know the argument types
ahead of time
which is mad complicated.

we should shortcut this with some cleverly designed logic.
FEELS like the π combiantor would have been very useful here.

fetches the 2nd argument
::[skip, ::[skip, id]]

This feels like we're sequencing these operations.

($ (id ∘ skip ∘ skip), arg)
= (id ∘ skip)

issue with this, again is we need the type of context elements.

BOOM ANOTHER IDEA.

what if we STORE the types next to the arguments as we go?

then, skip has the type and argument already filled in.

for example, if the next step is just ::[id, stuff],

then when we apply,
($ ::[t_arg, arg_val], (id m n))
= ($ id m n, t_arg, arg_val)

but what about at the first assertion?
we don't know the type of the argument.

how does the inductive step work?

t_in app produces our expected_type

α'


-/


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

/-
Sigma term substitution:

inside out or something?

id α = fun (x : α) => x
Sigma.mk α (fun (x : α) => x)


In Lean, sigma projection does implicit substitution.

the fun depends on the term α

(λ (x : A) => (N : B)) M = N[x := A]
(Sigma.mk M N[x := A]).snd = N[x := A]

(Σ (x : A), B x

(Σ (x : A), N x).snd = 

wait this seems vaguely interesting.


id α = fun (x : α) => x
Sigma.mk α (fun (x : α) => x)
Here, as well.

(fun (x : α) => x) is the substituted value.

In DCC,

::[α, id] (id _ _)
= (id _ _) id α
= id α = fun (x : α) => x


Sigma.mk α (
Sigma.mk 




id : ∀ (α : Type), α → α
s := (α : Type) × (fun (x : α) => x)
::[α, ::[Type, id]]



::[Type, id]

::[Type, id]

it would be REALLY NICE
if we could substitute in here.

::[α, ::[Type, id]] id
= id ::[Type, id] α
= ::[Type, id] α
= id Type α
-/
