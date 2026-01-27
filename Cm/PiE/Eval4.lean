import Cm.PiE.Ast

open Expr

/-
Notes:
feels like our evaluation rule for snd is potentially perfect.
.snd.fst works as intended.
once we reach the end of the list, we apply all.

and we have a way to check input arguments, since we can
manually do .snd.fst.snd.

WAIT. snd should not recurse snd.
-/

def do_step_apply (e : Expr) (with_logs : Bool := False) : Except Error Expr := do
  if with_logs then
    dbg_trace e

  match e with
  | ($ (fst _m _n), _α, _β, _γ, fn, ::[a, _b]) => pure ($ fn, a)
  | ($ (snd _m _n), _α, _β, _γ, fn, ::[::[x, xs], ::[f, nil]]) =>
    pure <| ($ ($ fn, ::[xs, ::[f, nil]]), x)
  | ($ (snd _m _n), _α, _β, _γ, fn, ::[x, ::[f, nil]]) =>
    pure <| ($ fn, f, x)
  | ($ (snd _m _n), _α, _β, _γ, fn, ::[x, ::[a, f]]) =>
    pure <| ($ fn, ::[::[x, a], f])
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
We assume that application types produce sigma outputs
where .snd.fst =
To type-check an application ($ (f : t), (x : α)):


-/

/-
Current .snd is not particularly powerful,
but we may be able to mimick substitution in types with it.

::[x, f].snd = (.app f.snd x)

::[x, t_f].snd.fst represents the expected type of x

.snd should produce a sigma with the head value being the expected type.
further types will need the entire context.
if we had partial application for cons, that would help a lot, since
then we could just append α to ::[Ty m, α]

a partially applied cons would be stupid powerful,
though we can probably simulate it with π,

t_id = ::[($ cons, Ty m), ::[nil m, id m.succ]]

t_id = ::[($ cons, Ty m), ::[::[Ty m, id m.succ]

x part receives ::[α, ($ const' m.succ.succ m.succ, Ty m.succ, Ty m, Ty m), nil],
then ::[x, α, ($ const' m.succ.succ m.succ, Ty m.succ, Ty m, Ty m), nil]

Idea:
type of lists is kinda determined by fst and snd,
I would like to be able to treat this context as just a list and select the second element.

snd ∘ snd

another idea:
perhaps we can make snd more powerful?

snd gets like a fold argument.

do we even need α β arguments if f has a type?
f should include the type, hmmmmm.

does this mean we can downgrade to nondependent pairs?
since there is no actual application going on.

snd id ::[x, ::[f, nil]]

this should produce ($ f, x)

current rule looks good.

fst f ::[a, b] = (f a)

this FEELS like it should simplify the types ngl.
we might not need the types of fst and snd to be very dependent.

fst : ∀ (α : Type) (β : Type)

snd' 

snd' (snd' fst) ::[x, α, stuff] = α

snd fold argument works after substitution.

what is the advantage of this?

snd' fn ::[x, ::[::[a, b], f]] = ::[($ fn, ::[x, a, b]), f]

snd' fn ::[x, ::[::[a, b], f]] = ::[($ fn, ::[x, a, b]), f]

snd' id ::[x, (::[::[a, b], f] : β)] = ::[::[x, a, b], f]

f : ∀ (l : (α × β.fst)

this is potentially even nicer,
since we don't have to explicitly type ::[x, α, stuff] as strictly.

snd' f ::[a, ::[b, c]] = f ::[::[a, b], c]

this simplifies the type a lot.

this is kind of nice.
it would be nice if we could find a way to merge dependent and nondependent pairs.

it would be really nice if we could move the type dependency to snd.
snd says how to interpret these two things.

we basically want to "substitute".
I think the current rules are fine for this.

our selector is what to do once we've reached a nil list?



snd : ∀ (α : Type) (β : Type) (γ : ∀ (x : α), β x → Type) (f : ∀ (x : α) (y : β x), γ x y) (l : (α × β)),
  γ l.fst l.snd

bring π back? this is a combination of both.

am I stupid?

feels like we could simplify both now.

snd fn ::[x, ::[::[a, b], f]] = fn ::[::[x, a, b], f]

this seems kind of whack. seems like a potential infinite loop.

can we recover substitution?

sub ::[x, ::[::[a, b], f]] = 

snd' : ∀ (α : Type) (β : α → Type) (γ : ∀ (x : α) (y : β x), Type) (f : l) (l : (× α β)), γ l.fst (β l.fst)

id : ∀ (α : Type), α → α

::[α, t_id].snd (fst ∘ snd)

question:
can we defer substitution with this?

snd fn ::[a, ::[::[b, c], f]] = ($ fn, a, ::[::[b, c], f])

snd cons ::[a, ::[::[b, c], f]] = ($ cons, a, ::[::[b, c], f])

this feels like a nice identity.

uncurry, we receive y ::[x, f]

snd y ::[x, f] = ($ y x f)

C combinator?

snd y ::[x, f] = ($ y x f)

can we use fst inside?

($ fst, f, ::[a, b]) = ($ f, a)

oh wait interesting.
this is where we can make it work like before.

snd should do some kind of substitution.

does fn tell us how to substitute?

snd should absolutely destroy a.

snd f ::[a, b] =

how, ideally, do I want to use this for id?

id : ∀ (α : Type), α → α

I feel like ideally, snd should just do application as substitution.

snd (id α) ::[x, f] = (f x)

equations:

snd f ::[a, b] = f b a

this is like the C combinator.

and, we can recover the original list, I think.
this doesn't matter.

snd f ::[a, b] = f b a

id : ∀ (α : Type), α → α

::[α, t_id].snd

what do we plug into snd to do substitution?
if we plug in id, then we get
simple application.
for substitution, we probably want

fst f ::[a, b] = f a b

whoah that is whack.

interesting.

to do substitution with snd:

we get the function first, b.

this contains our nested context.

fst fn ::[x, f] = fn x f

the nested sigma is kind of an interesting case.
how do we know when to stop?

snd fn ::[x, f] = fn f x

snd cons ::[x, ::[y, f]] = cons ::[y, f] x = ::[::[y, f], x]

nested snd looks very promising
wait this is literally it.

snd (snd cons) ::[y, ::[x, f]]
  = (snd cons) ::[x, f] y
  = cons f x y

snd (snd id) ::[y, ::[x, f]]
  = (snd id) ::[x, f] y
  = (id f x) y

wait that is so cool.

f ::[ctx, out] x

we can nest snd and fst nicely.

f = cons

::[($ cons 

snd (fst y) ::[x, f] = ($ ($ fst, y, 

snd ::[y, ::[x, f]]

how do we recurse here reliably?

fn receives a and acts on the second element.
INTERESTING.



snd fn ::[

in this version, we don't actually apply inside the sigma.


f takes in a, 

question:
since we're deferring applications to f, can we actually avoid
dependent sigmas in snd altogether?

snd : ∀ (α : Type) (β : Type) (f : ∀ (l : (α × β)

::[(b : α), (c] : (⨯ 
snd' f ::[a, ::[b, c]] = 
-/

def id.type (m : Level) : Expr :=
  ::[::[($ const' m.succ.succ m.succ, Ty m.succ, Ty m, Ty m), nil]
   , ::[($ id m, (Ty 0)), ::[($ id m.succ, (Ty m)), nil], nil]]

notation "snd!" => (fun e => ($ (snd 0 0), Ty 0, Ty 0, ($ id 0, Ty 0), e))
notation "fst!" => (fun e => ($ (fst 0 0), Ty 0, Ty 0, ($ id 0, Ty 0), e))

example : try_step_n 100 (snd! ∘ fst! ∘ snd! <| ::[(Ty 1), id.type 2]) = (.ok (Ty 2)) := rfl

#eval try_step_n 100 (snd! <| ::[(Ty 0), (snd! ∘ snd! <| ::[(Ty 1), id.type 2])])

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
