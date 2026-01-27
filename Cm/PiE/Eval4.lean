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
  | ($ (snd _m _n), _α, _β, _γ, fn, ::[x, f]) => pure ($ fn, f, x)
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
