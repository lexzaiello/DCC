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
  | ($ (fst _m _n), _α, _β, ::[a, _b]) => pure a
  | ($ (snd m n), α, β, ::[::[x, xs], ::[f, nil]]) =>
    pure <| ($ ($ (snd m n), α, β, ::[xs, ::[f, nil]]), x)
  | ($ (snd _m _n), _α, _β, ::[x, ::[f, nil]]) =>
    pure <| ($ f, x)
  | ($ (snd _m _n), _α, _β, ::[x, ::[a, f]]) =>
    pure <| ::[::[x, a], f]
  | ($ (.id _o), _α, x) => pure x
  | ($ (.const _o _p), _α, _β, c, _x)
  | ($ (.const' _o _p), _α, _β, c, _x) => pure <| c
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

example : try_step_n 100 ($ (id 2), (Ty 1), (Ty 0)) = (.ok (Ty 0)) := rfl

example : try_step_n 100 ($ (snd 0 0), (Ty 0), (Ty 0), ::[Ty 0, ::[Ty 1, id 2, nil]])
  >>= (fun c => try_step_n 100 ($ (snd 0 0), (Ty 0), (Ty 0), c)) = (.ok (Ty 0)) := rfl

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

snd' (snd' fst) ::[x, α, stuff] = α


-/

def id.type (m : Level) : Expr :=
  ::[::[($ const' m.succ.succ m.succ, Ty m.succ, Ty m, Ty m), nil]
   , ::[($ id m, (Ty 0)), ::[($ id m.succ, (Ty m)), nil], nil]]

notation "snd!" => (fun e => ($ (snd 0 0), Ty 0, Ty 0, e))
notation "fst!" => (fun e => ($ (fst 0 0), Ty 0, Ty 0, e))

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
