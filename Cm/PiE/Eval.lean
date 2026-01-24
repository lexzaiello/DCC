import Cm.PiE.Ast

open Expr

/-
apply just turns a list into an app.
-/

/-
For testing purposes.
This mirrors is_step_once exactly.

TODO: applying arg onto a ::[x, f] feels like it should shortcut to
::[::[arg, x], f]

we will need to redo all our eval rules with this new ordering.

::[x, α, id m]

feels like snd should just be (f$ f x)?

nil m α x = α

TODO: it feels like snd shouldn't be applying as eagler.
what about the list case? did we handle this already or something?

listpill:
- can we remove apps from inside snd?
it's unclear when we will see an app or a cons.
I feel like we should default to cons and convert if necessary.

::[f, ::[t_in, t_out]]

what if t_in is itself dependent?
this seeems not allowed.

don't normalize cons snd projection.

($ snd ::[x, ::[t_in, t_out]]) = ::[

id.{[m]} : (::[::[Ty m, ::[Ty m, nil.{[m.succ]}]], ::[(id, ::[Ty m, id m.succ]]]])
::[α, ::[::[Ty m, ::[Ty m, nil.{[m.succ]}]], ::[(id, ::[Ty m, id m.succ]]]]]

it feels like the default behavior should be "substitution."
that is, just extending the list.

so, again, when does application happen?

cons is not actually application, it just kind of behaves like it due to normalizing .snd
component.

so, we need some way to induce

assuming we are using app strategy, not cons:
::[α, ::[::[Ty m, ::[Ty m, nil.{[m.succ]}]], ::[(id, ::[Ty m, id m.succ]]]]]

::[(x : α), (xs : β x)] : (⨯' α β)

it feels like it shoul be possible to partially apply cons.

Potential solutions to our woes, and concerns:
- feels strange that snd is actually applying. or maybe it's not strange?
  - if it's not strange, then how exactly are we substituting? we're not. I think it's just by virtue of prepending.
- did I do the order wrong in fst and snd? probably not. probably not. examples work fine.

how should snd work?
just apply fst to the second component.
pretty straightforward.

seeems fine.

I think the answer is probably we need partial application of cons,
or some way to form new lists inside the type.

what about nested sigmas?

what does it mean for a sigma to be nested? how does that work?

::[(x : α), (? : β x)]

sigma doesn't really do anything special,
so we cannot rely on the ? inner value being a nested sigma, ngl.

what I thought this would do:


f = ::[::[Ty m, ::[Ty m, nil.{[m.succ]}]], ::[(id, ::[Ty m, id m.succ]]]], x = α
::[α, ::[::[Ty m, ::[Ty m, nil.{[m.succ]}]], ::[(id, ::[Ty m, id m.succ]]]]].snd
  = (f$ ::[::[Ty m, ::[Ty m, nil.{[m.succ]}]], ::[(id, ::[Ty m, id m.succ]]]] x), f = f above, x = x
  = f$ (::[x, f] matched on f, so [::[Ty m, ::[Ty m, nil.{[m.succ]}]], ::[(id, ::[Ty m, id m.succ]]]]) arg
  = ($ ::[(id, ::[Ty m, id m.succ]]], ::[Ty m, ::[Ty m, nil.{[m.succ]}]], x), recurse list application
  = ($ 
  = ($ ::[(id, ::[Ty m, id m.succ]]], -- 19 lines below, argument insertion, I think
-/
def do_step_apply : Expr → Except Error Expr
  | ($ (fst _m _n), _α, _β, ::[a, _b]) => pure a
  | ($ (snd _m _n), _α, _β, ::[x, f]) => pure (f$ f x)
  /-
    nil can downgrade a dependent type to a nondependent type.
    this is how nondependent pairs are derived from sigmas.
  -/
  | ($ (.nil _m), α, _x) => pure α
  | ($ (.id _o), _α, x) => pure x
  | ($ (.const _o _p), _α, _β, c, _x) => pure <| c
  | ($ (.both o p q), α, β, γ, f, g, x) => -- TODO: not sure whether to nest ::[f, g] here, or leave flat
    pure <| ::[($ (snd o p), α, β, ::[x, f]), ($ (snd o q), α, γ, ::[x, g])]
  | ($ (.eq o p), α, β, fn_yes, fn_no, a, b) =>
    if a == b then
      pure <| ($ (snd o p), α, β, ::[a, fn_yes])
    else
      pure <| ($ (snd o p), α, β, ::[b, fn_no])
  | f$ ::[x, f] arg => pure ($ f, x, arg)
  | e => .error <| .no_rule e

/-
(×' α (β : α → Type))
-/

def run (e : Expr) : Except Error Expr := do
  do_step_apply e <|> (match e with
  | :: x xs => (do
    let x' ← run x
    let xs' ← run xs
    pure <| :: x' xs') <|> (do
    let xs' ← run xs
    pure <| :: x xs') <|> (do
    let x' ← run x
    pure <| :: x' xs)
  | e => .error <| .stuck e)

def try_step_n (n : ℕ) (e : Expr) : Except Error Expr :=
  match n with
  | .zero => pure e
  | .succ n =>
    match run e with
    | .ok e' => try_step_n n e' <|> (pure e')
    | .error e => .error e

/-
nil.{[m]} : ∀ (α : Type m), α → Ty m
nil (Ty m) α = Ty m
out receives ::[α, Ty m, nil.{{m.succ]}]
same pattern
::[nil.{[m]}, ::[::[(fst m ? ? ?), nil.{{m]}], Prod.snd]]

We also need to feed Prod.snd into here.

we can basically nil / lift the term mapping from (x : α) → (β x)
to get the corresponding type.

app? ::[Ty m, ::[nil.{[m]}, ::[::[(fst m ? ? ?), nil.{{m]}], Prod.snd]]

to check t_in: ::[x, t_f].snd.fst.snd
this normalizes t_in, but this could just be like a simple pair,
not a dependent pair.
-/
/-def nil.type (m : Level) : Expr :=
  let t_α := ::[Ty m, nil.{[m.succ]}]
  ::[t_α, ::[ (Ty m)
  sorry-/

/-
psuedo-code
inner = ::[(id, ::[Ty m, id m.succ]]]
id.{[m]} : (::[::[Ty m, ::[Ty m, nil.{[m.succ]}]], ::[(id, ::[Ty m, id m.succ]]]])

::[Ty m, nil.{[m.succ]}] : (Ty m → 
inner receives (l = ::[α, Ty m, ::[Ty m, nil.{[m.succ]}]])
l : ((Ty m) × ((nil.{{m.succ.succ]} (Ty m.succ)) × (
($ nil.{[m.succ]}, Ty m) : Ty m → Ty m.succ
-/

/-def id.type (m : Level) : Expr :=
  -- insert α before Ty m-/

/-
id.{[m]} : (::[::[(Ty m), nil.{[m.succ]}], ::[::[(Prod.fst ? ?, nil.{[m]}], Prod.snd]])
-/
/-
def id.type (m : Level) : Expr :=
  let t_α := ::[(Ty m), (nil m.succ)]
  -- prod.fst ::[α, ...], β = ?
  -- α × (β : α → Type)
  -- t_x receives ::[\alpha, ::[Ty m, nil.{{m.succ]}]]
  -- nil.{[m]} : ∀ (α : Type m), α → Ty m
  -- β : (const' ? ? ($ ×', (Ty m.succ), t_nil
  let α_ret := ::[::[::[(Ty m) (Prod.fst m.succ 0) ? ?, nil m], Prod.snd]]
  sorry-/

namespace hole

def TSorry : Expr := .unit

def app? (f : Level → Level → Expr) (e : Expr) := ($ (f 0 0), TSorry, TSorry, e)

def quote_n? : ℕ → Expr → Expr
  | .zero, e => e
  | .succ n, e => ::[quote_n? n e, ?, ?, const 0 0]

/-
Currying.
We can apply apps as normal, but for ::[x, f] calls, we need to Prod.snd first.
-/
example : try_step_n 100 ($ (const 0 0), ?, ?, (symbol "a"), (symbol "discard")) = (.ok (symbol "a")) := rfl

example : (try_step_n 100 <|
  app? snd ::[(symbol "discard"), (symbol "a"), ?, ?, (const 0 0)]) = (.ok (symbol "a")) := rfl

example : try_step_n 100 ::[
  (symbol "discard")
  , (symbol "a")
  , ?
  , ?
  , (const 0 0)] = (.error <| .stuck (symbol "discard")) := rfl

/-
($
-/

#eval try_step_n 100 ($ quote_n? 1 (symbol "hi"), (symbol "discard₁"), (symbol "discard₂"), (symbol "discard₃"))

/-
need to make f something that evaluates.
we could just nest n quoted id's.
-/
def check (n : ℕ) (my_f : Expr := .symbol "f") : Except Error Bool := do
  let a ← try_step_n 100 <| ((List.range n).map (.symbol ∘ toString)).foldl .app my_f
  let b ← try_step_n 100 <| app? snd <| ((List.range n).map (.symbol ∘ toString)).foldr .cons my_f

  pure <| a == b

/-
g ∘ f. ezpz.

g ∘ f
-/
example : try_step_n 200 (app? snd ::[(symbol "x"), ::[symbol "f", symbol "g"]])  =
  (.ok (f$ ((symbol "g")) ((f$ ((symbol "f")) ((symbol "x")))))) := rfl

example : try_step_n 100 (app? snd ::[(Ty 1), ::[(Ty 2), .id 3]]) = (.ok <| Ty 1) := rfl

example : try_step_n 100 (app? snd ::[(Ty 0), ::[(Ty 1), .nil 2]]) = (.ok (Ty 1)) := rfl

end hole
