import Cm.PiE.Ast

open Expr

/-
questions on prod.snd.

it feels like prod.snd shouldn't be as eagerly normalizing here.

snd is a function actually, so this kind of makes sense.
no reason we can't do this.

this looks fine.

some tests to run:

nested app.

| f$ ::[x, f] arg

this rule feels derivable.

::[(x : α), (xs : β x)].snd "substitutes" x in, by some vague, unknown mechanism.
the most logical conclusion is that

::[x, ::[y, ys]].snd = ::[x,

Question: can we replace f$ ::[x, f] arg with ::[arg, x, f]?

if xs is also a sigma, then how exactly is it dependent on x?

::[(x : α), ::[(y : Ty m), ::[(z : Ty n), nil]]] nil delimiter closes the loop?

BUT, this is also a (×' α β) type.
another question. why in god's name does ⨯' exist?

question: can we derive the type of a product without funky (⨯' α β)?
could this potentially make our cons's even more flexible?

for fst, though, we need some way to capture the head, and if we don't
do it by construction with (×' α β), then what?

fst already get α and β

the main question is:

(a : ?) × β x, here for example,
what if we want a to depent on something above it as well?
how does that work?

the head element of a sigma should be able to "leak" its dependency,
kind of like a function argument.

::[(y : Ty m), ::[(z : Ty n), nil]]
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
id : ∀ (α : Type), α → α
id : ::[
-/

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
(id id) x = x

::[x, ::[?, id 0], ::[?, id 0]]
-/
example : try_step_n 100 (app? snd ::[(symbol "x"), ::[?, id 0], ::[?, id 0]]) = (.ok (symbol "x")) := rfl

/-
g ∘ f. ezpz.

g ∘ f
-/
example : try_step_n 200 (app? snd ::[(symbol "x"), ::[symbol "f", symbol "g"]])  =
  (.ok (f$ ((symbol "g")) ((f$ ((symbol "f")) ((symbol "x")))))) := rfl

example : try_step_n 100 (app? snd ::[(Ty 1), ::[(Ty 2), .id 3]]) = (.ok <| Ty 1) := rfl

example : try_step_n 100 (app? snd ::[(Ty 0), ::[(Ty 1), .nil 2]]) = (.ok (Ty 1)) := rfl

end hole
