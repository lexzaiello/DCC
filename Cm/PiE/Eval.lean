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

namespace hole

def TSorry : Expr := .unit

/-
id.{[m]} : (::[::[(Ty m), nil.{[m.succ]}], ::[nil.{[m]} ∘ Prod.fst, Prod.snd]])
-/
--def id.type_with_hole (m : Level) : Expr :=
  

def app? (f : Level → Level → Expr) (e : Expr) := ($ (f 0 0), TSorry, TSorry, e)

example : try_step_n 200 (app? snd ::[(symbol "x"), ::[symbol "f", symbol "g"]])  = (.ok (f$ ((symbol "g")) ((f$ ((symbol "f")) ((symbol "x")))))) := rfl

example : try_step_n 100 (app? snd ::[(Ty 1), ::[(Ty 2), .id 3]]) = (.ok <| Ty 1) := rfl

example : try_step_n 100 (app? snd ::[(Ty 0), ::[(Ty 1), .nil 2]]) = (.ok (Ty 1)) := rfl

end hole
