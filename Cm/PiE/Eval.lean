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
  | ::[_x, α, .nil _m] => pure α
  | ::[x, _α, .id _o] => pure x
  | ::[_x, c, _β, _α, const _o _p] => pure <| c
  | ::[x, g, f, γ, β, α, both o p q] => -- TODO: not sure whether to nest ::[f, g] here, or leave flat
    pure <| ::[($ (snd o p), α, β, ::[x, f]), ($ (snd o q), α, γ, ::[x, g])]
  | ::[b, a, fn_no, fn_yes, β, α, eq o p] =>
    if a == b then
      pure <| ($ (snd o p), α, β, ::[a, fn_yes])
    else
      pure <| ($ (snd o p), α, β, ::[b, fn_no])
  | f$ ::[x, f] arg => pure ::[arg, x, f]
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

def app? (f : Level → Level → Expr) (e : Expr) := ($ (f 0 0), TSorry, TSorry, e)

#eval try_step_n 100 (app? snd ::[(Ty 1), ::[(Ty 2), .id 3]])

end hole
