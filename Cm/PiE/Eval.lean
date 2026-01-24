import Cm.PiE.Ast

open Expr

/-
apply just turns a list into an app.
-/

/-
For testing purposes.
This mirrors is_step_once exactly.
-/
def do_step_apply : Expr → Except Error Expr
  /-
    nil can downgrade a dependent type to a nondependent type.
    this is how nondependent pairs are derived from sigmas.
    ((x : (α : Ty m)) × (β : Ty n)) = ((x : α) × (.nil m n α β))
  -/
  | ::[.nil _m _n, _α, β, _x] => pure β
  | ::[.id _o, _α, x] => pure x
  | ::[const _o _p, _α, _β, c, _x] => pure <| c
  | ::[both o p q, α, β, γ, ::[f, g], x] => -- TODO: not sure whether to nest ::[f, g] here, or leave flat
    pure <| ::[f$ (apply o p) ::[α, β, f, x], f$ (apply o q) ::[α, γ, g, x]]
  | ::[π o p q r, α, β, γ, δ, ::[fx, fxs], ::[x, xs]] =>
    pure <| ::[f$ (apply o q) ::[α, γ, fx, x], f$ (apply p r) ::[β, δ, fxs, xs]]
  | ::[eq o p, α, β, ::[fn_yes, fn_no], a, b] =>
    if a == b then
      pure <| f$ (apply o p) ::[α, β, fn_yes, a]
    else
      pure <| f$ (apply o p) ::[α, β, fn_no, b]
  | e => .error <| .no_rule e

def run (e : Expr) : Except Error Expr := do
  match e with
  | f$ a@(apply _m _n) ::[fα, fβ, f, x] => do
    let eval_both : Except Error Expr := do
      let f' ← run f
      let x' ← run x
      pure <| f$ a ::[fα, fβ, f', x']
    let eval_arg_first : Except Error Expr := do
      let x' ← run x
      pure <| f$ a ::[fα, fβ, f, x']
    let eval_f_first : Except Error Expr := do
      let f' ← run f
      pure <| f$ a ::[fα, fβ, f', x]
    let step_whole : Except Error Expr := do
      do_step_apply <| ::[f, x]
    let push_arg : Except Error Expr := do
      ((Expr.push f x).map Except.ok).getD (.error <| .stuck e)
        >>= (fun f' => pure <| f$ a ::[fα, fβ, f'])

    eval_f_first <|> eval_both <|> eval_arg_first <|> step_whole <|> push_arg
  | :: x xs => (do
    let x' ← run x
    let xs' ← run xs
    pure <| :: x' xs') <|> (do
    let xs' ← run xs
    pure <| :: x xs') <|> (do
    let x' ← run x
    pure <| :: x' xs)
  | e => .error <| .stuck e

def try_step_n (n : ℕ) (e : Expr) : Except Error Expr :=
  match n with
  | .zero => pure e
  | .succ n =>
    match run e with
    | .ok e' => try_step_n n e' <|> (pure e')
    | .error e => .error e

namespace test_curry

example : try_step_n 200 (f$ (apply 0 0) ::[Ty 0, Ty 0, .id 0, Ty 1, Ty 0]) = try_step_n 200 (f$ (apply 0 0) ::[Ty 0, Ty 0, ::[.id 0, Ty 1], Ty 0]) := rfl

end test_curry

namespace hole


end hole

