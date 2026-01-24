import Cm.PiE.Ast

open Expr

/-
For testing purposes.
This mirrors is_step_once exactly.
-/
def do_step : Expr → Except Error Expr
  | (f$ (f$ (f$ (apply _m _n) _fα) _fβ) ::[::[.id _o, _α], x]) => pure x
  | (f$ (f$ (f$ (apply _m _n) _fα) _fβ) ::[::[::[(const _o _p), _α, _β], c], _x]) => pure c
  | (f$ (f$ (f$ (apply _m _n) _fα) _fβ) ::[::[::[(both o p q), α, β, γ], ::[f, g]], x]) =>
    pure <| ::[f$ (f$ (f$ (apply o p) α) β)  ::[f, x], f$ (f$ (f$ (apply o q) α) γ) ::[g, x]]
  | (f$ (f$ (f$ (apply _m _n) _fα) _fβ) ::[::[::[π o p q r, α, β, γ, δ], ::[fx, fxs]], ::[x, xs]]) =>
    pure <| ::[f$ (f$ (f$ (apply o q) α) γ) ::[fx, x], f$ (f$ (f$ (apply p r) β) δ) ::[fxs, xs]]
  | (f$ (f$ (f$ (apply _m _n) _fα) _fβ) ::[::[::[::[eq o p, α, β], fn_yes, fn_no], a], b]) =>
    if a == b then
      pure <| (f$ (f$ (f$ (apply o p) α) β) ::[fn_yes, a])
    else
      pure <| (f$ (f$ (f$ (apply o p) α) β) ::[fn_no, b])
  | e => .error <| .no_rule e

def run (e : Expr) : Except Error Expr := do
  match e with
  | f$ (f$ (f$ (apply m n) fα) fβ) ::[f, x] => do
    let eval_both : Except Error Expr := do
      let f' ← run f
      let x' ← run x
      pure <| f$ (f$ (f$ (apply m n) fα) fβ) ::[f', x']
    let eval_arg_first : Except Error Expr := do
      let x' ← run x
      pure <| f$ (f$ (f$ (apply m n) fα) fβ) ::[f, x']
    let eval_f_first : Except Error Expr := do
      let f' ← run f
      pure <| f$ (f$ (f$ (apply m n) fα) fβ) ::[f', x]
    let step_whole : Except Error Expr := do
      do_step <| f$ (f$ (f$ (apply m n) fα) fβ) ::[f, x]

    eval_f_first <|> eval_both <|> eval_arg_first <|> step_whole
  | :: x xs => (do
    let x' ← run x
    let xs' ← run xs
    pure <| :: x' xs') <|> (do
    let xs' ← run xs
    pure <| :: x xs') <|> (do
    let x' ← run x
    pure <| :: x' xs)
  | e => (.error <| .no_rule e)

def try_step_n (n : ℕ) (e : Expr) : Except Error Expr :=
  match n with
  | .zero => pure e
  | .succ n =>
    match run e with
    | .ok e' => try_step_n n e' <|> (pure e')
    | .error e => .error e
