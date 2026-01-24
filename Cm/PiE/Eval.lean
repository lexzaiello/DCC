import Cm.PiE.Ast

open Expr

/-
For testing purposes.
This mirrors is_step_once exactly.
-/
def do_step_apply : Expr → Except Error Expr
  | ::[::[.id _o, _α], x] => pure x
  | ::[::[::[(const _o _p), _α, _β], c], _x]
  | ::[::[::[(const' _o _p), _α, _β], c], _x] => pure c
  | ::[::[::[(both o p q), α, β, γ], ::[f, g]], x]
  | ::[::[::[(both' o p q), α, β, γ], ::[f, g]], x] =>
    pure <| ::[f$ (f$ (f$ (apply o p) α) β) ::[f, x], f$ (f$ (f$ (apply o q) α) γ) ::[g, x]]
  | ::[::[::[π o p q r, α, β, γ, δ], ::[fx, fxs]], ::[x, xs]] =>
    pure <| ::[f$ (f$ (f$ (apply o q) α) γ) ::[fx, x], f$ (f$ (f$ (apply p r) β) δ) ::[fxs, xs]]
  | ::[::[::[::[eq o p, α, β], fn_yes, fn_no], a], b] =>
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
      do_step_apply <| ::[f, x]

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

namespace hole

def quote (e : Expr) : Expr := ::[::[const' 0 0, ?, ?], e]
def quote?₁ (α e : Expr) (m : Option Level := .none) : Expr := ::[::[const' (m.getD 0) 0, α, ?], e]

def const?₀ : Expr := ::[const' 0 0, ?, ?]
def const?₁ (α : Expr) (m : Option Level := .none) : Expr := ::[const' (m.getD 0) 0, α, ?]

def both? (f g : Expr) : Expr := ::[::[both' 0 0 0, ?, ?, ?], ::[f, g]]
def both?₁ (α f g : Expr) (m : Option Level := .none) : Expr := ::[::[both' (m.getD 0) 0 0, α, ?, ?], ::[f, g]]

def both?₀ : Expr := ::[both' 0 0 0, ?, ?, ?]

notation "f?" => (fun f x => (f$ (f$ (f$ (apply 0 0) ?) ?) ::[f, x]))

def id.type_with_holes (m : Level) : Expr :=
  both?
    (f := (quote?₁ (Ty m.succ) (Ty m) (m := m.succ.succ)))
    (g := (both?₁
      (α := (Ty m))
      (f := (quote?₁ (Ty m) both?₀ (m := m.succ)))
      (g := (both?₁
        (α := (Ty m))
        (f := (const?₁ (α := Ty m) (m := m.succ)))
        (g := (const?₁ (α := Ty m) (m := m.succ)))
        (m := m.succ)))
      (m := m.succ)))

#eval Expr.tail! <$> try_step_n 500 (f? (id.type_with_holes 0) (Ty 0))

/-
Type inference for filling in holes in expr types.
-/
def infer_holes : Expr → Except Error Expr
  |

end hole

example : try_step_n 100 (f$ (f$ (f$ (apply 0 0) nil) nil) ::[::[id 2, Ty 1], Ty 0]) = (.ok <| Ty 0) := rfl

example : try_step_n 100 (f$ (f$ (f$ (apply 0 0) nil) nil) ::[::[::[const 2 2, Ty 1, Ty 1], Ty 0], Ty 0]) = (.ok <| Ty 0) := rfl
