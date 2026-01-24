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
  -- this apply rule allows treating a list as if it were a function application
  | ::[::[.id _o, _α], x] => pure x
  | e@::[::[(const _o _p), _α, _β], _c]
  | e@::[::[(const' _o _p), _α, _β], _c] => pure e
  | ::[::[::[(const _o _p), _α, _β], c], _x]
  | ::[::[::[(const' _o _p), _α, _β], c], _x] => pure c
  | ::[::[::[(both o p q), α, β, γ], ::[f, g]], x] =>
    pure <| ::[mk_apply o p α β ::[f, x], mk_apply o q α γ ::[g, x]]
  | ::[::[::[(both' o p q), α, β, γ], ::[f, g]], x] =>
    -- both' is nondependent, so β' = (mk_quote p.succ o (Ty p) α β)
    let fβ := mk_quote p.succ o (Ty p) α β
    let gβ := mk_quote q.succ o (Ty q) α γ

    pure <| ::[mk_apply o p.succ α fβ ::[f, x], mk_apply o q.succ α gβ ::[g, x]]
  | ::[::[::[π _o _p _q _r, _α, _β, _γ, _δ], ::[fx, fxs]], ::[x, xs]] =>
    pure <| ::[f$ fx x, f$ fxs xs]
  | ::[::[::[::[eq _o _p, _α, _β], fn_yes, fn_no], a], b] =>
    if a == b then
      pure <| f$ fn_yes a
    else
      pure <| f$ fn_no b
  | e => .error <| .no_rule e

def run (e : Expr) : Except Error Expr := do
  match e with
  | f$ a@(f$ (f$ (apply _m _n) _fα) _fβ) ::[f, x] => do
    let eval_both : Except Error Expr := do
      let f' ← run f
      let x' ← run x
      pure <| f$ a ::[f', x']
    let eval_arg_first : Except Error Expr := do
      let x' ← run x
      pure <| f$ a ::[f, x']
    let eval_f_first : Except Error Expr := do
      let f' ← run f
      pure <| f$ a ::[f', x]
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
  | e => .error <| .stuck e

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
def quote?_n (n : ℕ) : Expr → Expr :=
  (List.replicate n const?₀).foldr (fun e acc => ::[e, acc])

def both? (f g : Expr) (α : Option Expr := .none) (m : Option Level := .none) : Expr :=
  ::[::[both' (m.getD 0) 0 0, (α.getD .hole), ?, ?], ::[f, g]]
def both?₁ (α f g : Expr) (m : Option Level := .none) : Expr := ::[::[both' (m.getD 0) 0 0, α, ?, ?], ::[f, g]]
def both?₀ (α : Option Expr := .none) (m : Option Level := .none) : Expr :=
  ::[both' (m.getD 0) 0 0
  , (α.getD .hole)
  , ? , ?]

def apply?₀ (α β : Option Expr := .none) (m n : Option Level := .none) : Expr :=
  f$ (f$ (apply (m.getD 0) (n.getD 0)) (α.getD ?)) (β.getD ?)

def id? (α : Option Expr := .none) (m : Option Level := .none) := ::[id (m.getD 0), α.getD .hole]

/-
curried n * quote
:: both (:: (quote const) id)
-/
def quote?_n₀ (n : ℕ) (α : Option Expr := .none) (m : Option Level := .none) : Expr :=
  (List.replicate n (quote const?₀)).foldr (fun e acc => both? e acc) (@id? α m)

-- for n λ binders. this expands into n * (n * const(both))
-- this "binds" n binders deep by injecting n future both's
def both?_n (n : ℕ) (f g : Expr) (α : Option Expr := .none) (m : Option Level := .none) : Expr :=
  ((List.range n).tail.map (fun n => quote?_n n both?₀)).foldr
    (fun e acc => both? e acc) (both? (f := f) (g := g) (α := α) (m := m))

example : try_step_n 200 (f$ apply?₀ ::[(f$ apply?₀ ::[(f$ apply?₀ ::[quote?_n 3 (Ty 0), (Ty 0)]), Ty 0]), Ty 0])  = (.ok (Ty 0)) := rfl

/-
  α → β
-/
def imp? (α β : Expr) : Expr := ::[quote α, quote β]

/-
id : ∀ (α : Type), α → α
-/
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

example : Expr.tail! <$> try_step_n 500 (f$ apply?₀ ::[id.type_with_holes 0, Ty 0])
  >>= (fun (e : Expr) => try_step_n 500 (f$ apply?₀ ::[e, Ty 100])) = (.ok (::[Ty 0, Ty 0])) := rfl

/-
Type inference for filling in holes in expr types.
-/
def infer_holes : Expr → Except Error Expr
  |

end hole

example : try_step_n 100 (f$ (f$ (f$ (apply 0 0) nil) nil) ::[::[id 2, Ty 1], Ty 0]) = (.ok <| Ty 0) := rfl

example : try_step_n 100 (f$ (f$ (f$ (apply 0 0) nil) nil) ::[::[::[const 2 2, Ty 1, Ty 1], Ty 0], Ty 0]) = (.ok <| Ty 0) := rfl
