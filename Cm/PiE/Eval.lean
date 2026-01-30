import Cm.PiE.Ast

open Expr

/-
snd rule feels kinda wrong ngl.

::[x, f] fn = ($ fn, f, x)

feels like this should actually be

($ ($ f, fn), x)

::[y, ::[x, f]] id
= ($ ($ ::[x, f], id) y)
=

× α β. this is something where projection produces

old snd
snd fn ::[x, f] = ($ fn, f, x)

So our current evaluation rule should be fine.
It's just whether we can recurse or not.

But, this answers our sigma type question, pretty much.

::[(x : α), (f : β)] : {γ : α → β → Type} (∀ (f : β) (x : α), γ f x)

I think we can also do sigma fst.

::[x, f] (const' ...)
= (const' ...) f x = x. this is right

sigma snd is just id, since that's application.
-/

#eval repr ::[($ symbol "f", symbol "x"), ($ symbol "g", symbol "x")]

/-
Expr.app
  (.app .cons (.app f x))
  (.app g x)
-/

inductive is_step : Expr → Expr → Prop
  | sapp   : is_step ($ ::[x, f], fn) ($ fn, f, x)
  | nil    : is_step ($ (nil _o), α, _x) α
  | id     : is_step ($ (.id _o), _α, x) x
  | const  : is_step ($ (.const _o _p), _α, _β, c, _x) c
  | const' : is_step ($ (.const' _o _p), _α, _β, c, _x) c
  | both   : is_step ($ (.both _o _p _q), _α, _β, _γ, f, g, x) ::[($ f, x), ($ g, x)]
  | eq_yes : a == b → is_step ($ (.eq _o _p), _α, _β, fn_yes, fn_no, a, b)
    (.app fn_yes a)
  | eq_no  : a ≠ b → is_step ($ (.eq _o _p), _α, _β, fn_yes, fn_no, a, b)
    (.app fn_no b)
  | left   : is_step f f'
    → is_step ($ f, x) ($ f', x)
  | right  : is_step x x'
    → is_step ($ f, x) ($ f, x')

#eval repr (::[symbol "a", symbol "b"])

def do_step_apply (e : Expr) (with_logs : Bool := False) : Except Error Expr := do
  if with_logs then
    dbg_trace e

  match e with
  | ($ ::[x, f], fn) => pure ($ fn, f, x)
  | ($ (nil _o), α, _x) => pure α
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

#eval try_step_n 100 ($ ::[(symbol "x"), (symbol "f")], ($ (Expr.id 0), (.symbol "α")))

example : try_step_n 100 ($ (id 2), (Ty 1), (Ty 0)) = (.ok (Ty 0)) := rfl

/-
currying:
snd id = ($ ::[x, f] (id ?)) = ($ f, x)
-/

example : try_step_n 100 ($ ::[(symbol "self"), ($ id 0, (symbol "sorry"))], ($ (id 0), (symbol "sorry")))
   = (.ok (symbol "self")) := rfl

/-
Tricky thing with writing assertions is that our combinators are 
-/

def id.type (m : Level) : Expr :=
  ::[($ nil m.succ, (Ty m)), nil m, nil m]

