import Mathlib.Data.Nat.Notation

/-
Automatic currying is quite nice, but I think we could
make it more obvious when it's required.

π could do this.
Can derive next from π.

π is like the opposite of both.

π x_case xs_case

π fn nil matches a list with only one thing in it.

The other issue is control flow.
Both handles one direction,
but what about the other?

We need a better way to achieve nesting.

With π, we replace read with id.

Append is fine.

An advantage with removing read and next is
that we no longer have to worry about pipelining.

Can we clean up both? Currently, π will just fail
if we don't have enough arguments.

I see no reason why we can't have an uncurried
and curried layer.

Since we have pattern matching now,
what do we do with the extra arguments?
Just get rid of them.

Idea:
- we denote values with no arguments as (:: val nil)

Another idea:
- both will only combine (:: _ nil) functions
with arbitrary parameters.

Currying will handle more than that.
-/

open Std (Format)
open Std (ToFormat)
open Std.ToFormat (format)

inductive Expr where
  | cons   : Expr
    → Expr
    → Expr
  | π      : Expr
    → Expr
    → Expr
  | id     : Expr
  | const  : Expr
  | both   : Expr
    → Expr
    → Expr
  | nil    : Expr
  | symbol : String
    → Expr
deriving Repr, BEq

inductive Error where
  | stuck      : Expr → Error
  | no_rule    : Expr → Error
  | cant_curry : Expr → Error

open Expr

def Expr.fmt (e : Expr) : Format :=
  match e with
  | .π a b => .paren <| "π " ++ (.paren a.fmt) ++ .line ++ (.paren b.fmt)
  | .cons (.cons a b) (.cons c d) =>
    ":: " ++ (.group <| .nest 2 <| (.paren (Expr.cons a b).fmt) ++ Format.line ++ (.paren (Expr.cons c d).fmt))
  | .cons (.cons a b) xs =>
    ":: " ++ (.group <| .nest 2 <| (.paren (Expr.cons a b).fmt) ++ Format.line ++ xs.fmt)
  | .cons x (.cons a b) =>
    ":: " ++ (.group <| .nest 2 <| x.fmt ++ Format.line ++ (.paren (Expr.cons a b).fmt))
  | .cons x xs =>
    ":: " ++ (.group <| .nest 2 <| x.fmt ++ Format.line ++ xs.fmt)
  | id => "id"
  | .const => "const"
  | .both f g => .paren ("both " ++ (.group <| .nest 2 <| (.paren f.fmt) ++ Format.line ++ (.paren g.fmt)))
  | .nil => "nil"
  | symbol s => .paren ("symbol " ++ ("\"" ++ s ++ "\""))

def Error.fmt : Error → Format
  | .stuck e => "got stuck evaluating: " ++ .line ++ e.fmt
  | .cant_curry e => "couldn't curry: " ++ .line ++ e.fmt
  | .no_rule e => "no rule to evaluate: " ++ .line ++ e.fmt

instance Expr.instToFormat : ToFormat Expr where
  format := Expr.fmt

instance Error.instToFormat : ToFormat Error where
  format := Error.fmt

instance Error.isntToString : ToString Error where
  toString := toString ∘ Error.fmt

instance Expr.instToString : ToString Expr where
  toString := toString ∘ Expr.fmt

notation "::" => Expr.cons

def Expr.push_back (val : Expr) : Expr → Option Expr
  | :: x nil => do pure <| :: x val
  | :: x xs => do pure <| :: x (← push_back val xs)
  | _ => .none

def mk_app (f x : Expr) : Option Expr :=
  Expr.push_back (:: x nil) f

def mk_app' (f : Option Expr) (x : Expr) : Option Expr := do
  Expr.push_back (:: x nil) (← f)

notation "f*" => mk_app'
notation "f$" => mk_app

example : Expr.push_back (:: (symbol "zero") nil) (:: (symbol "succ") nil) =
  (:: (symbol "succ") (:: (symbol "zero") nil)) := rfl

def step (e : Expr) (with_logs : Bool := false) : Except Error Expr := do
  if with_logs then
    dbg_trace e

  match e with
  | :: .id x => pure x
  | :: (π a nil) (:: x nil) => do
    pure <| :: (← step (:: a x)) nil
  | :: (π a b) (:: x xs) => do
    pure <| :: (← step (:: a x)) (← step (:: b xs))
  | :: (:: const x) _ => step x <|> (pure x)
  | :: (both f g) l =>
    let g' ← step (:: g l)
    match (← step (:: f l)) with
    | .cons .id (:: v nil)
    | :: v nil =>
      pure <| :: v (:: g' nil)
    | _ => .error <| .stuck e
  | :: f x => (do pure <| :: (← step f) (← step x))
    <|> (do pure <| :: f (← step x))
    <|> (do pure <| :: (← step f) x)
  | e => .error <| .no_rule e

def try_step_n (f : Expr → Except Error Expr) (n : ℕ) (e : Expr) (with_logs : Bool := false) : Except Error Expr := do
  if n = 0 then
    pure e
  else
    let e' ← f e
    (try_step_n f (n - 1) e' with_logs) <|> (pure e')

def do_step (f : Expr → Except Error Expr) (e : Expr) (with_logs : Bool := false):= try_step_n f 20 e with_logs

namespace church

/-
zero f x = x

Note: may considering changing the right branch
to keep x's arguments floating around?
Other branch would be
(:: zero (:: f (:: x (:: other
we can discard those.
-/
def zero : Expr :=
  π (:: const id) (π id nil)

/-
n(f, x)
-/
def succ.nfx : Expr :=
  π id (π id (π id nil))

/-
Selects f out of succ(n, f, x) as
(:: f nil)
-/
def succ.f : Expr :=
  π (:: const id) (π id (:: const nil))

def succ : Expr :=
  both succ.f succ.nfx

#eval step (:: succ.nfx (:: (symbol "n") (:: (symbol "f") (:: (symbol "x") nil))))
#eval do_step step (:: succ (:: (symbol "n") (:: (symbol "f") (:: (symbol "x") nil))))
#eval do_step step (:: succ (:: (symbol "n") (:: id (:: (symbol "x") nil))))
#eval do_step step (:: zero (:: (symbol "f") (:: (symbol "x") nil)))

end church

/-
Turns a function over a list of arguments
into a partially applied function over a single argument.
Exactly one argument.

TODO: I want to make this accept literally only one argument,
but we will need to make π data first.
-/
def curry (e : Expr) : Except Error Expr :=
  match e with
  | .id => pure .id
  | :: .const e => pure (:: .const e)
  /-
    both expects only one argument, the
    item to be copied.
    the equivalent to currying is
    accepting a singleton list.
  -/
  | both f g =>
    pure (both (π f nil) (π g nil))
  | π _a nil => pure e
  | π a b => do
    let rst ← curry b
    pure <| π a (:: const rst)
  | const => pure <| π id nil
  | symbol s => pure <| :: const (symbol s)
  | e => .error <| .cant_curry e

def test_curry_zero : Except Error Bool := do
  let actual ← do_step step (:: church.zero (:: (symbol "f") (:: (symbol "x") nil)))
  let ours ← do_step step (:: (:: (← curry church.zero) (:: (symbol "f") nil)) (:: (symbol "x") nil))

  pure <| actual == ours

def test_curry_succ : Except Error Bool := do
  let actual ← do_step step (:: church.succ (:: church.zero (:: id (:: (symbol "x") nil))))
  let curr ← curry church.succ
  let ours ← do_step step (:: (:: (:: curr (:: church.zero nil)) (:: id nil)) (:: (symbol "x") nil))

  dbg_trace s!"theirs: {actual}"
  dbg_trace s!"ours: {ours}"

  pure <| actual == ours

#eval test_curry_zero
#eval test_curry_succ

#eval (curry (symbol "curry")) >>= (fun c =>  do_step step (:: c (:: (symbol "fake arg") nil)))
#eval do pure <| (← do_step step (:: church.zero (:: (symbol "f") (:: (symbol "x") nil)))) ==
  (← do_step step (:: (:: (← curry church.zero) (:: (symbol "f") nil)) (:: (symbol "x") nil)))


-- 1 id whatever = whatever
#eval do_step step (:: church.succ (:: church.zero (:: id (:: (symbol "x") nil))))
#eval 


