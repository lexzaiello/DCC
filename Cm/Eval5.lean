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

open Expr

def Expr.fmt (e : Expr) : Format :=
  match e with
  | .π a b => .paren <| "π " ++ a.fmt ++ .line ++ b.fmt
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

instance Expr.instToFormat : ToFormat Expr where
  format := Expr.fmt

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

def step_uncurry (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if with_logs then
    dbg_trace e

  match e with
  | :: .id x => pure x
  | :: (π a nil) (:: x nil) => do
    let a' ← step_uncurry (:: a x)
    pure <| :: a' nil
  | :: (π a b) (:: x xs) => do
    let a' ← step_uncurry (:: a x)
    let b' ← step_uncurry (:: b xs)
    pure <| :: a' b'
  | :: (:: const x) _ => pure x
  | :: (both f g) l =>
    let g' ← step_uncurry (:: g l)
    match (← step_uncurry (:: f l)) with
    | :: v nil =>
      pure <| :: v (:: g' nil)
    | _ => .none
  | :: f x => :: (← step_uncurry f) x
  | _ => .none

def try_step_n (f : Expr → Option Expr) (n : ℕ) (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if n = 0 then
    pure e
  else
    let e' ← f e
    (try_step_n f (n - 1) e' with_logs) <|> (pure e')

def do_step (f : Expr → Option Expr) (e : Expr) (with_logs : Bool := false):= try_step_n f 20 e with_logs

namespace church'

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
  π (:: const id) (π id nil)

def succ : Expr :=
  both (

#eval do_step step_uncurry (:: zero (:: (symbol "f") (:: (symbol "x") nil)))

def succ.n : Expr := read

def succ.f : Expr :=
  (:: next read)

def succ.x : Expr :=
  (:: next (:: next read))

def succ.fx : Expr :=
  (both succ.f (both succ.x nil))

def succ.nfx : Expr :=
  (both succ.n succ.fx)

def succ.f_append : Expr :=
  (both (:: const append) (both succ.f nil))

def succ : Expr :=
  both succ.f_append (both succ.nfx nil)

def succ' : Expr :=
  both (both (:: const append) (both (:: const (symbol ("f"))) (:: const nil))) (:: const (symbol "nfx"))

-- nfx outputs the correct value
#eval do_step step (:: succ.nfx (:: zero (:: (symbol "f") (:: (symbol "x") nil)))) == some (symbol "x")

-- succ outputs the correct value
-- succ 0 f x = :: f (:: (0 f x) nil)
-- we should assume this is a single argument
#eval do_step step (:: succ (:: zero (:: (symbol "f") (:: (symbol "x") nil)))) == some (:: (symbol "f") (:: (symbol "x") nil))

-- curried form
#eval do_step step (:: succ.nfx (:: zero nil))
#eval ToFormat.format <$> do_step step (:: (:: succ.nfx (:: zero nil)) (:: (symbol "f") (:: (symbol "x") nil)))

end church'
