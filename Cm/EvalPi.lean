import Mathlib.Data.Nat.Notation

/-
Would be nice if we could dictate the order of evaluation somehow.
Both is nice, but we need the reverse as well.
Perhaps we can derive it somewhat easily.

:: (both f g) l = :: (:: f l) (:: g l)

Technically :: is sequencing.
:: f x = do f, then apply x.

So, we can just do
both

The main tricky spot is in succ,
f (n f x)

This shouldn't be an issue, since there is an extra nil.
We can remove the extra nil with our "anonymous function
factory".

Another thought:
we can probably replace next and read with
π and id.

next = π (:: const (:: append nil))
const is necessary, though.

Is append necessary?
Maybe.
-/

open Std (Format)
open Std (ToFormat)

inductive Expr where
  | cons   : Expr
    → Expr
    → Expr
  | id     : Expr
  | π      : Expr
    → Expr
    → Expr
  | const  : Expr
  | append : Expr
  | both   : Expr
    → Expr
    → Expr
  | nil    : Expr
  | symbol : String
    → Expr
deriving Repr, BEq

def Expr.fmt (e : Expr) : Format :=
  match e with
  | .quote e => "quote " ++ e.fmt
  | .append => "append"
  | .π f g => .paren ("π " ++ f.fmt ++ Format.line ++ g.fmt)
  | .next => "next"
  | .nat n => ToFormat.format n
  | .cons (.cons a b) (.cons c d) =>
    ":: " ++ (.group <| .nest 2 <| (.paren (Expr.cons a b).fmt) ++ Format.line ++ (.paren (Expr.cons c d).fmt))
  | .cons (.cons a b) xs =>
    ":: " ++ (.group <| .nest 2 <| (.paren (Expr.cons a b).fmt) ++ Format.line ++ xs.fmt)
  | .cons x (.cons a b) =>
    ":: " ++ (.group <| .nest 2 <| x.fmt ++ Format.line ++ (.paren (Expr.cons a b).fmt))
  | .cons x xs =>
    ":: " ++ (.group <| .nest 2 <| x.fmt ++ Format.line ++ xs.fmt)
  | .read => "read"
  | .const => "const"
  | .both f g => .paren ("both " ++ (.group <| .nest 2 <| (.paren f.fmt) ++ Format.line ++ (.paren g.fmt)))
  | .nil => "nil"
  | symbol s => .paren ("symbol " ++ ("\"" ++ s ++ "\""))

instance Expr.instToFormat : ToFormat Expr where
  format := Expr.fmt

instance Expr.instToString : ToString Expr where
  toString := toString ∘ Expr.fmt

open Expr

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

def step (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if with_logs then
    dbg_trace e

  let mk_append (f args : Expr) : Option Expr :=
    both (:: const f) (:: append args)

  match e with
  | :: (:: append a) b =>
    match (step a).getD a, (step b).getD b with
    | a@(:: x xs), b =>
      Expr.push_back b a
    | v, b => :: (:: append v) b
  | :: .read (:: x xs) => pure x
  | :: (:: .const x) _l => pure x
  | :: (:: next f) (:: _x nil) => .none
  | :: (:: next f) (:: _x xs) => step (:: f xs) with_logs
  | :: b@(both f nil) l@(:: _x _xs) => do
    match step (:: f l) with_logs with
    | .some f' =>
      :: f' nil
    | .none => do
      both (← mk_append f l) nil
  | :: b@(both f g) l@(:: _x _xs) => do
    match step (:: f l) with_logs, step (:: g l) with_logs with
    | .some f', .some g' =>
      :: f' g'
    | .some f', .none => do
      both (:: const f') (← mk_append g l)
    | .none, .some g' => do
      both (← mk_append f l) (:: const g')
    | .none, .none => .none
  | :: (both f g) nil => pure <| :: (← step (:: f nil)) (← step (:: g nil))
  | :: f x => :: (← step f) x
  | _ => .none

namespace church

def zero : Expr :=
  (:: next read)

namespace succ

def n : Expr := read

def f : Expr :=
  (:: next read)

def x : Expr :=
  (:: next (:: next read))

def fx : Expr :=
  (both succ.f succ.x)

def nfx : Expr :=
  (both succ.n succ.fx)

end succ

def succ : Expr :=
  (both succ.f (both succ.nfx nil))

end church

def mk_church : ℕ → Option Expr
  | .zero => church.zero
  | .succ n => do
    let inner ← mk_church n
    pure (:: church.succ inner)

