import Mathlib.Data.Nat.Notation

open Std (Format)
open Std (ToFormat)
open Std.ToFormat (format)

inductive Expr where
  | cons   : Expr
    → Expr
    → Expr
  | apply  : Expr
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
  | .apply => "apply"
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

/-
Wraps f and x as singleton values,
then applies.
-/
def mk_apply_now (f x : Expr) : Expr :=
  :: apply (:: (:: f nil) (:: (:: x nil) nil))

notation "f$" => mk_apply_now

def step_apply (e : Expr) (with_logs : Bool := false) : Except Error Expr := do
  if with_logs then
    dbg_trace e

  match e with
  | :: .id x => pure x
  | :: (π a nil) (:: x nil) =>
    pure <| f$ a x
  | :: (π a b) (:: x xs) => do
    let a'  := f$ a x

    -- f$ will pass the entire xs in as
    -- a single value, but apply will
    -- give it back to us
    -- in full list form.
    let b' := f$ b xs

    pure <| :: a' b'
  | :: (:: const x) _ => pure x
  /-
    Assume l is a single value here.
  -/
  | :: (both f g) (:: l nil) =>
    let f' := f$ f l
    let g' := f$ g l
    pure <| :: f' g'
  | e => .error <| .no_rule e

def run (e : Expr) (with_logs : Bool := false) : Except Error Expr := do
  if with_logs then
    dbg_trace e

  /-
    If this instruction can be done without nested applications, do it.
    Otherwise, handle the applications.
  -/
  step_apply e with_logs
    <|> (do
    /-
      Applications can happen at the top level,
      or they can be deeply nested.
      We will assume that applications have the
      requisite arguments.
    -/
    match e with
    /-
      Apply calls always accept a singleton function,
      and a singleton value.
      We evaluate f and x in case there is nestesd
      application.

      If there is a nested application,
      it will be bubbled up to us for free.
    -/
    | :: apply (:: (:: f nil) (:: (:: x nil) nil)) => do
      let eval_arg_first : Except Error Expr := do
        let x' ← run x
        pure <| :: apply (:: (:: f nil) (:: (:: x' nil) nil))
      let eval_f_first : Except Error Expr := do
        let f' ← run f
        pure <| :: apply (:: (:: f' nil) (:: (:: x nil) nil))
      let step_whole : Except Error Expr := do
        step_apply (:: f x)

      eval_arg_first <|> eval_f_first <|> step_whole
    | e => .error <| .stuck e
  )
