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

/-
I like our pattern matching, but we end up
with a bunch of extra nil values.

Non-obvious application should be made clear with a
keyword.

Apply should allow us to apply singleton
lists.

Even better, apply should be like pipelining.

Even better, apply should only run step.
No magic.

Even better, we should probably only apply
when apply is run.
Otherwise, it's just data.
-/

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

def Expr.push_back (val : Expr) : Expr → Option Expr
  | :: x nil => do pure <| :: x val
  | :: x xs => do pure <| :: x (← push_back val xs)
  | _ => .none

example : Expr.push_back (:: (symbol "zero") nil) (:: (symbol "succ") nil) =
  (:: (symbol "succ") (:: (symbol "zero") nil)) := rfl

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
    | :: apply (:: f (:: g nil)) =>
      let f' ← run f <|> (pure f)
      let g' ← run g <|> (pure g)

      pure <| :: apply (:: f' (:: g' nil))
    sorry
  )

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
    pure <| :: (← step (:: f l)) (← step (:: g l))
  -- Singleton values (i.e., with no arguments, we can apply instantly
  | :: apply (:: (:: f nil) (:: (:: g nil) nil)) =>
    step <| :: f (:: g nil)
  | :: apply (:: f (:: g nil)) =>
    let f' ← step f <|> (pure f)
    let g' ← step g <|> (pure g)

    pure <| :: apply (:: f' (:: g' nil))
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

/-
f and nfx should be evaluated separately,
then pipelined.
-/
def succ : Expr :=
  both (:: const apply) (both succ.f (both succ.nfx (:: const nil)))

#eval do_step (step (with_logs := true)) (:: succ.f (:: (symbol "n") (:: id (:: (symbol "x") nil))))
#eval step (:: succ.nfx (:: (symbol "n") (:: (symbol "f") (:: (symbol "x") nil))))
#eval do_step step (:: succ (:: (symbol "n") (:: (symbol "f") (:: (symbol "x") nil))))
#eval do_step step (:: succ (:: (symbol "n") (:: id (:: (symbol "x") nil))))
#eval do_step step (:: succ (:: (symbol "n") (:: (symbol "f") (:: (symbol "x") nil))))
#eval do_step (step (with_logs := true)) (:: succ (:: zero (:: id (:: (symbol "x") nil))))
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
  | π _a (:: const nil) => pure e
  | π _a nil => pure e
  | π a b => do
    let rst ← curry b
    pure <| π a (:: const rst)
  | e => .error <| .cant_curry e

def test_curry_succ_f : Except Error Bool := do
  let expected ← do_step step (:: church.succ.f (:: (symbol "n") (:: (symbol "f") (:: (symbol "x") nil))))
  let curr ← curry church.succ.f
  dbg_trace do_step step (:: (:: (:: curr (:: (symbol "n") nil)) (:: (symbol "f") nil)) (:: (symbol "x") nil))
  dbg_trace expected
  let actual ← do_step step (:: (:: (:: curr (:: (symbol "n") nil)) (:: (symbol "f") nil)) (:: (symbol "x") nil))

  pure <| actual == expected

#eval test_curry_succ_f

--def tests_curry_succ_f : Except Error Bool := do
--  let actual ← do_step step 

def test_curry_zero : Except Error Bool := do
  let actual ← do_step step (:: church.zero (:: (symbol "f") (:: church.zero nil)))
  let ours ← do_step step (:: (:: (← curry church.zero) (:: (symbol "f") nil)) (:: church.zero nil))

  pure <| actual == ours

def test_curry_succ : Except Error Bool := do
  let actual ← do_step step (:: church.succ (:: church.zero (:: id (:: (symbol "x") nil))))
  let curr ← curry church.succ
  let ours ← do_step step (:: (:: (:: curr (:: church.zero nil)) (:: id nil)) (:: (symbol "x") nil))

  dbg_trace s!"theirs: {actual}"
  dbg_trace s!"our curr: {curr}"
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


