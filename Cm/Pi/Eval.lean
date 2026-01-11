import Mathlib.Data.Nat.Notation
import Cm.EvalUtil
import Cm.Pi.Ast

/-
TODO:
- removed singletons eval function argument. update examples
- removed :: π (:: f nil), only function pattern matching now. update as well.
-/

/-
This file used to live in Eval6.lean. I have split it up for organization.
-/

open Std (Format)
open Std (ToFormat)
open Std.ToFormat (format)

open Expr

/-
Singleton values: how necessary are they?
Should π work on singletons or actual lists?

TODO: remove sinngletones from examples
that use both, since both will auto-inject them.
-/

def step_apply (e : Expr) (with_logs : Bool := false) : Except Error Expr := do
  if with_logs then
    dbg_trace e

  match e with
  | :: .id x => pure x
  | :: (:: π (:: a b)) (:: x xs) => do
    let a' := :: apply (:: a x)
    let b' := :: apply (:: b xs)

    pure <| :: a' b'
  | :: (:: const x) _ => pure x
  | :: (:: both (:: f g)) l => pure <| :: (:: apply (:: f l)) (:: apply (:: g l))
  | e => .error <| .no_rule e

def run (e : Expr) (with_logs : Bool := false) : Except Error Expr := do
  if with_logs then
    dbg_trace e

  /-
    If this instruction can be done without nested applications, do it.
    Otherwise, handle the applications.
  -/
  /-
    Applications can happen at the top level,
    or they can be deeply nested.
    We will assume that applications have the
    requisite arguments.
  -/
  match e with
  /-
    Apply calls accept a function and an arguments list.
    NOTE: apply should always have the function as a singleton
    so as to be clear.
  -/
  | :: apply (:: f x) => do
    let eval_arg_first : Except Error Expr := do
      let x' ← run x
      pure <| :: apply (:: f x')
    let eval_f_first : Except Error Expr := do
      let f' ← run f
      pure <| :: apply (:: f' x)
    let step_whole : Except Error Expr := do
      step_apply (:: f x) with_logs

    eval_arg_first <|> eval_f_first <|> step_whole
  | :: x xs => (do
    let x' ← run x with_logs
    let xs' ← run xs with_logs
    pure <| :: x' xs') <|> (do
    let xs' ← run xs with_logs
    pure <| :: x xs') <|> (do
    let x' ← run x with_logs
    pure <| :: x' xs)
  | e => .error <| .no_rule e

/-
A basic test of the eval function:
- projecting on a list
-/

def my_eval_test : Except Error Expr := do
  let my_proj : Expr := :: π (:: id (:: π (:: id (:: const nil))))

  let my_data : Expr := :: (symbol "a") (:: (symbol "b") nil)

  do_step run (:: apply (:: my_proj my_data))

/-
Test showing that we can replace the nil value in a list
with a constant.
-/
def my_eval_test₂ : Except Error Expr := do
  let my_proj : Expr := :: π (:: id (:: π (:: id nil)))

  let my_data : Expr := :: (symbol "a") (:: (symbol "b") nil)

  do_step run (:: apply (:: my_proj my_data))

#eval my_eval_test
