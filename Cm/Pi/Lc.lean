import Mathlib.Data.Nat.Notation

import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util
import Cm.Pi.Curry

open Std (Format)
open Std (ToFormat)
open Std.ToFormat (format)

open Expr

abbrev DebruijnIdx := ℕ

/-
A lambda calculus expression where variables are represented by
the type α.
-/
inductive LcExpr (α : Type) where
  | app : LcExpr α
    → LcExpr α
    → LcExpr α
  | lam : LcExpr α
    → LcExpr α
  | var : α → LcExpr α
  | symbol : String -- our machine has these
    → LcExpr α

def LcExpr.fmt : (LcExpr DebruijnIdx) → Format
  | .app f x => .paren <| (.group <| .nest 2 <| f.fmt ++ Format.line ++ x.fmt)
  | .var n => s!".var {n}"
  | .lam body => "(λ! " ++ .paren body.fmt ++ ")"
  | .symbol s => s!"(symbol {s})"

instance LcExpr.instToFormat : ToFormat (LcExpr DebruijnIdx) where
  format := LcExpr.fmt

instance LcExpr.instToString : ToString (LcExpr DebruijnIdx) where
  toString := toString ∘ format

notation "λ!" => LcExpr.lam
notation "f$" => LcExpr.app

/-
Potential translation with positinal parameters:

Make a context of substitutions, which is the list of arguments.
-/

namespace positional

open Expr

def apply_now_pointfree : Expr :=
  (:: both (:: (:: const apply) id))

/-
Fetches the nth value in the context / positional arguments,
and strips the nil value

Suspicion: const apply whatever should only happen at the very end
recursively.
-/
def get_nth_pos (n : ℕ) : Expr :=
  let rec mk_get_nth_pos (n : ℕ) : Expr :=
    match n with
    | .zero => :: π (:: const (:: const nil))
    | .succ n =>
      -- arg 1: π (:: (:: const const) (:: π (:: const (:: const nil))))
      (:: π (:: (:: const apply_now_pointfree) (mk_get_nth_pos n)))

  apply_now <| mk_get_nth_pos n

/-
Prepends a value to the context
-/
def cons_ctx (with_val : Expr) : Expr → Expr := (:: with_val ·)

def steal_context (x' : Expr) : Expr → Expr
  | :: apply (:: f ctx) => :: apply (:: f (cons_ctx x' ctx))
  | e => :: apply (:: e (:: x' nil))

#eval do_step run (:: apply (:: (get_nth_pos 0) (:: (symbol "0th") nil)))
#eval do_step run (:: apply (:: (get_nth_pos 0) (:: (symbol "0th") (:: (symbol "1th") (:: (symbol "2nd") nil)))))
#eval do_step run (:: apply (:: (get_nth_pos 1) (:: (symbol "0th") (:: (symbol "1th") (:: (symbol "2nd") nil)))))
#eval do_step run (:: apply (:: (get_nth_pos 2) (:: (symbol "0th") (:: (symbol "1th") (:: (symbol "2nd") nil)))))

/-
argument is the λ body

bound variables just use get_nth_pos. we should have an entry in our context.

free variables get the get_nth_pos of the context length - the depth

We are using 0-indexed debruijn indices

Issue is the free variables, and also substitution.
When we substitute in, we should probably increment all the free variables.

If bound, do not change.
If free, increment by one every time substituted into a lambda.

Apply now logic is very suspicious.
Should only now_apply when lambda application invoked.

Apply should be happening inside abstract, not in get thingy.

Question one:
- what happens if we remove the apply_now_pointfree?

We need to increment free variables upon substitution.
Increment them all by one.
-/

/-
(λ.λ.1) λ.0
bound variable does not change.
free variables increment?
-/

/-
Run this with depth := 0
-/
def incr_free (depth : ℕ) : LcExpr DebruijnIdx → LcExpr DebruijnIdx
  | .var n =>
    if n > depth then
      .var n.succ
    else
      .var n
  | .lam b => .lam <| incr_free depth.succ b
  | .app f x => .app (incr_free depth f) (incr_free depth x)
  | .symbol s => .symbol s

def contains_free (depth : ℕ) : LcExpr DebruijnIdx → Bool
  | .var n => n > depth
  | .app f x => contains_free depth f || contains_free depth x
  | .symbol _ => false
  | .lam body => contains_free depth.succ body

/-def abstract (depth : ℕ) : LcExpr DebruijnIdx → Expr
  | .symbol s => (symbol s)
  | .var n =>
    -- λ.0 has depth 1, so it is free
    -- its substitution should be the first thing in the context
    if n < depth then
      get_nth_pos n
    else
      -- future context. delete the binders so far
      -- e.g., λ.1 is free if depth == 1, so substract one
      -- TODO: something funky here probably
      let n' := n - depth
      quote (get_nth_pos n')
  | .app f x =>
    -- to translate f, treat it as if it were a λ binder: potentially SUS
    -- however, the depth should not increase?
    let x' := abstract depth x
    let f' := abstract depth f

    /- if 
    match f', contains_free 0 f with
    | :: apply (:: f ctx), true =>
      pure <| :: apply (:: f (:: x' ctx))
    | f, _ =>
      pure <| :: apply (:: f (:: x' nil))-/
    -- if f' contains no free variables, then
    -- we are free to substitute the value in
    -- e.g., (λ.0) x we can substitute,
    -- but (λ.1) x we cannot
    -- nonetheless, this is an application, so
    --dbg_trace s!"free in {contains_free depth f}: original: {f} f': {f'}"
    match f', contains_free depth f with
    | _, true =>
      :: apply (:: f' nil)
    | :: apply (:: f ctx), false =>
      :: apply (:: f (:: x' ctx))
    | f, false =>
      :: apply (:: f (:: x' nil))
  | .lam body => abstract depth.succ body-/

def is_lam {α : Type} : LcExpr α → Bool
  | .lam _ => true
  | _ => false

mutual

/-
ONLY for λ bodies. arg is the λ body
Pretty sure we just need to fix incrementing bound variables
-/
def abstract (depth : ℕ) : LcExpr DebruijnIdx → Expr
  | .var n =>
    if n < depth then
      get_nth_pos n
    else
      -- TODO: suspicious
      let n' := n - depth
      quote (get_nth_pos n')
  | .app f x =>
    let x' := abstract depth x
    let f' := abstract depth f

    match f', contains_free depth f with
    | _, true =>
      :: apply (:: f' nil)
    | :: apply (:: f ctx), false =>
      :: apply (:: f (:: x' ctx))
    | f, false =>
      :: apply (:: f (:: x' nil))
  | .lam body => abstract depth.succ body
  -- symbol in body, so we should quote it
  | .symbol s => quote (symbol s)

def Expr.of_lc : LcExpr DebruijnIdx → Except Error Expr
  | .var _n =>
    .error .var_in_output
  | .lam b => pure <| abstract 1 b
  | .app f x => do
    let f' ← Expr.of_lc f
    let x' ← Expr.of_lc x

    -- TODO: sus, potentially change this to below
    --pure <| :: apply (:: f' (:: x' nil))
    match f', contains_free (if is_lam f then 1 else 0) f with
    | _, true =>
      pure <| :: apply (:: f' nil)
    | :: apply (:: f ctx), false =>
      pure <| :: apply (:: f (:: x' ctx))
    | f, false =>
      pure <| :: apply (:: f (:: x' nil))
  | .symbol s => pure <| symbol s

end

--def Expr.of_lc := abstract 0

/-
SUS: Expr.of_lc potentially totally unnecessary?
def Expr.of_lc : LcExpr DebruijnIdx → Except Error Expr
  | .symbol s => pure <| .symbol s
  | .app f x => do
    let f' ← abstract 1 f
    let x' ← Expr.of_lc x

    -- if f' has a context, this should be added to it
    -- this is the root value, so we give it an empty context? TODO: not sure about this
    -- TODO: major sus
    pure <| steal_context x' f'
  | .lam body => do
    abstract 1 body
  | .var _n =>
    .error .var_in_output
-/

def mk_test (step_with : Expr → Except Error Expr) (lam_e : LcExpr DebruijnIdx) : Except Error Expr := do
  let cm_e ← Expr.of_lc lam_e
  do_step step_with cm_e

/-
(λ x.x) (symbol "Hello, world")
-/

def test_hello_world := (f$ (λ! (.var 0)) (.symbol "Hello, world"))
  |> mk_test run

#eval test_hello_world

/-
Church encoding of true. should get the first argument.

tre a b = a
tre = λ λ.1
-/

def tre := f$ (f$ (λ! (λ! (.var 1))) (.symbol "Hello, world")) (.symbol "other")
  |> mk_test run

#eval test_hello_world
#eval tre

/-
Church encoding of false. should get the second argument.
-/

def flse := f$ (f$ (λ! (λ! (.var 0))) (.symbol "Hello, world")) (.symbol "other")
  |> mk_test run

#eval flse

/-
(flse "hello world" (λx.x)) ("hello world")
-/

def flse_i_app := f$ (f$ (f$ (λ! (λ! (.var 0))) (.symbol "Hello, world")) (λ! (.var 0))) (.symbol "Hello, world")
  |> mk_test run

#eval flse_i_app

def tre_i_app := f$ (f$ (f$ (λ! (λ! (.var 1))) (λ! (.var 0))) (.symbol "Hello, world")) (.symbol "Hello, world")
  |> mk_test run

#eval tre_i_app

def zero_lc := λ! (λ! (.var 0))

def zero_hello_world_app := f$ (f$ zero_lc (λ! (.var 0))) (.symbol "Hello, world")
  |> mk_test run

#eval zero_hello_world_app

-- succ n f x = f (n f x)
-- f is bound to the second lambda
-- n is bound to the top lambda
def succ_lc := λ! (λ! (λ! (f$ (.var 1) (f$ (f$ (.var 2) (.var 1)) (.var 0)))))

def succ_nfx_lc := λ! (λ! (λ! (f$ (f$ (.var 2) (.var 1)) (.var 0))))

def one_hello_world_app_lc := f$ (f$ (f$ succ_lc zero_lc) (λ! (.var 0))) (.symbol "Hello, world")

def one_hello_world_app := f$ (f$ (f$ succ_lc zero_lc) (λ! (.var 0))) (.symbol "Hello, world")
  |> mk_test run

def one_hello_world_app' := (f$ (f$ succ_lc zero_lc) (λ! (.var 0)))
  |> mk_test run

#eval one_hello_world_app'

#eval one_hello_world_app_lc
#eval one_hello_world_app

/-
zero id ("hello world") = "hello world"
-/
--def zero_id_hello_world := f$

end positional

