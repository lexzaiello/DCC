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
  | .app f x => "f$ " ++ Format.paren (.group <| .nest 2 <| f.fmt ++ Format.line ++ x.fmt)
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

We can just eval at the very end I guess.
Or do a similar trick with nil.

If inner is :: x nil, then
we can do a π inside

π id _

I want to optimize this more.

could do (:: const (:: both id (:: const nil)))

(:: both (:: (:: const const) id))

Perhaps opposite order.
We're just continually popping off the stack.
Shouldn't be too hard.

Oh yo idea. :: then_cons

Then we get something that we can lazilly put on our stack.

We can be lazy. Nested id is fine.
We're not introducing any new nil values.
-/
def get_nth_pos (n : ℕ) : Expr :=
  let rec mk_get_nth_pos (n : ℕ) : Expr :=
    match n with
    | .zero => :: π (:: id (:: const nil))
    | .succ n =>
      -- arg 1: π (:: (:: const const) (:: π (:: const (:: const nil))))
      (:: π (:: (:: const id) (mk_get_nth_pos n)))

  mk_get_nth_pos n

--#eval try_step_n run 2 (:: apply (:: (get_nth_pos 0) (:: (symbol "0th") nil)))
--#eval try_step_n run 2 (:: apply (:: (get_nth_pos 0) (:: (symbol "0th") (:: (symbol "1th") (:: (symbol "2nd") nil)))))
--#eval try_step_n run 4 (:: apply (:: (get_nth_pos 2) (:: (symbol "0th") (:: (symbol "1th") (:: (symbol "2nd") nil)))))
--#eval do_step run (:: apply (:: (get_nth_pos 2) (:: (symbol "0th") (:: (symbol "1th") (:: (symbol "2nd") nil)))))

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
    let f' := abstract depth f
    let x' := abstract depth x

    match f' with
    | :: apply s =>
      (:: both (:: (quote f') x'))
    | _ =>
      (:: both (:: (quote apply) (:: both (:: (quote f') x'))))

    /-match f', contains_free depth f with
    | f', true =>
      :: apply (:: f' nil)
    | :: apply (:: f ctx), false =>
      :: apply (:: f (:: x' ctx))
    | f, false =>
      :: apply (:: f (:: x' nil))-/
  | .lam body => abstract depth.succ body
  -- symbol in body, so we should quote it
  | .symbol s => quote (symbol s)

def Expr.of_lc : LcExpr DebruijnIdx → Except Error Expr
  | .var _n =>
    .error .var_in_output
  | .lam b =>
    pure <| abstract 1 b
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

def mk_test (step_with : Expr → Except Error Expr) (lam_e : LcExpr DebruijnIdx) : Except Error Expr := do
  let cm_e ← Expr.of_lc lam_e
  do_step step_with cm_e

/-
(λ x.x) (symbol "Hello, world")
-/

def test_hello_world := (f$ (λ! (f$ (λ! (f$ (λ! (.var 0)) (.var 0))) (.var 0))) (.symbol "Hello, world"))
  |> mk_test run

#eval test_hello_world

/-
Church encoding of true. should get the first argument.

tre a b = a
tre = λ λ.1
-/

def tre_lc := (λ! (λ! (.var 1)))
def tre := f$ (f$ tre_lc (.symbol "Hello, world")) (.symbol "other")
  |> mk_test run

--#eval test_hello_world
--#eval tre
--#eval Expr.of_lc tre_lc

/-
Church encoding of false. should get the second argument.
-/

def flse_lc := (λ! (λ! (.var 0)))
def flse := f$ (f$ flse_lc (.symbol "Hello, world")) (.symbol "other")
  |> mk_test run

--#eval flse

/-
(flse "hello world" (λx.x)) ("hello world")
-/

def flse_i_app := f$ (f$ (f$ (λ! (λ! (.var 0))) (.symbol "bruh")) (λ! (.var 0))) (.symbol "Hello, world")
  |> mk_test run

--#eval flse_i_app

def tre_i_app := f$ (f$ (f$ (λ! (λ! (.var 1))) (λ! (.var 0))) (.symbol "Hello, world")) (.symbol "Hello, world")
  |> mk_test run

--#eval tre_i_app

def zero_lc := λ! (λ! (.var 0))

def zero_hello_world_app := f$ (f$ zero_lc (λ! (.var 0))) (.symbol "Hello, world")
  |> mk_test run

--#eval zero_hello_world_app

-- succ n f x = f (n f x)
-- f is bound to the second lambda
-- n is bound to the top lambda
def succ_lc := λ! (λ! (λ! (f$ (.var 1) (f$ (f$ (.var 2) (.var 1)) (.var 0)))))

--#eval succ_lc

--#eval Expr.of_lc succ_lc

def succ_nfx_lc := λ! (λ! (λ! (f$ (f$ (.var 2) (.var 1)) (.var 0))))

def one_hello_world_app := f$ (f$ (f$ succ_lc zero_lc) (λ! (.var 0))) (.symbol "Hello, world")
  |> mk_test run

#eval one_hello_world_app
  >>= do_step run
  >>= do_step run

def two_hello_world_app := f$ (f$ (f$ succ_lc (f$ succ_lc zero_lc)) (λ! (.var 0))) (.symbol "Hello, world")
  |> mk_test run

--#eval two_hello_world_app

def three_hello_world_lc := f$ (f$ (f$ succ_lc (f$ succ_lc (f$ succ_lc zero_lc))) (λ! (.var 0))) (.symbol "Hello, world")

def test_three_hello_world : Except Error Expr := do
  let cm_e ← Expr.of_lc three_hello_world_lc
  try_step_n run 3 cm_e

--#eval test_three_hello_world

def five_hello_world_lc := f$ (f$ (f$ succ_lc (f$ succ_lc (f$ succ_lc (f$ succ_lc (f$ succ_lc zero_lc))))) (λ! (.var 0))) (.symbol "Hello, world")

def test_five_hello_world : Except Error Expr := do
  let cm_e ← Expr.of_lc five_hello_world_lc
  try_step_n run 3 cm_e

--#eval test_five_hello_world

def mk_test_hello_world_n (n max_steps : ℕ) : Except Error Expr := do
  let succ_e := List.replicate n succ_lc
    |> List.foldr (fun succ_e acc => (f$ succ_e acc)) zero_lc

  let hello_e := (f$ (f$ succ_e (λ! (.var 0))) (.symbol "Hello, world"))

  let cc ← Expr.of_lc hello_e
  try_step_n run max_steps cc

--#eval mk_test_hello_world_n 80 3

--#eval test_three_hello_world

def three_hello_world_app := f$ (f$ (f$ succ_lc (f$ succ_lc (f$ succ_lc zero_lc))) (λ! (.var 0))) (.symbol "Hello, world")
  |> mk_test run

--#eval three_hello_world_app

/-
Y = λ f (λ x.f(x x))(λ x. f(x x))
λx.f(x x) = (λ! ($f (.var 1) ($f (.var 0) (.var0))))
Y = λ! (
-/
def y_comb_lc : LcExpr DebruijnIdx :=
  let inner := (λ! (f$ (.var 1) (f$ (.var 0) (.var 0))))
  λ! (f$ inner inner)

/-
iszero = λn.n(λx.flse)tre
iszero (succ(zero)) = (succ(zero)) (λx.flse) tre
iszero zero = zero _ tre = tre
iszero = λ! (f$ (f$ (.var 0) (λ! flse)) tre)
-/
def is_zero_lc : LcExpr DebruijnIdx :=
  λ! (f$ (f$ (.var 0) (λ! flse_lc)) tre_lc)

/-
If the output is true, then we should be able to plug in
"a" and "b" and get out "a"
-/
def test_is_zero (max_steps : ℕ := 20) : Except Error Expr := do
  let tre_test := (f$ (f$ tre_lc (.symbol "a")) (.symbol "b"))
  let test := (f$ (f$ zero_lc (.symbol "a")) (.symbol "true"))
  --let is_zero_app_zero := (f$ (f$ (f$ (f$ zero_lc (.symbol "a")) tre_lc) (.symbol "a")) (.symbol "b"))
  let cc ← Expr.of_lc tre_test
  try_step_n run max_steps cc

--#eval test_is_zero

end positional

