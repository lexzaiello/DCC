import Mathlib.Data.Nat.Notation

import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util
import Cm.Pi.Curry

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

notation "λ!" => LcExpr.lam
notation "f$" => LcExpr.app

/-
Potential translation with positinal parameters:

Make a context of substitutions, which is the list of arguments.
-/

namespace positional

open Expr

def apply_now (op : Expr) : Expr :=
  (:: both (:: (:: const apply) op))

def apply_now_pointfree : Expr :=
  (:: both (:: (:: const apply) id))

/-
Fetches the nth value in the context / positional arguments,
and strips the nil value
-/
def get_nth_pos (n : ℕ) : Expr :=
  let rec mk_get_nth_pos (n : ℕ) : Expr :=
    match n with
    | .zero => :: π (:: const (:: const nil))
    | .succ n =>
      -- arg 1: π (:: (:: const const) (:: π (:: const (:: const nil))))
      (:: π (:: (:: const apply_now_pointfree) (mk_get_nth_pos n)))

  let get_idx := mk_get_nth_pos n
  apply_now get_idx

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

mutual

/-
argument is the λ body

bound variables just use get_nth_pos. we should have an entry in our context.

free variables get the get_nth_pos of the context length - the depth

We are using 0-indexed debruijn indices
-/

def abstract (depth : ℕ) : LcExpr DebruijnIdx → Except Error Expr
  | .symbol s => pure <| (:: const (symbol s))
  | .var n =>
    -- λ.0 has depth 1, so it is free
    -- its substitution should be the first thing in the context
    if n < depth then
      pure <| get_nth_pos n
    else
      -- future context. delete the binders so far
      -- e.g., λ.1 is free if depth == 1, so substract one
      -- TODO: something funky here probably
      let n' := n - depth
      pure <| quote (get_nth_pos n')
  | .app f x => do
    let x' ← Expr.of_lc x
    let f' ← Expr.of_lc f

    -- now we push the value onto the context
    -- if there is one
    pure <| steal_context x' f'
  | .lam body => do
    abstract depth.succ body

def Expr.of_lc : LcExpr DebruijnIdx → Except Error Expr
  | .symbol s => pure <| .symbol s
  | .app f x => do
    let f' ← Expr.of_lc f
    let x' ← Expr.of_lc x

    -- if f' has a context, this should be added to it
    -- this is the root value, so we give it an empty context? TODO: not sure about this
    -- TODO: major sus
    pure <| steal_context x' f'
  | .lam body => do
    abstract 1 body
  | .var _n =>
    .error .var_in_output

end

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

def one_hello_world_app_lc := f$ (f$ (f$ succ_lc zero_lc) (λ! (.var 0))) (.symbol "Hello, world")

def one_hello_world_app := f$ (f$ (f$ succ_lc zero_lc) (λ! (.var 0))) (.symbol "Hello, world")
  |> mk_test run

#eval one_hello_world_app

/-
zero id ("hello world") = "hello world"
-/
--def zero_id_hello_world := f$ 

end positional

