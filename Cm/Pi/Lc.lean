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

#eval do_step run (:: apply (:: (get_nth_pos 0) (:: (symbol "0th") (:: (symbol "1th") (:: (symbol "2nd") nil)))))
#eval do_step run (:: apply (:: (get_nth_pos 1) (:: (symbol "0th") (:: (symbol "1th") (:: (symbol "2nd") nil)))))
#eval do_step run (:: apply (:: (get_nth_pos 2) (:: (symbol "0th") (:: (symbol "1th") (:: (symbol "2nd") nil)))))

/-
argument is the λ body

bound variables just use get_nth_pos. we should have an entry in our context.

free variables get the get_nth_pos of the context length - the depth

We are using 0-indexed debruijn indices
-/
def abstract (depth : ℕ) : LcExpr DebruijnIdx → Except Error Expr
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
  

def Expr.of_lc : LcExpr DebruijnIdx → Except Error Expr
  

end positional

namespace curried

/-
Translation of de bruijn lambda calc expressions to our expressions.

We will use curried parameters for this version.
-/

/-
Converts the body of a lambda abstraction to an expression.
-/
def abstract : LcExpr DebruijnIdx → Except Error Expr
  | .var (n + 1) => do
    sorry
  | .app f x => do
    sorry
  | _ => sorry

def Expr.of_lc : LcExpr DebruijnIdx → Except Error Expr
  -- an n-height variable corresponds roughly to a nested π expression
  -- (:: referenced nil)
  -- for example, .var 0 => π id
  | .var v => pure <| .symbol (toString v)
  | .app f x => do
    let f' ← Expr.of_lc f
    let x' ← Expr.of_lc x

    sorry
  | .lam body => do
    sorry

end curried
