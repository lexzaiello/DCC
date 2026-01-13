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

def mk_n_const (n : ℕ) (inner_e : Expr) : Expr := (List.replicate n Expr.const).foldr (fun _e acc => (quote acc)) inner_e

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
notation:max "#" => @LcExpr.var DebruijnIdx

def is_bound (var depth : ℕ) : Bool := var < depth

def all_bound (depth : ℕ) : LcExpr DebruijnIdx → Bool
  | .var n => is_bound n depth
  | .lam b => all_bound depth.succ b
  | .symbol _s => true
  | .app f x => all_bound depth f && all_bound depth x

def all_free (depth : ℕ) : LcExpr DebruijnIdx → Bool
  | .var n => ¬ (is_bound n depth)
  | .lam b => all_free depth.succ b
  | .symbol _s => true
  | .app f x => all_free depth f && all_free depth x

def quot_if_free (depth : ℕ) (original : LcExpr DebruijnIdx) (e : Expr) : Expr :=
  if all_free depth original then
      (:: both (:: (quote const) e))
  else e

def quot_if_bound (depth : ℕ) (original : LcExpr DebruijnIdx) (e : Expr) : Expr :=
  if all_bound depth original then
      (:: both (:: (quote const) e))
  else e

def decr_all_vars : LcExpr DebruijnIdx → LcExpr DebruijnIdx
  | .var n => .var (n - 1)
  | .app f x => .app (decr_all_vars f) (decr_all_vars x)
  | .lam bdy => .lam (decr_all_vars bdy)
  | .symbol s => .symbol s

