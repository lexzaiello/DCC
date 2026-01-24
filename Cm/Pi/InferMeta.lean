import Mathlib.Tactic
import Cm.Pi.Ast
import Cm.Pi.Std.Except

open Expr

inductive is_step_once : Expr → Expr → Prop
  | app_id       : is_step_once (:: apply (:: id x)) x
  | app_const    : is_step_once (:: apply (:: (:: const c) _x)) c
  | app_both     : is_step_once (:: apply (:: (:: both (:: f g)) x))
    (:: (:: apply (:: f x)) (:: apply (:: g x)))
  | app_π_both   : is_step_once (:: apply (:: (:: π (:: fx fxs)) (:: x xs)))
    (:: (:: apply (:: fx x)) (:: apply (:: fxs xs)))
  | app_eq_yes   : a == b → is_step_once (:: apply (:: (:: (:: eq (:: fn_yes fn_no)) a) b))
    (:: apply (:: fn_yes a))
  | app_eq_no    : a ≠ b  → is_step_once (:: apply (:: (:: (:: eq (:: fn_yes fn_no)) a) b))
    (:: apply (:: fn_no b))

inductive is_step_star : Expr → Expr → Prop
  | once  : is_step_once e e'
    → is_step_star e e'
  | left  : is_step_star lhs lhs'
    → is_step_star (:: lhs rhs)
                   (:: lhs' rhs)
  | right : is_step_star rhs rhs'
    → is_step_star (:: lhs rhs)
                   (:: lhs rhs')
  | trans : is_step_star e e'
    → is_step_star e' e''
    → is_step_star e e''

example : is_step_once (:: apply (:: id (symbol "a"))) (symbol "a") :=
  .app_id

def TData : Expr := .symbol "Data"
def IList : Expr := .symbol "List"

inductive valid_judgment : Expr → Expr → Prop
  | symbol : valid_judgment (symbol s) TData
  | nil    : valid_judgment nil (:: IList TData)
  | list   : valid_judgment x α
    → valid_judgment xs (:: IList α)
    → valid_judgment (:: x xs) (:: IList α)
  | both   : valid_judgment (:: apply (:: f x)) α
    → valid_judgment (:: apply (:: g x)) (:: IList α)
    → valid_judgment (:: apply (:: (:: both (:: f g)) x)) (:: IList α)
  | id     : valid_judgment x α → valid_judgment (:: apply (:: id x)) α
  | const  : valid_judgment x α → valid_judgment (:: apply (:: (:: const x) _y)) α
  | π      : valid_judgment (:: apply (:: fx x)) α
    → valid_judgment (:: apply (:: fxs xs)) (:: IList α)
    → valid_judgment (:: apply (:: (:: π (:: fx fxs)) (:: x xs))) (:: IList α)
  | eq     : valid_judgment a t
    → valid_judgment b t
    → valid_judgment (:: apply (:: yes_case a)) t'
    → valid_judgment (:: apply (:: no_case b)) t'
    → valid_judgment (:: apply (:: (:: (:: eq (:: yes_case no_case)) a) b)) t'

def is_value : Expr → Prop
  | :: f x => f ≠ apply ∧ (is_value x)
  | .symbol _s | both | .id | const
  | π | eq | nil | apply => true

example : valid_judgment (:: (:: apply (:: (:: const (symbol "hello, ")) (symbol "discard"))) (:: (symbol "world") nil)) (:: IList TData) := by
  apply valid_judgment.list
  apply valid_judgment.const
  apply valid_judgment.symbol
  apply valid_judgment.list
  apply valid_judgment.symbol
  apply valid_judgment.nil

example : valid_judgment (:: apply (:: (:: both (:: (quote (symbol "a")) (quote (:: (symbol "b") nil)))) nil)) (:: IList TData) := by
  apply valid_judgment.both
  apply valid_judgment.const
  apply valid_judgment.symbol
  apply valid_judgment.const
  apply valid_judgment.list
  apply valid_judgment.symbol
  apply valid_judgment.nil

/-
Omega does not type-check.
(λ x => x x)(λ x => x x)
-/
example : ¬ ∃ t, (valid_judgment (:: apply (:: (:: both (:: (quote apply) (:: both (:: id id)))) (:: both (:: (quote apply) (:: both (:: id id)))))) t) := by
  intro ⟨t, h_t⟩
  cases h_t
  repeat contradiction

theorem preservation (h_t : valid_judgment e t) (h_step : is_step_once e e') : valid_judgment e' t := by
  induction h_t generalizing e'
  repeat contradiction
  cases h_step
  repeat contradiction
  cases h_step
  apply valid_judgment.list
  repeat assumption
  cases h_step
  assumption
  cases h_step
  assumption
  cases h_step
  apply valid_judgment.list
  repeat assumption
  cases h_step
  repeat assumption
