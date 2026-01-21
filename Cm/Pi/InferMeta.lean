import Cm.Pi.Ast

open Expr

inductive is_step_once : Expr → Expr → Prop
  | app_id       : is_step_once (:: apply (:: id x)) (:: apply x)
  | app_const    : is_step_once (:: apply (:: (:: const c) _x)) (:: apply c)
  | app_both     : is_step_once (:: apply (:: (:: both (:: f g)) x))
    (:: (:: apply (:: f x)) (:: apply (:: g x)))
  | app_π_weak_f : is_step_once (:: apply (:: (:: π (:: nil fxs)) (:: x xs)))
    (:: apply (:: fxs xs))
  | app_π_weak_g : is_step_once (:: apply (:: (:: π (:: fx nil)) (:: x xs)))
    (:: apply (:: fx x))
  | app_π_both   : is_step_once (:: apply (:: (:: π (:: fx fxs)) (:: x xs)))
    (:: (:: apply (:: fx x)) (:: apply (:: fxs xs)))
  | app_eq_yes   : a == b → is_step_once (:: apply (:: (:: (:: eq (:: fn_yes fn_no)) a) b))
    (:: apply (:: fn_yes a))
  | app_eq_no    : a ≠ b  → is_step_once (:: apply (:: (:: (:: eq (:: fn_yes fn_no)) a) b))
    (:: apply (:: fn_no b))
