import Cm.Pi.Std.Except
import Cm.Pi.Eval
import Cm.Pi.Ast

open Expr

def TData : Expr := .symbol "Data"

def TFail : Expr := .symbol "sorry"

def expected_but_found : Expr :=
  (λ' 1 (λ' 2 (::
    (λ' 1 (::
      (var.store 1)
      (λ' 1 (:: (:: (var.store 0) <| symbol "expected:") (var.read 0)))))
        (:: (var.store 0) <| (λ' 1 (:: (:: (var.store 0) <| symbol "but found: ") (var.read 0)))))))

def assert_eq : Expr :=
  let my_v := var.read 0

  let eq_ok := (λ' 1 (:: (var.store 1) (λ' 1 (:: (:: (var.store 0) Except'.s_ok) my_v))))

  (λ' 1
    (:: (λ' 1 (:: (:: (var.store 0) eq) (λ' 1 (:: eq_ok
        (λ' 1 (λ' 2 (:: (:: (var.store 0) (:: (var.store 0) Except'.s_err))
        (λ' 1 (:: (:: (var.store 0) apply) (λ' 1 (:: (:: (var.store 0) expected_but_found) my_v)))))))))))
      my_v))

/-
assert_eq but it returns just the data in the ok case.
-/
def assert_eq_unwrap : Expr :=
  let my_v := var.read 0

  (λ' 1
    (:: (λ' 1 (:: (:: (var.store 0) eq) (λ' 1 (:: (λ' 1 (:: (var.store 1) my_v))
      (λ' 1
        (λ' 2 (::
          (:: (var.store 0) (:: (var.store 0) Except'.s_err))
          (λ' 1 (::
            (:: (var.store 0) apply)
            (λ' 1 (::
              (:: (var.store 0) expected_but_found)
              my_v)))))))))))
      my_v))

def infer.self : Expr :=
  :: π (:: id nil)

def infer.x (with_op : Expr := id) : Expr :=
  :: π (:: nil with_op)


def infer_nil : Expr :=
  (λ' 1 (:: (quote apply)
    (:: π (::
    (quote <|
      :: (:: eq (:: (quote <| (:: apply (:: Except'.ok TData))) (:: apply (:: expected_but_found nil))))
      .nil)
    id))))

example : try_step_n' 100 (:: apply (:: infer_nil (:: infer_nil nil))) = (.ok (:: Except'.s_ok TData)) := rfl

/-
Infer fully applied id.
Curry this for partial app.

Currying = dependent type.

(:: apply (:: infer (:: infer (:: id x)))) = (:: apply (:: infer (:: infer x)))
-/
def infer_id : Expr :=
  :: both (:: (quote apply)
    (:: both (::
      (:: π (:: id nil))
      (:: π (:: id id)))))

example : try_step_n' 100 (:: apply (:: infer_id (:: infer_nil nil))) = (.ok (:: Except'.s_ok TData)) := rfl

/-
Also fully applied.
(:: apply (:: infer (:: infer (:: (:: both (:: f g)) x)))) = (:: apply (:: Except'.bothM (:: (:: apply (:: infer (:: infer (:: f x)))) (:: apply (:: infer (:: infer (:: g x)))))))
-/
def infer_both.f : Expr :=
  :: π (:: nil (:: π (:: id nil)))

def infer_both.g : Expr :=
  :: π (:: nil (:: π (:: nil (:: π (:: id nil)))))

def infer_both.x : Expr :=
  :: π (:: nil (:: π (:: nil (:: π (:: nil id)))))

def infer_both.infer_f : Expr :=
  :: both (:: (quote apply) (:: both (::
    infer.self (:: both (::
    infer.self (:: both (::
    infer_both.f
    infer_both.x)))))))

def infer_both.infer_g : Expr :=
  :: both (:: (quote apply) (:: both (::
    infer.self (:: both (::
    infer.self (:: both (::
    infer_both.g
    infer_both.x)))))))

def infer_both : Expr :=
  (:: both (::
      infer_both.infer_f
      infer_both.infer_g))

#eval try_step_n' 500 (:: apply (:: infer_both (:: (symbol "global infer") (:: (symbol "f") (:: (symbol "g") (symbol "x"))))))

def assert_op (op_getter : Expr) : Expr :=
  (:: π (:: id (:: π (:: op_getter id))))

def assert_whole (whole : Expr) : Expr :=
  (:: π (:: id whole))

def match_infer (match_fn then_do : Expr) (or_else : Expr := (quote (:: apply (:: Except'.err TFail)))) : Expr :=
  (:: both (:: (quote apply)
    (:: both (::
      (:: both (:: (:: both (:: (quote eq) (:: both (::
        (quote then_do)
        (quote or_else)))))
        match_fn))
     id))))

def infer_fn' (fn : Expr) : Expr :=
  (:: both (:: (quote apply) (:: both (::
    (:: both (:: (quote apply) (:: both (::
      fn (:: both (::
      infer.self
      (:: π (:: nil (:: π (:: id nil))))))))))
      (:: π (:: nil (:: π (:: nil id))))))))

def t_curr (e : Expr) : Expr :=
  (:: both (:: (quote apply) (:: both (:: (quote (:: apply (:: curry e))) infer.self))))

def infer : Expr :=
  match_infer
    (assert_whole (quote nil))
    infer_nil
    (match_infer
      (assert_whole (quote id))
      (t_curr infer_id)
      (match_infer
        (assert_whole (quote both))
        (t_curr infer_both)
        (infer_fn' infer.self)))

set_option maxRecDepth 5000
example : try_step_n' 500 (:: apply (:: infer (:: infer (:: id nil)))) = (.ok (:: Except'.s_ok TData)) := rfl

--#eval try_step_n' 1000 (:: apply (:: infer (:: infer (:: (:: both (:: id id)) nil)))) 
