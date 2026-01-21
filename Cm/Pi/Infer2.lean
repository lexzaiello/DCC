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
(:: apply (:: infer_both (:: infer_global (:: (:: f g) x))))
-/
def infer_both.x : Expr :=
  :: π (:: nil (:: π (:: nil id)))

def infer_both.infer_f : Expr :=
  (:: both (:: (quote apply) (:: both (::
    (args.read 0 (:: π (:: id nil))) (:: both (::
    (args.read 0 (:: π (:: id nil))) (:: both (::
    (args.read 0 (:: π (:: nil (:: π (:: id nil))))) (:: π (:: nil id))))))))))

def infer_both.infer_g : Expr :=
  (:: both (:: (quote apply) (:: both (::
    (args.read 0 (:: π (:: id nil))) (:: both (::
    (args.read 0 (:: π (:: id nil))) (:: both (::
    (args.read 0 (:: π (:: nil (:: π (:: nil id))))) (:: π (:: nil id))))))))))

/-
(:: apply (:: infer_both (:: infer_global (:: (:: f g) x))))
-/
def infer_both : Expr :=
  (:: apply (:: curry (:: apply (:: curry (:: both (:: (quote apply)
    (:: both (::
      (quote Except'.bothM)
      (:: both (:: infer_both.infer_f infer_both.infer_g))))))))))

def infer_curr.global_infer : Expr :=
  (args.read 0 (:: π (:: id nil)))

def infer_π.infer_f : Expr :=
  (:: both (:: (quote apply) (:: both (::
    (infer_curr.global_infer) (:: both (::
    (infer_curr.global_infer) (:: both (::
    (args.read 0 (:: π (:: nil (:: π (:: id nil))))) (:: π (:: nil (:: π (:: id nil))))))))))))

def infer_π.infer_g : Expr :=
  (:: both (:: (quote apply) (:: both (::
    (infer_curr.global_infer) (:: both (::
    (infer_curr.global_infer) (:: both (::
    (args.read 0 (:: π (:: nil (:: π (:: nil id))))) (:: π (:: nil (:: π (:: nil id))))))))))))

def infer_π : Expr :=
  (:: apply (:: curry (:: apply (:: curry (:: both (:: (quote apply)
    (:: both (::
      (quote Except'.bothM)
      (:: both (:: infer_π.infer_f infer_π.infer_g))))))))))

/-
(:: apply (:: infer (:: infer (:: (:: const x) y))))
= (:: apply (:: infer (:: infer x)))
-/
def infer_const : Expr :=
  (:: apply (:: curry (:: apply (:: curry
    (:: both (:: (quote apply) (:: both (::
      infer_curr.global_infer (:: both (::
      infer_curr.global_infer (args.read 0 (:: π (:: nil id)))))))))))))

/-
(:: apply (:: infer (:: infer (:: (:: (:: (:: eq (:: yes_case no_case)) test) val)))))
= (:: (:: (:: eq (:: (:: apply (:: infer (:: infer yes_case test)) (:: infer (:: infer no_case val))))) test) val)

currying twice gets nil applied.
-/
def infer_eq.yes_case : Expr :=
  (:: both (:: (quote both) (:: both (::
    (quote (quote apply)) (:: both (:: (quote both) (:: both (::
    (:: both (:: (quote const) infer_curr.global_infer)) (:: both (::
    (quote both)
    (:: both (:: (:: both (:: (quote const) infer_curr.global_infer)) (:: both (:: (quote both)
      (:: both (:: (:: both (:: (quote const) (args.read 0 (:: π (:: nil (:: π (:: id nil))))))) (quote id)))))))))))))))))

def infer_eq.no_case : Expr :=
  (:: both (:: (quote both) (:: both (::
    (quote (quote apply)) (:: both (:: (quote both) (:: both (::
    (:: both (:: (quote const) infer_curr.global_infer)) (:: both (::
    (quote both)
    (:: both (:: (:: both (:: (quote const) infer_curr.global_infer)) (:: both (:: (quote both)
      (:: both (:: (:: both (:: (quote const) (args.read 0 (:: π (:: nil (:: π (:: nil id))))))) (quote id)))))))))))))))))

def infer_eq.test_val : Expr :=
  (:: π (:: nil (:: π (:: nil id))))

def infer_eq : Expr :=
  (:: apply (:: curry
    (:: apply (:: curry
      (:: both (::
        (:: both (:: (quote eq)
          (:: both (:: infer_eq.yes_case infer_eq.no_case)))) (:: π (:: nil id))))))))

set_option maxRecDepth 1000
example : try_step_n' 100 (:: apply (:: (:: apply (:: (:: apply (:: (:: apply (:: curry (:: apply (:: curry infer_both.infer_f)))) (symbol "infer_global"))) (:: (symbol "f") (symbol "g")))) (symbol "x"))) = (.ok (:: apply (:: (symbol "infer_global") (:: (symbol "infer_global") (:: (symbol "f") (symbol "x")))))) := rfl

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

def t_curr (n : ℕ) (e : Expr) : Expr :=
  (:: both (:: (quote apply) (:: both (:: (quote (:: apply ((List.replicate n curry).foldr
    (fun e acc => :: e acc) e))) infer.self))))

def infer : Expr :=
  match_infer
    (assert_whole (quote nil))
    infer_nil
    (match_infer
      (assert_whole (quote id))
      (t_curr 1 infer_id)
      (match_infer
        (assert_whole (quote both))
        (:: both (:: (quote apply) (:: both (:: (quote infer_both) infer.self))))
        (match_infer
          (assert_whole (quote π))
          (:: both (:: (quote apply) (:: both (:: (quote infer_π) infer.self))))
          (match_infer
            (assert_whole (quote const))
            (:: both (:: (quote apply) (:: both (:: (quote infer_const) infer.self))))
            (match_infer
              (assert_whole (quote eq))
              (:: both (:: (quote apply) (:: both (:: (quote infer_eq) infer.self))))
              (infer_fn' infer.self))))))

set_option maxRecDepth 10000

example : try_step_n' 2000 (:: apply (:: infer (:: infer (:: (quote nil) nil)))) = (.ok (:: Except'.s_ok TData)) := rfl

example : try_step_n' 2000 (:: apply (:: infer (:: infer (:: (:: (:: eq (:: (quote nil) (quote (symbol "hi")))) nil) nil)))) = (.ok (:: Except'.s_ok TData)) := rfl

example : try_step_n' 500 (:: apply (:: infer (:: infer (:: id nil)))) = (.ok (:: Except'.s_ok TData)) := rfl

example : try_step_n' 500 (:: apply (:: (:: apply (:: (:: apply (:: infer (:: infer both))) (:: id id))) nil)) = (.ok (:: Except'.s_ok (:: TData TData))) := rfl

example : try_step_n' 500 (:: apply (:: infer (:: infer (:: (:: both (:: id id)) nil)))) = (.ok (:: (symbol "ok") (:: (symbol "Data") (symbol "Data")))) := rfl

example : try_step_n' 500 (:: apply (:: infer (:: infer (:: (:: π (:: id id)) (:: nil nil))))) = (.ok (:: (symbol "ok") (:: (symbol "Data") (symbol "Data")))) := rfl

example : try_step_n' 500 (:: apply (:: infer (:: infer (:: (:: const nil) nil)))) = (.ok (:: (symbol "ok") (symbol "Data"))) := rfl
