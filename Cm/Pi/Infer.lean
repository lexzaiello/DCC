import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Std.Except
import Cm.Pi.Std.Util
import Cm.Pi.Std.Nat
import Cm.Pi.Std.List

open Expr

/-
Type inference for the list calculus.
Nil is of type "Data", and so are symbols.

Infer is a fixpoint function.
It takes itself as an argument.

(:: apply (:: infer (:: infer x)))

Infer always returns an Except, where the ok value
is the type, and the error value is some error
message.
-/

def TData : Expr := .symbol "Data"

def TFail : Expr := .symbol "sorry"

/-
Expects the expected value as the first argument.
-/
/-def expected_but_found' : Except :=
  (λ' 2 (var.read 1 ((quote <| symbol "expected:")-/

/-
More dynamic version of expected_but_found.
Curried. Expects the expected value as the first argument.

Just makes an error message.
-/

def expected_but_found : Expr :=
  (λ' 1 (λ' 2 (::
    (λ' 1 (::
      (var.store 1)
      (λ' 1 (:: (:: (var.store 0) <| symbol "expected:") (var.read 0)))))
        (:: (var.store 0) <| (λ' 1 (:: (:: (var.store 0) <| symbol "but found: ") (var.read 0)))))))

/-
Checks whether a later curried argument
is equal to the first argument.

Outputs an expected but found error messsage otherwise.
Returns an ok with the first argument if ok.
-/

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

/-
Note: this is not safe generally.
Asserts that the argument is well-typed.
Do not run this unless chaining.
-/
def infer.assert_well_typed_unsafe :=
  (:: both (::
    (quote apply)
    (:: both (::
        infer.self
        (:: both (::
          infer.self
          infer.x))))))

/-
(:: apply (:: infer (:: infer (:: const x))))
-/
def infer_const.my_op :=
  infer.x (:: π (:: id nil))

def infer_const.my_data :=
  infer.x (:: π (:: nil id))

/-
With all args in scope.

Checks that the operator is "const".
-/
def infer_const.assert_op_const :=
  (:: apply (:: assert_eq .const)) ∘' infer_const.my_op

/-
With all args in scope.

Checks that the argument to const is well-typed.
-/
def infer_const.assert_well_typed :=
  (:: both (::
    (quote apply)
    (:: both (::
        infer.self
        (:: both (::
          infer.self
          infer_const.my_data))))))

def infer_const.assert_op_seq.wrap_ok : Expr :=
  (:: both (:: (quote apply) (:: both (:: (quote Except'.ok) id))))

def infer.assert_seq (e : Expr) : Expr :=
  (:: both
    (:: (quote apply) (:: both (:: (quote Except'.bind) (:: both (::
      (:: both (:: (quote apply) (:: both (:: (quote e) id))))
      (:: both (:: (quote const) infer_const.assert_op_seq.wrap_ok))))))))

/-
Asserts that the operator is const,
but gives the original arguments in the except.ok value
-/
def infer_const.assert_op_seq : Expr :=
  infer.assert_seq infer_const.assert_op_const

/-
infer const produces a curried function
that checks if the argument to (:: const v) is well-typed,
then returns the type of v.
-/
def infer_const.assert_op_ret_ty : Expr :=
  Except'.bind ∘' (:: both (::
        ($? <| (quote infer_const.assert_op_seq) ·')
        (quote infer_const.assert_well_typed)))

example : try_step_n' 1000 (:: apply (:: (:: apply (:: (quote infer.assert_well_typed_unsafe) (:: infer_nil (:: const nil)))) (:: infer_nil nil))) = (.ok (:: (symbol "ok") (symbol "Data"))) := rfl

def infer_const.cnst_out_ty : Expr :=
  (:: both (:: (quote const)
    (:: both (:: (quote const)
      (:: both (:: (quote apply) (:: both (::
        (quote infer_const.assert_op_ret_ty)
        id))))))))

def infer_const.future_infer : Expr :=
  (quote infer.assert_well_typed_unsafe)

def infer_const.bind_args : Expr :=
  (:: both (:: (quote both) (:: both (:: infer_const.future_infer
        infer_const.cnst_out_ty))))

def infer_const.future_apply : Expr :=
  (:: both (:: (quote both)
    (:: both (:: (quote (quote Except'.bind))
      (:: both (:: (quote both) (:: both (:: infer_const.future_infer
        infer_const.cnst_out_ty))))))))

/-
(:: apply (:: (:: apply (:: infer_const (:: infer (:: const data)))) (:: infer other_data)))
-/
def infer_const : Expr :=
  (:: both (:: (quote both) (:: both (::
    (quote (quote apply))
    infer_const.future_apply))))

/-
id is a curried infer rule.
it will just run infer on whatever comes next.
-/
def infer_id.my_op : Expr :=
  (:: π (:: nil id))

def infer_id.assert_op_id : Expr :=
  ((:: apply (:: assert_eq .id)) ∘' (:: π (:: nil id)))

def infer_id.bind_args : Expr :=
  (:: both
    (:: ($? <| (quote infer_id.assert_op_id) ·')
      (quote (quote infer.assert_well_typed_unsafe))))

def infer_id : Expr :=
  (:: both (:: (quote apply) (:: both (:: (quote Except'.bind) infer_id.bind_args))))

/-
eq is not well-typed unless the parameters are supplied.
I think this is fine ish, but maybe too restrictive.

We default to the yes case, so infer_eq is just the type of the yes case.
We assert that the type of the no_case is the same.

(:: apply (:: infer_eq (:: global_infer (:: eq (:: yes_case no_case)))))
-/

def infer.assert_op_seq (op : Expr) :=
  infer.assert_seq <| ((:: apply (:: assert_eq op)) ∘' (:: π (:: nil (:: π (:: id nil)))))

def infer_eq.assert_op_eq_seq : Expr :=
  infer.assert_op_seq .eq

def infer_eq.yes_case : Expr :=
  (:: π (:: nil (:: π (:: nil (:: π (:: id nil))))))

def infer_eq.no_case : Expr :=
  (:: π (:: nil (:: π (:: nil (:: π (:: nil id))))))

def infer_eq.yes_type : Expr :=
  (:: both (:: (quote apply)
    (:: both (:: infer.self
      (:: both (:: infer.self
      infer_eq.yes_case))))))

def infer_eq.no_type : Expr :=
  (:: both (:: (quote apply)
    (:: both (:: infer.self
      (:: both (:: infer.self
      infer_eq.no_case))))))

/-
Checks that the yes and no case types are equal,
then returns them.
-/
def infer_eq.eq_types : Expr :=
  (:: both (:: (quote apply)
        (:: both (::
          (:: both (:: (quote apply)
            (:: both (::
              (quote assert_eq)
              infer_eq.yes_type))))
          infer_eq.no_type))))

/-
Accepts the yes type eq assert as an argument.
Must create a new function that
runs infer on the next argument and plugs
it into the assert

Note that since eq has functions as the cases,
we will get a new infer function from the yes case.

Future_infer works on whatever assertion argument it is passed.
-/

/-
This is for the last eq argument.
-/
def infer_eq.future_infer₀ : Expr :=
  (:: both (:: (quote both) (:: both (::
    (quote (quote apply))
    (:: both (:: (quote both) (:: both (::
      const -- this wraps the eq assertions
      (quote (Except'.unwrap ∘' infer.assert_well_typed_unsafe)) -- this infers the future argument
      ))))))))

def infer_eq.do_future_infer : Expr :=
  (:: both (:: (quote both)
    (:: both (::
      (quote (quote apply))
      (:: both (:: (quote both) (:: both (::
        (:: both (:: (quote const) id)) -- this wraps the eq assertions
        (quote id)))))))))

/-
This is for the first eq data argument.
-/
def infer_eq.future_infer₁ : Expr :=
  (:: both (:: (quote (quote apply))
    (:: both (:: (quote assert_eq) (:: both (:: (quote apply) (:: (quote infer_eq.do_future_infer) id)))))))

/-
with third argument type as the input.
-/

def infer_eq.inject_future_assert_eq : Expr :=
  (:: both (:: (quote both) (:: both (:: (quote (quote apply))
      (:: both (:: (quote both) (:: both (:: (quote (quote assert_eq_unwrap)) id))))))))

def infer_eq.inject_future_infer : Expr :=
  (mk_both' 0 ∘ mk_both' 1) (:: (qn' 2 both)
    (:: (qn' 3 apply)
        (:: (qn' 2 both) (::
            (:: (qn' 2 const) Expr.id)
            (qn' 2 infer.assert_well_typed_unsafe)))))

example : (quote (quote infer.assert_well_typed_unsafe)) = (q' q' infer.assert_well_typed_unsafe) := rfl

/-
Checks that the eq maps have the same type,
and that the result of applying the test argument into
that type is the same as the type of the actual argument.
-/
def infer_eq : Expr :=
  (infer_eq.assert_op_eq_seq
    e>=> infer_eq.eq_types
    e>=> (infer_eq.inject_future_infer ∘' infer_eq.inject_future_assert_eq))

def infer_both.f : Expr :=
  :: π (:: nil (:: π (:: nil (:: π (:: id nil)))))

def infer_both.g : Expr :=
  :: π (:: nil (:: π (:: nil (:: π (:: nil id)))))

example : try_step_n' 1000 (:: apply (:: infer_both.g (:: infer_nil (:: both (:: id id))))) = (.ok .id) := rfl
example : try_step_n' 1000 (:: apply (:: infer_both.f (:: infer_nil (:: both (:: const id))))) = (.ok .const) := rfl

/-
With all args in scope.

Inserts future arg in (:: apply (:: (eval infer_both.g) (:: infer_global arg)))
position.
-/
def infer_both.fn_with_global_infer (fn : Expr) : Expr :=
  :: both (:: (quote both)
    (:: both (:: (quote (quote apply))
    (:: both (:: (quote both)
      (:: both (::
        (:: both (:: (quote const) (infer.self)))
        (:: both (:: (quote both) (:: both (::
          (:: both (:: (quote const) (infer.self)))
            (:: both (:: (quote both) (:: both (::
              (:: both (:: (quote const) fn))
              (quote id))))))))))))))))

example : try_step_n' 1000 (:: apply (:: (:: apply (:: (infer_both.fn_with_global_infer infer_both.f) (:: (symbol "global infer") (:: both (:: (symbol "f") id))))) (symbol "my data"))) = (.ok (:: apply (:: (symbol "global infer") (:: (symbol "global infer") (:: (symbol "f") (symbol "my data")))))) := rfl

def infer_both.body : Expr :=
  (:: apply (:: curry
      (:: both (:: (quote apply) (:: both (::
        (quote Except'.bothM) (:: both (::
          (:: both (:: (quote apply) (:: both (::
            (args.read 0 <| infer_both.fn_with_global_infer infer_both.f)
            (args.read 1 id))))) -- infer (:: f l)
          (:: both (:: (quote apply) (:: both (::
            (args.read 0 <| infer_both.fn_with_global_infer infer_both.g)
            (args.read 1 id))))))))))))) -- infer (:: g l)

def infer_both : Expr :=
  infer.assert_op_seq .both
    e>=> infer_both.body

set_option maxRecDepth 5000
example : try_step_n' 1000 (:: apply (:: (:: apply (:: infer_both (::
  (quote (:: apply (:: Except'.ok (symbol "ok")))) (:: both (:: id id)))))
  (symbol "my data"))) = (.ok (:: (symbol "ok") (:: (symbol "ok") (symbol "ok")))) := rfl

def infer_apply : Expr :=
  infer.assert_op_seq .both
  e>=> (:: apply (:: curry (:: both (::
    (quote apply) (:: both (::
      (args.read 0 infer.self) (:: both (::
        (args.read 0 infer.self)
        (args.read 1 id)))))))))

def infer_π.body : Expr :=
  (:: apply (:: curry
      (:: both (:: (quote apply) (:: both (::
        (quote Except'.bothM) (:: both (::
          (:: both (:: (quote apply) (:: both (::
            (args.read 0 <| infer_both.fn_with_global_infer infer_both.f)
            (args.read 1 (:: π (:: id nil))))))) -- infer (:: f (:: x _xs))
          (:: both (:: (quote apply) (:: both (::
            (args.read 0 <| infer_both.fn_with_global_infer infer_both.g)
            (args.read 1 (:: π (:: nil id))))))))))))))) -- infer (:: g (:: _ xs))

def infer_π : Expr :=
  infer.assert_op_seq .π
    e>=> infer_π.body

/-
(:: apply (:: (match_infer infer_π infer_nil) (:: infer_nil nil)))
= (:: apply (:: Except'.ok TData))
-/
def match_infer (match_fn then_do or_else : Expr) : Expr :=
  (:: both (:: (quote apply)
    (:: both (::
      (:: both (:: (:: both (:: (quote eq) (:: both (::
        (quote then_do)
        (quote or_else)))))
        match_fn))
     id))))

/-
(:: apply (:: infer (:: infer nil)))
(:: apply (:: infer (:: infer (:: apply 
-/
def infer : Expr :=
  match_infer
    (:: π (:: id (quote nil)))
    infer_nil
    (match_infer
      (:: π (:: id (:: π (:: (quote apply) id))))
      infer_apply
      (match_infer
        (:: π (:: id (:: π (:: (quote π) id))))
        infer_π
        (match_infer
          (:: π (:: id (:: π (:: (quote both) id))))
          infer_both
          (match_infer
            (:: π (:: id (:: π (:: (quote const) id))))
            infer_const
            (match_infer
              (:: π (:: id (quote id)))
              infer_id
              (quote (:: apply (:: Except'.err TFail))))))))

example : try_step_n' 100 (:: apply (:: infer (:: infer nil))) = .ok (:: Except'.s_ok TData) := rfl

example : try_step_n' 500 (:: apply (:: infer (:: infer (:: apply (:: id nil))))) = .ok (:: Except'.s_ok TData) := rfl

#eval try_step_n' 500 (:: apply (:: infer (:: infer (:: apply (:: (:: both (:: id id)) nil)))))

namespace infer_test

set_option maxRecDepth 5000

example : try_step_n' 2000 (:: apply (:: (:: apply (:: (:: apply (:: infer_eq (:: infer_id (:: eq (:: id id))))) (:: infer_nil nil))) (:: infer_nil nil))) = (.ok (:: (symbol "ok") (symbol "Data"))) := rfl

example : try_step_n' 1000 (:: apply (:: (:: apply (:: infer_id (:: infer_nil id))) (:: infer_nil nil))) = (.ok (:: (symbol "ok") (symbol "Data"))) := rfl

example : (try_step_n' 500 (:: apply (:: (:: apply (:: infer_const (:: infer_nil (:: const nil)))) (:: infer_nil nil)))) = (.ok (:: (symbol "ok") (symbol "Data"))) := rfl

example : try_step_n' 1000 (:: apply (:: (:: apply (:: (quote infer.assert_well_typed_unsafe) (:: infer_nil (:: const nil)))) (:: infer_nil nil))) = (.ok (:: (symbol "ok") (symbol "Data"))) := rfl

example : try_step_n' 20 (:: apply (:: (:: apply (:: expected_but_found const)) nil)) = .ok (:: (:: (symbol "expected:") const) (:: (symbol "but found: ") nil)) := rfl

example : try_step_n' 50 (:: apply (:: (:: apply (:: assert_eq .const)) nil)) = .ok (:: (symbol "error") (:: (:: (symbol "expected:") const) (:: (symbol "but found: ") nil))) := rfl

example : try_step_n' 20 (:: apply (:: (:: apply (:: assert_eq .const)) .const)) = .ok (:: (symbol "ok") const) := rfl

example : try_step_n' 50 (:: apply (:: infer_const.assert_op_const (:: (symbol "infer") (:: const (symbol "whatever"))))) = .ok (:: (symbol "ok") const) := rfl

example : try_step_n' 50 (:: apply (:: infer_const.assert_op_const (:: (symbol "infer") (:: (symbol "bad") (symbol "whatever"))))) = .ok (:: (symbol "error") (:: (:: (symbol "expected:") const) (:: (symbol "but found: ") (symbol "bad")))) := rfl

example : try_step_n' 50 (:: apply (:: infer_const.assert_well_typed (:: infer_nil (:: const nil)))) = .ok (:: (symbol "ok") (symbol "Data")) := rfl

example : try_step_n' 100 (:: apply (:: infer_const.assert_op_seq (:: (symbol "infer") (:: const (symbol "whatever"))))) = .ok (:: (symbol "ok") (:: (symbol "infer") (:: const (symbol "whatever")))) := rfl

example : try_step_n' 100 (:: apply (:: infer_const.assert_op_seq (:: (symbol "infer") (:: (symbol "bad") (symbol "whatever"))))) = .ok (:: (symbol "error") (:: (:: (symbol "expected:") const) (:: (symbol "but found: ") (symbol "bad")))) := rfl

example : try_step_n' 100 (:: apply (:: infer_const.assert_op_const (:: (symbol "infer") (:: (symbol "bad") (symbol "whatever"))))) = .ok (:: (symbol "error") (:: (:: (symbol "expected:") const) (:: (symbol "but found: ") (symbol "bad")))) := rfl

example : try_step_n' 200 (:: apply (:: infer_const.assert_op_ret_ty (:: infer_nil (:: const nil)))) = .ok (:: (symbol "ok") (symbol "Data")) := rfl
example : try_step_n' 200 (:: apply (:: infer_const.assert_op_ret_ty (:: infer_nil (:: (symbol "not const") nil)))) = .ok (:: (symbol "error") (:: (:: (symbol "expected:") const) (:: (symbol "but found: ") (symbol "not const")))) := rfl

example : try_step_n' 20 (:: apply (:: infer_nil (:: (symbol "infer") nil))) = .ok (:: (symbol "ok") (symbol "Data")) := rfl
example : try_step_n' 50 (:: apply (:: infer_nil (:: (symbol "infer") (symbol "whatever")))) = .ok (:: (:: (symbol "expected:") nil) (:: (symbol "but found: ") (symbol "whatever"))) := rfl

end infer_test
