import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Error
import Cm.Pi.Util
import Cm.Pi.Nat

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
More dynamic version of expected_but_found.
Curried. Expects the expected value as the first argument.

Just makes an error message.
-/

def expected_but_found' : Expr :=
  let expected := Expr.id

  (:: both (:: (quote both) (:: both (::
    (:: both (:: (quote const) (:: both (:: (quote <| symbol "expected:") expected))))
    (quote <| (:: both (:: (quote <| symbol "but found: ") id)))))))

/-
Checks whether a later curried argument
is equal to the first argument.

Outputs an expected but found error messsage otherwise.
Returns an ok with the first argument if ok.
-/
def assert_eq : Expr :=
  let my_v := Expr.id

  let eq_ok := (:: both (:: (quote const) (:: both (:: (quote Except'.s_ok) my_v))))

  (:: both
    (:: (:: both (:: (quote eq) (:: both (:: eq_ok
    (:: both (:: (quote both) (:: both (:: (quote (quote Except'.s_err)) (:: both (:: (quote apply) (:: both (:: (quote expected_but_found') my_v)))))))))))) my_v))

/-
assert_eq but it returns just the data in the ok case.
-/
def assert_eq_unwrap : Expr :=
  let my_v := Expr.id

  (:: both
    (:: (:: both (:: (quote eq) (:: both (:: (:: both (:: (quote const) my_v))
    (:: both (:: (quote both) (:: both (:: (quote (quote Except'.s_err)) (:: both (:: (quote apply) (:: both (:: (quote expected_but_found') my_v)))))))))))) my_v))

/-def expected_but_found' : Expr :=
  let expected := id
  (:: both -/

def Arr : Expr := .symbol "→"

def mk_arrow : Expr :=
  .cons both (:: (quote Arr) (:: π (:: id id)))

def infer.self : Expr :=
  :: π (:: id nil)

def infer.x (with_op : Expr := id) : Expr :=
  :: π (:: nil with_op)


def infer_nil : Expr :=
  :: both (:: (quote apply)
    (:: π (::
    (quote <|
      :: (:: eq (:: (quote <| (:: apply (:: Except'.ok TData))) (:: apply (:: expected_but_found' nil))))
      .nil)
    id)))

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

#eval try_step_n' 1000 (:: apply (:: (:: apply (:: (quote infer.assert_well_typed_unsafe) (:: infer_nil (:: const nil)))) (:: infer_nil nil)))

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

def infer_eq.assert_op_eq : Expr :=
  ((:: apply (:: assert_eq .eq)) ∘' (:: π (:: nil (:: π (:: id nil)))))

def infer_eq.assert_op_eq_seq : Expr :=
  infer.assert_seq infer_eq.assert_op_eq

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

def infer_eq.mk_future_assert_type : Expr :=
  $? (assert_eq ·')

def infer_eq.inject_future_assert_eq : Expr :=
  (:: both (:: (quote both) (:: both (:: (quote (quote apply))
      (:: both (:: (quote both) (:: both (:: (quote (quote assert_eq_unwrap)) id))))))))

def infer_eq.inject_future_infer : Expr :=
  (:: both (:: (quote both) (:: both (::
    (quote (quote both))
    (:: both (:: (quote both) (:: both (::
      (quote (quote (quote apply)))
        (:: both (:: (quote both) (:: both (::
          (quote (quote both))
          (:: both (:: (quote both) (:: both (::
            (:: both (:: (quote both) (:: both (::
              (quote (quote const))
              Expr.id))))
          (quote (quote infer.assert_well_typed_unsafe))))))))))))))))))

/-
Checks that the eq maps have the same type,
and that the result of applying the test argument into
that type is the same as the type of the actual argument.
-/
def infer_eq : Expr :=
  (infer_eq.assert_op_eq_seq
    e>=> infer_eq.eq_types
    e>=> (infer_eq.inject_future_infer ∘' infer_eq.inject_future_assert_eq))

/-
quote π is pretty common, unfortunately, so we will need to make a curried type.
π has an x map, an xs map, and produces an xs map.

the x and xs maps do not need to be the same type.

- check that the operation is π
- check that the x map is well-typed
- check that the xs map is well-typed
-/

namespace infer_test

set_option maxRecDepth 5000

example : try_step_n' 2000 (:: apply (:: (:: apply (:: (:: apply (:: infer_eq (:: infer_id (:: eq (:: id id))))) (:: infer_nil nil))) (:: infer_nil nil))) = (.ok (:: (symbol "ok") (symbol "Data"))) := rfl

example : try_step_n' 1000 (:: apply (:: (:: apply (:: infer_id (:: infer_nil id))) (:: infer_nil nil))) = (.ok (:: (symbol "ok") (symbol "Data"))) := rfl

example : (try_step_n' 500 (:: apply (:: (:: apply (:: infer_const (:: infer_nil (:: const nil)))) (:: infer_nil nil)))) = (.ok (:: (symbol "ok") (symbol "Data"))) := rfl

example : try_step_n' 1000 (:: apply (:: (:: apply (:: (quote infer.assert_well_typed_unsafe) (:: infer_nil (:: const nil)))) (:: infer_nil nil))) = (.ok (:: (symbol "ok") (symbol "Data"))) := rfl

example : try_step_n' 20 (:: apply (:: (:: apply (:: expected_but_found' const)) nil)) = .ok (:: (:: (symbol "expected:") const) (:: (symbol "but found: ") nil)) := rfl

example : try_step_n' 18 (:: apply (:: (:: apply (:: assert_eq .const)) nil)) = .ok (:: (symbol "error") (:: (:: (symbol "expected:") const) (:: (symbol "but found: ") nil))) := rfl

example : try_step_n' 20 (:: apply (:: (:: apply (:: assert_eq .const)) .const)) = .ok (:: (symbol "ok") const) := rfl

example : try_step_n' 50 (:: apply (:: infer_const.assert_op_const (:: (symbol "infer") (:: const (symbol "whatever"))))) = .ok (:: (symbol "ok") const) := rfl

example : try_step_n' 50 (:: apply (:: infer_const.assert_op_const (:: (symbol "infer") (:: (symbol "bad") (symbol "whatever"))))) = .ok (:: (symbol "error") (:: (:: (symbol "expected:") const) (:: (symbol "but found: ") (symbol "bad")))) := rfl

example : try_step_n' 50 (:: apply (:: infer_const.assert_well_typed (:: infer_nil (:: const nil)))) = .ok (:: (symbol "ok") (symbol "Data")) := rfl

example : try_step_n' 70 (:: apply (:: infer_const.assert_op_seq (:: (symbol "infer") (:: const (symbol "whatever"))))) = .ok (:: (symbol "ok") (:: (symbol "infer") (:: const (symbol "whatever")))) := rfl

example : try_step_n' 100 (:: apply (:: infer_const.assert_op_seq (:: (symbol "infer") (:: (symbol "bad") (symbol "whatever"))))) = .ok (:: (symbol "error") (:: (:: (symbol "expected:") const) (:: (symbol "but found: ") (symbol "bad")))) := rfl

example : try_step_n' 100 (:: apply (:: infer_const.assert_op_const (:: (symbol "infer") (:: (symbol "bad") (symbol "whatever"))))) = .ok (:: (symbol "error") (:: (:: (symbol "expected:") const) (:: (symbol "but found: ") (symbol "bad")))) := rfl

example : try_step_n' 200 (:: apply (:: infer_const.assert_op_ret_ty (:: infer_nil (:: const nil)))) = .ok (:: (symbol "ok") (symbol "Data")) := rfl
example : try_step_n' 200 (:: apply (:: infer_const.assert_op_ret_ty (:: infer_nil (:: (symbol "not const") nil)))) = .ok (:: (symbol "error") (:: (:: (symbol "expected:") const) (:: (symbol "but found: ") (symbol "not const")))) := rfl

example : try_step_n' 20 (:: apply (:: infer_nil (:: (symbol "infer") nil))) = .ok (:: (symbol "ok") (symbol "Data")) := rfl
example : try_step_n' 50 (:: apply (:: infer_nil (:: (symbol "infer") (symbol "whatever")))) = .ok (:: (:: (symbol "expected:") nil) (:: (symbol "but found: ") (symbol "whatever"))) := rfl

end infer_test
