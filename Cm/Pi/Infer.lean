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
Makes an except with an error messages.
-/
def raise_err (msg : String) : Expr :=
  quote <| (:: apply (:: Except'.err (symbol msg)))

/-
Accepts an "actual" value at runtime as an input,
and outputs an Except "expected {expected}, but found {acutal}"
-/
def expected_but_found (expected : Expr) : Expr :=
  (:: both (:: (quote apply)
    (:: both (:: (quote Except'.err)
    (:: both (:: (quote <| symbol s!"expected '{expected}', but found: ")
      id))))))

#eval do_step run (:: apply (:: (expected_but_found (symbol "stuff")) (symbol "other stuff")))

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

#eval do_step run (:: apply (:: (:: apply (:: expected_but_found' const)) nil))

/-
Checks whether a later curried argument
is equal to the first argument.

Outputs an expected but found error messsage otherwise.
Returns an ok with the first argument if ok.
-/
def assert_eq : Expr :=
  let my_v := Expr.id

  (:: both
    (:: (:: both (:: (quote eq) (:: both (:: (:: both (:: (quote const) (:: both (:: (quote Except'.s_ok) my_v))))
    (:: both (:: (quote apply) (:: both (:: (quote expected_but_found') my_v)))))))) my_v))

#eval try_step_n run 100 (:: apply (:: (:: apply (:: assert_eq .const)) nil))
#eval try_step_n run 100 (:: apply (:: (:: apply (:: assert_eq .const)) .const))

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

#eval try_step_n run 50 (:: apply (:: infer_const.assert_op_const (:: (symbol "infer") (:: const (symbol "whatever")))))

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

#eval try_step_n run 50 (:: apply (:: infer_const.assert_well_typed (:: infer_nil (:: const nil))))

def infer_const.assert_op_seq.wrap_ok : Expr :=
  (:: both (:: (quote apply) (:: both (:: (quote Except'.ok) id))))

/-
Asserts that the operator is const,
but gives the original arguments in the except.ok value
-/
def infer_const.assert_op_seq : Expr :=
  (:: both
    (:: (quote apply) (:: both (:: (quote Except'.bind) (:: both (::
      (:: both (:: (quote apply) (:: both (:: (quote infer_const.assert_op_const) id))))
      (:: both (:: (quote const) infer_const.assert_op_seq.wrap_ok))))))))

#eval try_step_n run 100 (:: apply (:: infer_const.assert_op_seq (:: (symbol "infer") (:: const (symbol "whatever")))))

/-
infer const produces a curried function
that checks if the argument to (:: const v) is well-typed,
then returns the type of v.
-/
def infer_const : Expr :=
  
  -- if the op is "const", then fetch our infer component and run that
  sorry

#eval do_step run (:: apply (:: infer_nil (:: (symbol "infer") nil)))
#eval do_step run (:: apply (:: infer_nil (:: (symbol "infer") (symbol "whatever"))))

