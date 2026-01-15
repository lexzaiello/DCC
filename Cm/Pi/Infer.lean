import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util
import Cm.Pi.Nat

open Expr

/-
Type inference for the list calculus.
Nil is of type "Data", and so are symbols.

Infer is a fixpoint function.
It takes itself as an argument.

(:: apply (:: infer (:: infer x)))
-/

def TData : Expr := .symbol "Data"

def TFail : Expr := .symbol "sorry"

def err : String → Expr := quote ∘ symbol

def Arr : Expr := .symbol "→"

def mk_arrow : Expr :=
  .cons both (:: (quote Arr) (:: π (:: id id)))

def infer.self : Expr :=
  :: π (:: id nil)

def infer.x (with_op : Expr := id) : Expr :=
  :: π (:: nil with_op)

/-
(:: apply (:: infer (:: infer (:: const x))))
-/
def infer_const.my_op :=
  infer.x (:: π (:: id nil))

def infer_const.my_data :=
  infer.x (:: π (:: nil id))

/-def infer_const.check_op_yes :=
  :: both (::
    (quote const)
    (:: both (::
      (quote both)
      (:: both (::
        (:: both (::
          (quote const)
          (:: both (::
            (quote apply) (:: both
            (:: infer.self (:: both
            (:: infer.self infer_const.my_data))))))))
        (:: both (::
          (quote both) (:: both (::
            (quote const) (:: both (::
            infer.self)-/

def infer_const.check_op_no := err "not a const operation"

/-def infer_const : Expr :=
  -- if the op is "const", then fetch our infer component and run that
  .cons both (:: (quote apply)
    (:: both
      (:: (:: both (:: (:: both (:: (quote eq) (:: both (:: infer_const.check_op_yes (quote infer_const.check_op_no))))) (quote .const))) infer_const.my_op)))-/

def infer_nil : Expr :=
  :: both (:: (quote apply) (:: π (:: (quote <| :: (:: eq (:: (quote TData) (quote TFail))) .nil) id)))

#eval do_step run (:: apply (:: infer_nil (:: (symbol "infer") nil)))

