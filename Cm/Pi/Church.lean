import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util
import Cm.Pi.Curry

open Expr

/-
zero f x = x

This expects that at most two arguments are applied,
with no terminal nil value.
-/
def zero : Expr := :: π (:: (:: const id) id)

/-
succ n f x = f (n f x)

(:: (:: succ n) (:: f x)) = (:: f (:: n f x))

takes in n as the only positional argument,
the accepts f, x as the next positional arguments
-/
def succ : Expr :=
  let n := Expr.id

  -- we make a new "binder" by making a quoted π expression.
  -- NOT evaluating it.

  -- assuming f x args are like (:: f x),
  -- then we can copy and create a const / quotation
  -- to delete the nil value
  -- assuming f x are in scope
  -- head is f, rest is x
  -- TODO: this might cause the apply both issue. really annoying
  -- we will want :: apply (:: f (:: apply (:: n (:: f x))))
  -- this is a quoted expression that we are generating.
  let f_beginning := quote (:: π (:: const (:: const nil)))

  -- assuming n is the only positional argument in scope
  -- we are generating a "both" expression
  -- (:: (quote both) n
  let insert_id := quote id
  let insert_apply := quote apply
  let nfx := :: both (::
    insert_apply
    (:: both (::
      .id
      insert_id)))
  
  
  -- we want to make "both (π 

  let f_root := (:: π (:: (quote id) (:: π (:: id (:: const nil)))))

  -- nfx is all of the arguments anyway
  let nfx := :: both (:: (:: const apply) (:: π (:: id (:: π (:: id id)))))

  let f_nfx := .cons both (:: f_root nfx)

  .cons both (.cons (:: const apply) f_nfx)

def example_zero_church : Except Error Expr :=
  let my_fn := :: const (symbol "const")
  let my_x  := :: const (symbol "intact")

  do_step run (:: apply (:: zero (:: my_fn my_x)))

def example_zero_church' : Except Error Expr :=
  let my_fn := Expr.id
  let my_x  := :: const (symbol "intact")

  do_step run (:: apply (:: zero (:: my_fn my_x)))

#eval example_zero_church'
  >>= step_apply

#eval example_zero_church
  >>= step_apply

def example_succ_church : Except Error Expr :=
  let my_fn := Expr.id
  let my_x := :: const (symbol "my_data")

  do_step run (:: apply (:: succ (:: zero (:: my_fn my_x))))

#eval example_succ_church

/-
Partially applying zero by only supplying one argument.
:: then_cons x = :: both (:: (:: const f) id)

(:: (:: then_cons f) x) = (:: f x)

For currying, we want the opposite.
We want append?

We want something we can do to our function to make it curry.

then_cons will cons the argument onto later arguments


(:: (:: then_cons (:: (:: then_cons f) x)) y) =

-/
/-def example_curry : Except Error Expr :=
  let my_fn := Expr.id
  let my_x  := (symbol "intact")

  -- curry twice
  -- so now we should be able to plug
  -- stuff in
  do_step run (:: apply (:: curry zero))
    >>= (fun c => do_step run (:: apply ))

#eval example_curry-/
