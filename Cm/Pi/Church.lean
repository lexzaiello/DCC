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
How do we get rid of this nil value?
make a new both that allows us to insert n f x

Let's keep this for now. We'll clean up later.
-/
#eval do_step run (:: apply (:: (:: both (:: (:: const apply) (:: π (:: const id)))) (:: (symbol "const") (symbol "xs"))))

/-
succ n f x = f (n f x)

(:: (:: succ n) (:: f x)) = (:: f (:: n f x))

takes in n as the only positional argument,
the accepts f, x as the next positional arguments
-/

def succ.f_beginning : Expr :=
  quote (:: both (:: (:: const apply) (:: π (:: const id))))

def succ.nfx : Expr :=
  :: both (::
    (quote apply)
    (:: both (::
      const -- this should quote the current f TODO: maybe another quoted both required here?
      (quote id))))



def succ : Expr :=
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
  -- f is in a nice spot to insert the apply for itself
  -- prepending apply
  -- TODO: not sure if we need to quote this?
  -- this will properly drop the coming nil after f, but I'm not 100% sure why we need to quote it.
  -- this produces just f, but the quoted instructions for the future arguments
  -- this does not contain the very beginning apply just yet
  let f_beginning := quote (:: both (:: (:: const apply) (:: π (:: const id))))

  -- assuming n is the only positional argument in scope, this is
  -- is essentially just then_cons
  -- assuming n is the only positional argument in scope
  -- we are generating a "both" expression
  -- (:: (quote both) n
  -- this produces :: apply (:: n fx)
  -- gets passed n, then later appends
  let nfx := (:: both (:: (:: const apply) (:: both (:: (:: const then_cons) id))))
  /-let nfx := :: both (::
    (quote apply)
    (:: both (::
      const -- this should quote the current f TODO: maybe another quoted both required here?
      (quote id))))-/

  -- we are missing an apply.
  -- this apply is wrong.
  -- at the very least, we are missing a both
  -- we're closer, but still missing a quoted apply after both
  let f_nfx_call := (:: both (:: f_beginning nfx))

  let data := .cons both (:: (quote both) f_nfx_call)

  -- wrap the whole thing inside an apply
  -- and same with the inner both
  -- we need to double quote those applies though,
  -- since they get popped off twice.

  data

-- f = id
-- x = (symbol "hi")
-- so this will create a new expression with f on the left
-- :: (:: both (:: (:: const apply) (:: π (:: const id)))) (:: π (:: (:: const id) id))
#eval do_step run (:: apply (:: succ (symbol "n")))
#eval do_step run (:: apply (:: zero (:: id (symbol "x"))))
#eval do_step run (:: apply (:: (:: apply (:: succ zero)) (:: id (symbol "x"))))
  >>= (fun c => do_step run (:: apply c))
  >>= (fun c => do_step run (:: apply c))
#eval do_step run (:: apply (:: (:: apply (:: succ (symbol "n"))) (:: (symbol "f") (symbol "x"))))

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
