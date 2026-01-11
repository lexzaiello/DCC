import Cm.Pi.Ast
import Cm.Pi.Eval

open Expr

def quote (e : Expr) : Expr :=
  (:: const e)

def apply_quoted : Expr := quote apply

/-
Skips the tail element in a projection.
-/
def skip : Expr := quote nil

/-
Utility functions for the list calculus.
-/

/-
Flips the head and nexte of a :: x (:: y ys) list, giving
:: y (:: x xs)

(:: apply (:: flip_head_tail (::

we can do this by inserting an ad-hoc
quoted π expression in a both,
and

(π head tail)

since we have the ys buffer room,
and selecting x will incur no nil,

(π id (π (:: const id) id)) - this will fetch x
and place ys after it

(π (:: const id) (π const id)) - this will fetch
y via the π const, apply yx to it, giving just y,
and the upper π will return y via id

Giving:

both (π (:: const id) (π const id)) (π id (π (:: const id) id))

both (π (:: const id) (π const id))

both xy_stuff (both (π id (π (:: const id))) id)

both 
π x (π y ys)

both (quote π) (
-/
def flip_head_next : Expr :=
  (:: both (:: (:: π (:: (:: const id) (:: π (:: const id)))) (:: π (:: id (:: π (:: (:: const id) id))))))



/-
Reverses the argument order of a combinator accepting 2 arguments.
Point-free, as well. Specify only the combinator as an argument
with no nil value.
-/
--def reverse : Expr := .cons both
  /-
    id corresponds to the function
    we're reversing the order of
    we do this by making a π
    expression where
    the first element is (quote both)
    
  π (-/

/-
Set tail args, but more point-free.
Supply only the replacement value for the tail.
-/
def set_tail_args' : Expr :=
  .cons both (::
    (quote π)
    (:: both
      (:: (:: const id) (:: both (::
        (quote const)
        id)))))

def example_set_tail_args_pointfree : Except Error Expr :=
  let replace_with := (:: (symbol "x") (:: (symbol "xs") nil))
  let replace_in := (:: (symbol "replace") nil) -- args tail

  do_step run (:: apply (:: set_tail_args' replace_with))
    >>= (fun rep =>
      do_step run (:: apply (:: rep replace_in)))

#eval example_set_tail_args_pointfree

/-
Replaces the tail of a list with the specified value.

(:: set_tail nil) (:: (:: a xs) (:: replace nil))
= (:: replace (:: a xs))
-/
def set_tail_args : Expr :=
  -- do this by generating a new π instruction
  -- we fill in the tail of the π instruction
  -- with the second argument
  -- and set the head to correspond with "replace"

  let insert_π := quote π

  -- do this by making a π instruction
  -- with id as the head (corresponds to "replace")
  -- and the tail as (:: a xs)
  -- assume here that (:: a xs) is in scope for "id"
  let my_π := :: both (::
    insert_π
    (:: both
      (:: (:: const id) (:: both (::
        (quote const)
        id)))))

  -- this inserts the literal "apply" word
  let my_apply := apply_quoted

  -- TODO: try without singleton?

  -- first element under π corresponds to replace_with
  -- second element corresponds to replace_in
  .cons both (:: my_apply (:: π (:: my_π id)))

def example_set_tail_args : Except Error Expr :=
  let replace_with := (:: (symbol "x") (:: (symbol "xs") nil))
  let replace_in := (:: (symbol "replace") nil) -- args tail
  do_step run (:: apply (:: set_tail_args (:: replace_with replace_in)))

#eval example_set_tail_args

/-
Mutates the first element of the arguments, while leaving the rest in place.

(:: map_head nil) (:: my_f (:: (:: a (:: b ... nil)) nil))
-/
def map_head_arg : Expr :=
  -- we generate a π instruction
  -- :: π (:: !my_f id)

  let insert_π := (:: const π)

  let my_π := :: both (::
    insert_π
    (:: both
      (:: id (:: const id))))

  -- this inserts the literal "apply" word
  let my_apply := apply_quoted

  .cons both (:: my_apply (:: π (:: my_π id)))

def example_map_head_arg : Except Error Expr :=
  let my_args := :: (symbol "head") (:: (symbol "b") (:: (symbol "c") nil))

  /-
    Replace the head of the list with "replaced"
  -/
  let my_f := (:: const (symbol "replace"))

  do_step run (:: apply (:: map_head_arg (:: my_f my_args)))

#eval example_map_head_arg

/-
Point-free function to map the head of a list.
This accepts only a function argument,
and it generates a π expression.

(:: apply (:: map_head my_function))

NOTE: this function does not expect nil as a final argument.
-/
def map_head: Expr :=
  :: both (:: (quote π) (:: both (:: id (quote id))))

/-
An example of using map_head that wraps the head
of a list inside a singleton value.
-/
def map_head_example : Except Error Expr :=
  let my_list := :: (symbol "head") (:: (symbol "b") (:: (symbol "c") nil))

  -- replace the head of the list with "replaced"
  let my_f := (:: const (symbol "replaced"))

  do_step run (:: apply (:: map_head my_f))
    >>= (fun map => do_step run (:: apply (:: map my_list)))

#eval map_head_example

/-
Gets the head of a list and runs some
operation on it.

This assumes the first argument is
a map and the second argument is a list.

(:: select_head nil) (:: my_f (:: (:: a (:: b ... nil)) nil))

This assumes the function argument
is not wrapped in a singleton
-/
def select_head : Expr :=
  -- Our function should be wrapped (:: f nil)
  -- like such
  let my_f := Expr.id

  -- the first element of the second
  -- argument
  -- is the head we are referring to
  let my_head := (:: π (:: id skip))

  .cons both (:: (:: const apply) (:: π (:: my_f (:: π (:: my_head nil)))))
