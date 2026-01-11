import Cm.Pi.Ast
import Cm.Pi.Eval

open Expr

def quote (e : Expr) : Expr :=
  (:: const (:: e nil))

def apply_quoted : Expr := quote apply

/-
Skips the tail element in a projection.
-/
def skip : Expr := quote nil

def singleton_later : Expr :=
  :: both (:: id (:: const (:: nil nil)))

/-
Utility functions for the list calculus.
-/

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
      (:: (:: const (:: id nil)) (:: both (::
        (quote const)
        id)))))

  let my_π := :: both (::
    insert_π
    (:: both
      (:: (:: const (:: id nil)) (:: both (::
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
  do_step run (:: apply (:: (:: set_tail_args nil) (:: replace_with replace_in)))

#eval example_set_tail_args

/-
Mutates the first element of the arguments, while leaving the rest in place.

(:: map_head nil) (:: my_f (:: (:: a (:: b ... nil)) nil))
-/
def map_head_arg : Expr :=
  -- we generate a π instruction
  -- :: π (:: !my_f id)

  let insert_π := (:: const (:: π nil))

  let my_π := :: both (::
    insert_π
    (:: both
      (:: id (:: const (:: id nil)))))

  let my_π_singleton := Expr.cons both
    (.cons my_π (.cons const (.cons nil nil)))

  -- this inserts the literal "apply" word
  let my_apply := apply_quoted

  .cons both (:: my_apply (:: π (:: my_π_singleton id)))

def example_map_head_arg : Except Error Expr :=
  let my_args := :: (symbol "head") (:: (symbol "b") (:: (symbol "c") nil))

  -- wrap the head as a singleton
  -- by inserting nil at the end
  let my_f := :: both (:: id (:: const (:: nil nil)))

  do_step run (:: apply (:: (:: map_head_arg nil) (:: my_f my_args)))

#eval example_map_head_arg

/-
Mutates the first element of a list, while leaving the rest in place.

(:: map_head nil) (:: my_f (:: (:: a (:: b ... nil)) nil))

TODO: is the extra apply even necessary here?
-/
def map_head: Expr :=
  -- we generate a π instruction
  -- :: π (:: !my_f id)

  let insert_π := (:: const (:: π nil))

  -- π id (const id) gets the mapper function,
  -- then inserts literal "id" after
  -- an extra apply / indirection is
  -- required, since
  -- we are using the list twice
  -- this generates :: π (:: the_map id)
  -- id refers to the mapper
  -- :: π (:: my_map id)
  -- note: there should be an extra id
  -- π should have another π
  -- to select the first element,
  -- the list
  let my_π' := :: both (::
    insert_π
    (:: both
      (:: id (:: const (:: id nil)))))
  let my_π_f := :: both (::
    insert_π
    (:: both (::
      my_π'
      (:: const (:: nil nil)))))

  let my_π_singleton := Expr.cons both
    (.cons my_π_f (.cons const (.cons nil nil)))

  -- this inserts the literal "apply" word
  let my_apply := apply_quoted

  .cons both (:: my_apply (:: π (:: my_π_singleton id)))

/-
An example of using map_head that wraps the head
of a list inside a singleton value.
-/
def map_head_example : Except Error Expr :=
  let my_list := :: (symbol "head") (:: (symbol "b") (:: (symbol "c") nil))

  -- wrap the head as a singleton
  -- by inserting nil at the end
  let my_f := :: both (:: id (:: const (:: nil nil)))

  do_step run (:: apply (:: (:: map_head nil) (:: my_f (:: my_list nil))))

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
  let my_f := singleton_later

  -- the first element of the second
  -- argument
  -- is the head we are referring to
  let my_head := (:: π (:: id skip))

  .cons both (:: (:: const (:: apply nil)) (:: π (:: my_f (:: π (:: my_head nil)))))
