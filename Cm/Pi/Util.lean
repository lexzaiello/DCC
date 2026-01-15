import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval

/-
Utility functions for the list calculus.
-/

open Expr

/-
Forces an expression to be evaluated immediately.
-/
def apply_now (e : Expr) : Expr :=
  :: both (:: (:: const apply) e)

def quote (e : Expr) : Expr :=
  (:: const e)

/-
Composition of functions:
f ∘ g data = f(g(data))

(:: both (:: (quote apply) (:: (quote f)
  (:: both
    (:: (quote apply)
      (quote g)
      id)))))
-/

infixr:65 "∘'" => (fun (f : Expr) (g : Expr) => (:: both (:: (quote apply)
  (:: both (:: (quote f)
  (:: both
    (:: (quote apply) (:: both (::
      (quote g)
      Expr.id)))))))))

notation "$!" => Expr.cons apply

/-
(f ·') = (:: both (:: f id))

These operators do not force evaluation.
-/
postfix:60 "·'" => (fun f => (:: both (:: f id)))

prefix:60 "·'" => (fun f => (:: both (:: id f)))

#eval do_step run (:: apply (::
  ((·' (quote (symbol "another")) ) ∘'
  ((quote (symbol "prefix")) ·')) (symbol "hi")))

/-
|> pipelining
(f x)
  |> my_op = (:: apply (:: my_op (:: apply (f x))))
-/
infixl:60 "|>'" => (fun x => (fun y => (:: apply (:: y (:: apply x)))))

#eval do_step run ((::
  ((·' (quote (symbol "another")) ) ∘'
  ((quote (symbol "prefix")) ·')) (symbol "hi")) |>' Expr.id)

/-
<| pipelining
my_op
  <| (f x) = (:: apply (:: my_op (:: apply (f x))))
-/
infixr:60 "<|'" => (fun x y => y |>' x)

#eval do_step run (Expr.id <|' (::
  ((·' (quote (symbol "another")) ) ∘'
  ((quote (symbol "prefix")) ·')) (symbol "hi")))

def apply_quoted : Expr := quote apply

/-
Skips the tail element in a projection.
-/
def skip : Expr := quote nil

/-
Lazy cons. This accepts exactly one value.

:: then_cons x = :: both (:: (:: const x) id)

This will prepend the value to the next argument.

Assumes that nil is not passed, and the argument is the value
to prepend.
-/
def then_cons : Expr :=
  .cons both (:: (quote both) (:: both (:: const (quote id))))

/-
Lazy append. Lazy cons with the order reversed.


(:: apply (:: apply (:: then_append f)) b) = (:: b f)
-/
def then_append : Expr :=
  .cons both (:: (quote both) (:: both (:: (quote id) const)))

/-
Yep. Reverse of then_cons.
-/
def example_then_append : Except Error Expr := do
  let my_data := symbol "hi"
  let my_other := symbol "other"

  do_step run (:: apply (:: then_append my_data))
    >>= (fun c => do_step run (:: apply (:: c my_other)))

#eval example_then_append

/-
Note:
we need to then_append in reverse consistently.
Otherwise, we get a hanging :: at the end.
-/
def example_append_chain : Except Error Expr := do
  let my_data := symbol "hi"
  let my_other := (symbol "other")

  do_step run (:: apply (:: then_append my_data))
    >>= (fun c => do_step run (:: apply (:: c my_other)))
    >>= (fun c => do
      let my_d ← do_step run (:: apply (:: then_append (symbol "other data")))
      do_step run (:: apply (:: my_d c)))

#eval example_append_chain

/-
Why can't we chain then_cons?
What happens if we do?

Then cons can be chained just fine.
We just need to:
- apply every then_cons with the data
- apply the output of then_cons with preivous chain
-/
def example_cons_chain : Except Error Expr := do
  let my_data := symbol "hi"
  let my_other := symbol "other"

  do_step run (:: apply (:: then_cons my_data))
    >>= (fun c => do_step run (:: apply (:: c my_other)))
    >>= (fun c => do
      let my_d ← do_step run (:: apply (:: then_cons (symbol "other data")))
      do_step run (:: apply (:: my_d c)))

def cons_chain_is_reverse_append_chain : Except Error Bool := do
  let a_l ← unwrap_with (.stuck nil) <| Expr.as_list (← example_cons_chain)
  let b_l ← unwrap_with (.stuck nil) <| Expr.as_list (← example_append_chain)

  dbg_trace a_l
  dbg_trace b_l

  pure (a_l == b_l.reverse)

#eval cons_chain_is_reverse_append_chain

#eval example_cons_chain
#eval example_append_chain

def example_cons_now : Except Error Expr := do
  let my_data := symbol "hi"
  let my_l := :: (symbol "head") (:: (symbol "tail") nil)

  let c := (:: then_cons my_data)
  do_step run (:: apply (:: (:: apply c) my_l))

#eval example_cons_now

def example_cons_multiple : Except Error Expr := do
  let my_data := symbol "hi"
  let my_l := :: (symbol "head") (:: (symbol "tail") nil)

  let c  := (:: apply (:: then_cons my_data))
  let o  := (:: apply (:: then_cons (symbol "other data")))
  let l := (:: apply (:: c my_l))
  do_step run (:: apply (:: o l))

#eval example_cons_multiple

def example_then_cons : Except Error Expr := do
  let my_data := symbol "hi"
  let my_l := :: (symbol "head") (:: (symbol "tail") nil)

  do_step run (:: apply (:: then_cons my_data))
    >>= (fun c => do_step run (:: apply (:: c my_l)))

#eval example_then_cons

/-
Flips the head and next of a :: x (:: y ys) list, giving
:: y (:: x xs)
-/
def flip_head_next : Expr :=
  let y_const := :: both (:: (:: const const) id)
  let get_y := (:: π (:: (:: const apply) (:: π (:: y_const id))))
  let get_xrst := (:: π (:: id (:: both (::
    (quote apply)
    (:: π (:: (:: const id) id))))))

  (:: both (:: get_y get_xrst))

def example_flip_head_next : Except Error Expr := do
  let my_l := (:: (symbol "x") (:: (symbol "y") (symbol "ys")))
  let flip := (:: apply (:: flip_head_next my_l))

  do_step run flip

#eval example_flip_head_next

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

