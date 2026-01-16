import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval

/-
Utility functions for the list calculus.
-/

open Expr

def quote (e : Expr) : Expr :=
  (:: const e)

/-
Utility methods for currying that simulate lambda calculus binders with de bruijn indices.
In the list calculus, arguments are usually positional, not curried.
This gets around that by growing the context in a sequence, cons'ing each argument as it is applied.

The three main operators are:
args.read, args.push, $args, and lam.
var.read `n` creates a (:: π (:: nil (:: π ... id))) expression with `n` nil entries.
This skips the first `n` elements in a context and gets the last one.

args.store pushes an argument to the arguments list of a function.
args.store expects that the context / arguments list is in scope.

(:: apply (:: (:: apply (:: args.push x)) args)) = (:: x args)
args.push = (:: both (:: (quote both) (:: both
  const
  (quote id))))

$args spreads the context / arguments list among many operations,
and applies the args to each function.

(:: apply (:: (:: apply (:: $args (:: f (:: g h)))) args)) =
(:: (:: apply (:: f args)) (:: (:: apply (:: g args)) (:: apply h args)))

(:: apply (:: lam body)) creates a (:: both (:: (quote body) args.store)) expression.

TODO:
- these old utility methods may not actually work as intended.
-/

def mk_π_skip (n : ℕ) (at_end : Expr) : Expr :=
  match n with
  | .zero => at_end
  | .succ n =>
    :: π (:: nil (mk_π_skip n at_end))

example : mk_π_skip 2 (:: π (:: id nil)) = (:: π (:: nil (:: π (:: nil (:: π (:: id nil)))))) := rfl

notation "args.read" => (mk_π_skip · id)

example : try_step_n' 5 (:: apply (:: (args.read 2) (:: (symbol "a") (:: (symbol "b") (symbol "c"))))) = (.ok (symbol "c")) := rfl

-- This is essentially the I rule in the compilation from lambda calculus to SK combiantors
notation "var.read" => (fun (n : ℕ) => List.foldr Expr.cons Expr.id (List.replicate n Expr.const))

-- This is the K rule
notation "var.store" => (fun (n : ℕ) => List.foldr Expr.cons const (List.replicate n const))

def mk_binder (n : ℕ) (e : Expr) :=
  match n with
  | .zero => e
  | .succ n' =>
    let the_both := (List.foldr Expr.cons Expr.both (List.replicate n' Expr.const))
    (:: the_both (mk_binder n' e))

notation "$n" => (fun (n : ℕ) => List.foldr Expr.cons apply (List.replicate n const))

example : $n 0 = apply := rfl
example : $n 1 = (:: const apply) := rfl

notation "λ'" => mk_binder

example : try_step_n' 100 (:: apply (:: (:: apply (:: (λ' 1 (:: (var.store 1) id)) (symbol "hello, world"))) (symbol "discard")))
  = (.ok (symbol "hello, world")) := rfl

#eval try_step_n' 100 (:: apply (:: (:: apply
  (:: (λ' 1 (
    (λ' 2 (:: (var.read 0) (var.read 1)))))
      (quote (symbol "var 0"))))
      (quote (symbol "var 1"))))

example : try_step_n' 10 (:: apply (:: (:: apply
  (:: (λ' 1 (
    (λ' 2 (:: (var.read 1) (var.read 1)))))
      (quote (symbol "var 0"))))
      (quote (symbol "var 1")))) =
    (.ok (:: (:: const (symbol "var 1")) (:: const (symbol "var 1")))) := rfl

example : try_step_n' 10 (:: apply (:: (:: apply
  (:: (λ' 1
    (λ' 2 (:: (var.read 1) (var.read 1))))
      (quote (symbol "var 0"))))
      (quote (symbol "var 1")))) =
    (.ok (:: (:: const (symbol "var 1")) (:: const (symbol "var 1")))) := rfl

example : try_step_n' 10 (:: apply (:: (:: apply
  (:: (λ' 1 (λ' 2 (:: (var.store 0) (var.store 0))))
    (quote (symbol "var 0")))) (quote (symbol "var 1")))) =
      (.ok (:: (:: const (symbol "var 0")) (:: const (symbol "var 0")))) := rfl

example : try_step_n' 1 (:: apply (:: (λ' 0 (var.read 0)) (quote (symbol "var 0")))) = (.ok (:: const (symbol "var 0"))) := rfl

/-
(:: apply (:: (:: apply (:: (:: apply (:: fun.comp f)) g)) x))
= (:: apply (:: f (:: apply (:: g x))))
-/
def func.comp : Expr := (λ' 1 (λ' 2 (λ' 3 (:: ($n 3) (λ' 3 (:: (var.store 3) (λ' 2 (:: ($n 2) (λ' 2 (:: (var.read 1) (var.read 0)))))))))))
--def func.comp : Expr := (λ' 1 (:: (λ' 1 (λ' 1 (var.read 3))) (var.store 0)))

#eval try_step_n 500 (:: apply (:: (:: apply (:: (:: apply (:: func.comp id)) id)) (symbol "hi")))

--infixr:65 "∘''" => 

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
notation "$?" => (fun e => (:: both (:: (quote apply) e))) -- for applying later

def both_from_list (n_repeat : ℕ) : List Expr → Expr
  | .cons x xs => with_boths (:: x (both_from_list n_repeat xs))
  | .nil => nil
where the_both (n_quote : ℕ) := (List.replicate n_quote const).foldr Expr.cons both
      with_boths (e : Expr) := (List.range n_repeat).map the_both
        |> List.foldr Expr.cons e

example : both_from_list 1 [(symbol "a"), (symbol "b"), (symbol "c")]
  = (:: both (:: (symbol "a") (:: both (:: (symbol "b") (:: both (:: (symbol "c") nil)))))) := rfl

example : both_from_list 2 [(symbol "a"), (symbol "b"), (symbol "c")]
  = (:: both (:: (quote both) (:: (symbol "a") (:: both (:: (quote both)
    (:: (symbol "b") (:: both (:: (quote both) (:: (symbol "c") nil))))))))) := rfl


#eval both_from_list 2 [(symbol "a"), (symbol "b"), (symbol "c")]

def mk_both_tail : Expr → Expr
  | :: const e => :: const e
  | :: x xs => :: both (:: x (mk_both_tail xs))
  | e => e

/-
Creates a :: both (:: both ...) tree,
ending with the last expression.

Does not both quoted exprs.
-/
def mk_both : Expr → Expr
  | :: const e => :: const e
  | :: x xs => :: both (:: (mk_both x) (mk_both xs))
  | e => e

/-
Creates a :: both (:: both ...) tree,
ending with the last expression.

Does not both quoted exprs.
Does not quote lists with quoted heads.

quotes both n times.
-/
def mk_both' (n : ℕ) : Expr → Expr
  | :: const e => :: const e
  | :: x xs => :: the_both (:: (mk_both' n x) (mk_both' n xs))
  | e => e
where the_both := (List.replicate n const).foldr Expr.cons both

/-
Inserts a quoted both after every both
in a tree.
-/
def nest_both : Expr → Expr
  | :: both xs => :: both (:: (quote both) (nest_both xs))
  | e => e

prefix:60 "q'" => quote
notation "qn'" => (fun (n : ℕ) (e : Expr) => List.foldr Expr.cons e (List.replicate n Expr.const))

/-
(f ·') = (:: both (:: f id))

These operators do not force evaluation.
-/
postfix:60 "·'" => (fun f => (:: both (:: f id)))

prefix:60 "·'" => (fun f => (:: both (:: id f)))

infixr:60 "b'" => (fun f g => (:: both (:: f g)))

#eval do_step (:: apply (::
  ((·' (quote (symbol "another")) ) ∘'
  ((quote (symbol "prefix")) ·')) (symbol "hi")))

/-
|> pipelining
(f x)
  |> my_op = (:: apply (:: my_op (:: apply (f x))))
-/
infixl:60 "|>'" => (fun x => (fun y => (:: apply (:: y (:: apply x)))))

#eval do_step ((::
  ((·' (quote (symbol "another")) ) ∘'
  ((quote (symbol "prefix")) ·')) (symbol "hi")) |>' Expr.id)

/-
<| pipelining
my_op
  <| (f x) = (:: apply (:: my_op (:: apply (f x))))
-/
infixr:60 "<|'" => (fun x y => y |>' x)

#eval do_step (Expr.id <|' (::
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

  do_step (:: apply (:: then_append my_data))
    >>= (fun c => do_step (:: apply (:: c my_other)))

#eval example_then_append

/-
Note:
we need to then_append in reverse consistently.
Otherwise, we get a hanging :: at the end.
-/
def example_append_chain : Except Error Expr := do
  let my_data := symbol "hi"
  let my_other := (symbol "other")

  do_step (:: apply (:: then_append my_data))
    >>= (fun c => do_step (:: apply (:: c my_other)))
    >>= (fun c => do
      let my_d ← do_step (:: apply (:: then_append (symbol "other data")))
      do_step (:: apply (:: my_d c)))

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

  do_step (:: apply (:: then_cons my_data))
    >>= (fun c => do_step (:: apply (:: c my_other)))
    >>= (fun c => do
      let my_d ← do_step (:: apply (:: then_cons (symbol "other data")))
      do_step (:: apply (:: my_d c)))

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
  do_step (:: apply (:: (:: apply c) my_l))

#eval example_cons_now

def example_cons_multiple : Except Error Expr := do
  let my_data := symbol "hi"
  let my_l := :: (symbol "head") (:: (symbol "tail") nil)

  let c  := (:: apply (:: then_cons my_data))
  let o  := (:: apply (:: then_cons (symbol "other data")))
  let l := (:: apply (:: c my_l))
  do_step (:: apply (:: o l))

#eval example_cons_multiple

def example_then_cons : Except Error Expr := do
  let my_data := symbol "hi"
  let my_l := :: (symbol "head") (:: (symbol "tail") nil)

  do_step (:: apply (:: then_cons my_data))
    >>= (fun c => do_step (:: apply (:: c my_l)))

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

  do_step flip

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

  do_step (:: apply (:: set_tail_args' replace_with))
    >>= (fun rep =>
      do_step (:: apply (:: rep replace_in)))

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
  do_step (:: apply (:: set_tail_args (:: replace_with replace_in)))

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

  do_step (:: apply (:: map_head_arg (:: my_f my_args)))

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

  do_step (:: apply (:: map_head my_f))
    >>= (fun map => do_step (:: apply (:: map my_list)))

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

