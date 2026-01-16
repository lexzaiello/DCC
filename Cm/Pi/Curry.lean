import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Utility methods for currying that simulate lambda calculus binders with de bruijn indices.
In the list calculus, arguments are usually positional, not curried.
This gets around that by growing the context in a sequence, cons'ing each argument as it is applied.

The three main operators are:
args.read, args.push, $args, and lam.
var.read `n` creates a (:: π (:: nil (:: π ... id))) expression with `n` nil entries.
This skips the first `n` elements in a context and gets the last one.

args.push pushes an argument to the arguments list of a function.
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
This is essentially one level of currying.
Applying other arugments will just push this argument to the front of them.

(:: apply (:: (:: apply (:: (:: apply (:: lam body)) (symbol "arg"))) other_args))
= (:: apply (:: body (:: (symbol "arg") other_args)))

TODO:
- these old utility methods may not actually work as intended.
-/

def mk_π_skip (n : ℕ) (at_end : Expr) : Expr :=
  match n with
  | .zero => :: π (:: at_end nil)
  | n => (List.replicate n nil).foldr (fun e acc => (:: π (:: e acc))) (:: π (:: at_end nil))

example : mk_π_skip 2 id = (:: π (:: nil (:: π (:: nil (:: π (:: id nil)))))) := rfl

def args.read (n : ℕ) (e : Expr) : Expr := mk_π_skip n e

example : try_step_n' 5 (:: apply (:: (args.read 0 id) (:: (symbol "a") nil))) = (.ok (symbol "a")) := rfl
example : try_step_n' 5 (:: apply (:: (args.read 2 id) (:: (symbol "a") (:: (symbol "b") (:: (symbol "c") nil))))) = (.ok (symbol "c")) := rfl
example : try_step_n' 5 (:: apply (:: (args.read 0 id) (:: (symbol "a") (:: (symbol "b") (symbol "c"))))) = (.ok (symbol "a")) := rfl

def args.push : Expr := (:: both (::
  (quote both) (:: both (::
    const
    (quote id)))))

example : try_step_n' 5
  (:: apply
    (:: (:: apply (:: args.push (symbol "arg"))) (:: (symbol "args") nil))) =
    (.ok (:: (symbol "arg") (:: (symbol "args") nil))) := rfl

example : try_step_n' 5 (:: apply (:: (:: apply (:: args.push (symbol "arg"))) nil)) =
  (.ok (:: (symbol "arg") nil)) := rfl

def args.app (e : Expr) :=
  match e with
  | :: x nil => (:: both (:: (:: both (:: (quote apply) (:: both (:: (quote x) id)))) (quote nil)))
  | :: x xs => (:: both (::
    (:: both (:: (quote apply) (:: both (:: (quote x) id))))
    (args.app xs)))
  | e => (quote e)

def args.app.test_args : Expr := (:: (symbol "a") (:: (symbol "b") (:: (symbol "c") nil)))
def args.app.test_ops : Expr := (:: (args.read 0 id) (:: (args.read 1 id) (:: (args.read 2 id) nil)))

example : try_step_n' 10 (:: apply (:: (args.app args.app.test_ops) args.app.test_args)) = (.ok args.app.test_args) := rfl

def curry.push_future_arg := (quote (:: both (:: (quote apply) (:: both (:: (quote args.push) id)))))

def curry : Expr := (:: both (:: (quote both)
    (:: both (:: (quote (quote both)) (:: both (:: (quote both)
      (:: both (:: (quote (quote (quote apply))) (:: both (:: (quote both)
        (:: both (:: (quote (quote both)) (:: both (:: (quote both)
          (:: both (:: (:: both (:: (quote const) const)) curry.push_future_arg))))))))))))))))

example : try_step_n' 50 (:: apply (:: (:: apply (:: (:: apply (:: curry.push_future_arg (args.app (:: (quote (symbol "arg: ")) (:: (args.read 0 id) nil))))) (symbol "hi"))) (:: (symbol "other arg") (:: (symbol "other other arg") nil))))
  = (.ok (:: (symbol "hi") (:: (symbol "other arg") (:: (symbol "other other arg") nil)))) := rfl

set_option maxRecDepth 1000

example : try_step_n' 100 (:: apply (::
  (:: apply (:: (:: apply (:: curry
    (args.app (:: (quote (symbol "ctx: ")) (:: id nil)))))
    (symbol "hi")))
    (:: (symbol "other arg") (:: (symbol "other other arg") nil)))) =
  (.ok (:: (symbol "ctx: ") (:: (:: (symbol "hi")
    (:: (symbol "other arg") (:: (symbol "other other arg") nil)))
    nil))) := rfl

example : try_step_n' 100 (:: apply (:: (:: apply (:: (:: apply (:: curry (args.read 0 id))) (symbol "arg 0"))) (symbol "rest args")))
   = (.ok (symbol "arg 0")) := rfl

example : try_step_n' 51 (:: apply (:: (:: apply (:: (:: apply (:: (:: apply (:: curry (:: apply (:: curry (args.read 1 id))))) (symbol "arg 0"))) (symbol "rest args"))) (:: (symbol ("other arg")) nil))) = (.ok (symbol "other arg")) := rfl
