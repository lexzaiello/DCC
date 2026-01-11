import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Applies the argument.
-/
def apply_now' : Expr :=
  :: both (:: (:: const apply) id)

def example_apply_now : Except Error Expr :=
  do_step run (:: apply (:: apply_now' (:: id (symbol "applied!"))))

#eval example_apply_now

/-
Currying is just n-nested then_append.
Then_append has a slightly misleading name,
since it doesn't actually append at the end.

(:: (:: then_append a) b) = (:: b a)

What happens if we chain the leftmost things?
-/

def test_many_chain_then_append : Except Error Expr := do
  let my_d := (symbol "hi")
  let base := (:: my_d (symbol "inner"))
  let base' := (:: apply (:: (:: apply (:: then_append (symbol "arg"))) (symbol "f")))

  let base'' := (:: apply (:: (:: apply (:: then_append (symbol "arg₂"))) base'))

  do_step run base''

#eval test_many_chain_then_append

/-
then_append only builds from inside out

(:: curry f) x = (:: f x). this is just then_cons
(:: (:: (:: curry (:: curry f)) x) y) = (:: f (:: x y))
(:: curry (:: cury f))
This is (:: apply (:: then_cons f) (:: (:: then_append y) x)

Many layers of both that get popped the more arguments get added.

Until last layer, data:
(:: both (:: const (:: then_cons f)) (:: both (:: const then_cons) (:: then_cons x)))

The then_cons will do (:: x y)

with 1: (:: curry f) =

(:: both (:: const (:: apply (:: then_cons f))) id)
-/

/-
f(arg)
-/
def test_curry_one : Except Error Expr := do
  let e := (:: apply (:: then_cons (symbol "f")))
  do_step run (:: apply (:: e (symbol "arg")))

#eval test_curry_one

/-
Basically all prior things get then_cons'd,
and the last thing doesn't.
-/
def test_curry_two : Except Error Expr := do
  let e := (:: apply (:: then_cons (symbol "f")))
  let a := (:: apply (:: then_cons (symbol "x")))
  do_step run (:: apply (:: e (:: apply (:: a (symbol "y")))))

/-
We should be able to make
(:: (:: (:: a b) c) d) in a nice order.

Nice.
-/
def test_append : Except Error Expr := do
  let e := (:: apply (:: then_cons (symbol "f")))
  let x := (symbol "x")
  let y := (:: apply (:: then_append (symbol "y")))

  do_step run (:: apply (:: e (:: apply (:: y x))))

#eval test_append

/-
Last argument is not append?

Append does pretty much what we want it to.

We leave the first argument un-appended,
append remaining arguments, then...
-/
def test_append' : Except Error Expr := do
  let e := (:: apply (:: then_cons (symbol "f")))
  let x := (symbol "x")
  let y := (:: apply (:: then_append (symbol "y")))
  let z := (:: apply (:: then_append (symbol "z")))
  let z₁ := (:: apply (:: then_append (symbol "z₁")))

  do_step run (:: apply (:: e (:: apply (:: z₁ (:: apply (:: z (:: apply (:: y x))))))))

#eval test_append'

#eval test_curry_two

/-
Currying is turning this:
(:: (:: (:: (:: (:: f x) a) b) c) d)
into this:
(:: f (:: x (:: a (:: b (:: c (:: d ...

So we can start by applying in that order.
-/
def test_append'' : Except Error Expr := do
  let f := symbol ("f")
  let app (s : String) := (:: apply (:: then_append (symbol s)))
  do_step run (:: apply (:: (app "c") (:: apply (:: (app "b") (:: apply (:: (app "a") f))))))

#eval test_append''

/-
:: (:: (:: (symbol "f") (symbol "a")) (symbol "b")) (symbol "c")

And then for each layer, we smush them together somehow

then_cons for each layer? and it outermost?
-/

/-
Note: need apply at the very end.
Another note: we may need to delay f evaluation somehow.

curry 0 f = (:: const f)
curry 1 f = (:: apply (:: then_cons f))
curry 2 f = (:: (:: apply (:: then_cons f)) 
-/

/-
Currying is just even lazier then_append.

curry 1 f = (:: then_append f)

(:: apply (:: (:: apply (:: then_append (symbol "arg"))) (symbol "f")))

this is roughly the order we want, which is nice.

curry n = n * then_cons, followed by 

-/


--def curry : ℕ → Except Error Expr
--  | .zero => 

