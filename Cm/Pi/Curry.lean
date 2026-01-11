import Mathlib.Data.Nat.Notation
import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
Expects the first both argument, but will wait for the second.

(:: (:: both_partial f) x) = (:: f x)

TODO: should this insert an apply by default? probably not.
-/
def both_partial : Expr :=
  (:: both (:: (quote both) (:: both (:: const (quote id)))))

def test_both_partial : Except Error Expr := do
  let my_f := symbol "f"
  let my_x := symbol "x"

  do_step run (:: apply (:: (:: apply (:: both_partial my_f)) my_x))

-- :: "f" "x"
#eval test_both_partial

/-
Note: we just turned both into both_partial with the above.
We removed one argument.
Pattern?

(:: both (:: (quote both) (:: both (:: const (quote id)))))

both is what we're currying here, so we quoted it.
Experiment time.
-/

/-
To curry two arguments:
- quote the function being called

-/
def test_curry (e : Expr) : Expr :=
  (:: both (:: (quote e) (:: both (:: const (quote id)))))

/-
Explicitly takes two arguments.
-/
def test_fn : Expr :=
  :: π (:: id (:: π (:: id (:: const nil))))

def test_fn₁ : Expr :=
  id

/-
To curry one argument (this is not really currying but
just for demonstration):

- quote the expression
- both (quote apply) (both (quote e) id
-/

def curr₁ (e : Expr) : Expr :=
  :: both (:: (quote apply) (:: both (:: (quote e) id)))

#eval do_step run (:: apply (:: (curr₁ test_fn₁) (symbol "a")))

/-
Currying:

- create a new function returning our function,
with whatever value substituted.

(:: f (:: x y)) = (:: (:: (:: curry f) x) y)

Each layer, just bubble up a partially applied

(:: both (const me))

Now this becomes just multiple both_partials.

(:: (:: both_partial f) (:: both_partial x y))
-/
def curry : Expr :=
  let inner_f := :: both (::
    
    both_partial
  
  -- (:: both (:: const (:: both (const me))) id)
  /-let me := (:: (:: const const) id)
  let mk_me := (:: both me)
  :: both (::
    (quote both)
    (:: both
      (:: both (::
        (quote const)
        (:: both (::
          (quote both)
          mk_me)))))
      (quote id))-/
