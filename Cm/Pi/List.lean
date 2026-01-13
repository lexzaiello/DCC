import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Util

open Expr

/-
(:: apply (:: apply (:: list.rec_with (:: list.rec_with (:: nil_case xs_case)))) list)

xs_case should accept the head of the list as an argument.
Note that this is a somewhat unsafe operation on lists that are not
delimited with nil.

xs_case receives the head and tail of the list.

inputs to xs_case:
(:: apply (:: apply list.rec_with (:: list.rec_with (:: nil_case xs_case))) (:: x xs))

NOTE:
- this is the exact same as the nat recursor, except zero is changed to nil
- we don't need to inject xs, since it's already in that position.

:: π whatever handles it for us.
-/

def list.rec_with.self :=
  :: π (:: id nil)

def list.rec_with.nil_case :=
  :: π (:: nil (:: π (:: id nil)))

/-
These are in the same position as with Nat's recursor.
-/
def list.rec_with.xs_case :=
  :: π (:: nil (:: π (:: nil id)))

-- produces (:: const (:: list.rec_with (:: nil_case xs_case)))
def list.rec_with.match_args : Expr :=
  (:: both (:: (quote const) (:: both (:: list.rec_with.self (:: both (:: list.rec_with.self (:: both (:: list.rec_with.nil_case list.rec_with.xs_case))))))))

def list.rec_with.quoted_xs_case :=
  (:: both (:: (quote const) list.rec_with.xs_case))

/-
This is the only thing that changes
-/
def list.rec_with.xs_num :=
  :: π (:: nil id)

def list.rec_with.quote_fix'' : Expr :=
  :: both (::
    (quote both) (:: both (::
    list.rec_with.quoted_xs_case
    (:: both (::
      (quote both) (:: both (::
      list.rec_with.match_args
      (quote list.rec_with.xs_num))))))))

def list.rec_with.quote_fix_and_run : Expr :=
  :: both (::
    (quote both) (:: both (::
      (quote (quote apply)) list.rec_with.quote_fix'')))

/-
Assumes list.rec_with is the first argument, nil_case 2nd, xs_case 3rd
-/
def list.rec_with : Expr :=
  let inner_eq := :: both (:: (quote eq) (:: both (:: list.rec_with.nil_case list.rec_with.quote_fix_and_run)))
  .cons both (:: inner_eq (quote nil))

/-
(:: apply (:: nat.plus (:: m n)))
Recurse on m, base case n.

each level, cons on one of our own elements.
-/
def list.append : Expr :=
  /-
    For the xs case, we receive (:: (:: list.rec_with ... stuff) (:: x xs))
    so we just need to cons onto the (:: x xs).
    This may not be the right order but we'll see.
    We just want to cons the x part, not the xs.
    That gets handled later.

    TODO: see if this receives the very top head element.
    may need to change recursor.
    not sure.
  -/
  -- let do_cons' := :: π (:: (
  let x := :: π (:: nil (:: π (:: id nil)))
  let xs := :: π (:: nil (:: π (:: nil id)))
  let do_app := :: both (:: (quote apply) (:: π (:: (:: both (:: (quote apply) id)) (:: π (:: nil id)))))
  let do_cons := :: both (:: x do_app)

  let m := :: π (:: id nil)
  let n := :: π (:: nil const)

  let nil_case := n

  -- generates recursor
  let do_rec := (:: both
    (:: (quote apply) (:: both
      (:: (quote list.rec_with) (:: both
        (:: (quote list.rec_with)
          (:: both (:: nil_case (quote do_cons)))))))))

  (:: both (:: (quote apply) (:: both (:: do_rec m))))

namespace test_list

def list_append (a b : Expr) : Except Error Expr := do
  try_step_n run 100 (:: apply (:: list.append (:: a b)))

#eval list_append (:: (symbol "a") (:: (symbol "b") nil)) (:: (symbol "a") (:: (symbol "b") nil))

/-
Continue running the recursor on a list until we get to nil,
then display.
-/
def rec_with_descent : Except Error Expr := do
  let my_succ_case := :: both (:: (quote apply) (:: π (:: (:: both (:: (quote apply) id)) id)))
  let my_zero_case := Expr.id
  let out ← try_step_n run 50 (:: apply (:: (:: apply (:: list.rec_with (:: list.rec_with (:: my_zero_case my_succ_case)))) (:: (symbol "discard") nil)))
  pure out

#eval rec_with_descent

end test_list
