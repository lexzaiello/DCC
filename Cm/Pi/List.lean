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

/-
the nil case is the second argument to :: list.rec (:: list.rec (:: nil_case cons_case))
-/
def list.rec_with.nil_case :=
  :: π (:: nil (:: π (:: id nil)))

/-
These are in the same position as with Nat's recursor.
-/
def list.rec_with.xs_case :=
  :: π (:: nil (:: π (:: nil id)))

-- produces (:: const (:: list.rec_with (:: nil_case xs_case)))
/-
for passing into our handlers
-/
def list.rec_with.match_args : Expr :=
  (:: both (:: (quote const) (:: both (:: list.rec_with.self (:: both (:: list.rec_with.self (:: both (:: list.rec_with.nil_case list.rec_with.xs_case))))))))

def list.rec_with.quoted_xs_case :=
  (:: both (:: (quote const) list.rec_with.xs_case))

/-
This is the only thing that changes
we just get the entire list, since we can use
π to project over it anyway.
-/
def list.rec_with.list := Expr.id

/-
case_e should be unquoted
this has access to the entire context when :: list.rec_with is applied
-/
def list.rec_with.quote_fix'' (case_e : Expr) : Expr :=
  :: both (::
    (quote both) (:: both (::
    (:: both (:: (quote const) case_e))
    (:: both (::
      (quote both) (:: both (::
      list.rec_with.match_args
      (quote list.rec_with.list)))))))) -- xs_num is the list

def list.rec_with.quote_fix_and_run (case_e : Expr) : Expr :=
  :: both (::
    (quote both) (:: both (::
      (quote (quote apply)) (list.rec_with.quote_fix'' case_e))))

/-
Assumes list.rec_with is the first argument, nil_case 2nd, xs_case 3rd
We quote an extra nil since that is our comparison value.
We are checking if the list is nil
-/
def list.rec_with : Expr :=
  let inner_eq := :: both (:: (quote eq) (:: both (:: (list.rec_with.quote_fix_and_run list.rec_with.nil_case) (list.rec_with.quote_fix_and_run list.rec_with.xs_case))))
  .cons both (:: inner_eq (quote nil))

/-
(:: apply (:: list.map (:: f l)))
-/
def list.map : Expr :=
  /-
    succ_case gets passed (:: match_args l)
  -/

  let nil_handler := (quote (quote nil))

  let my_f := :: π (:: id nil)
  let my_l := :: π (:: nil id)

  /-
    In succ handler.
    both'd to prepend the mapped head
  -/
  let advance := :: both (:: (quote apply) (:: π (:: (:: both (:: (quote apply) id)) (:: π (:: nil id)))))

  -- f should operate on the head element
  let f_on_x := :: both (::
    (quote π)
    (:: both (::
      (quote nil)
      (:: both (::
        (quote π) (:: both
        (:: my_f (quote nil))))))))

  /-
    This has all the original args in scope.
  -/
  let succ_handler := :: both (:: (quote both) (:: both (:: f_on_x (quote advance))))

  let do_rec := (:: both
    (:: (quote apply) (:: both
      (:: (quote list.rec_with) (:: both
        (:: (quote list.rec_with)
          (:: both (:: nil_handler succ_handler))))))))

  (:: both (:: (quote apply) (:: both (:: do_rec my_l))))

namespace test_list

def test_list_map_const (fn l : Expr) : Except Error Expr := do
  try_step_n run 100 (:: apply (:: list.map (:: fn l)))

#eval test_list_map_const (:: both (:: (quote (symbol "hi")) id)) (:: (symbol "a") (:: (symbol "b") nil))
#eval test_list_map_const (:: both (:: (quote (symbol "hi")) id)) (:: (symbol "a") (:: (symbol "b") nil))
  >>= (pure <| · == (:: (:: (symbol "hi") (symbol "a")) (:: (:: (symbol "hi") (symbol "b")) nil)))

end test_list

def list.reverse.state'' : Expr :=
  :: π (:: nil (:: π (:: nil id)))

/-
nil_handler has :: match_args l in scope
-/
def list.reverse.nil_handler₀ : Expr :=
  :: const nil

/-
  Push the head element into the list returned by the nil handler.
  this has :: match_args l in scope
  run the old nil handler to render the list.
-/
def list.reverse.nil_handler' : Expr :=
  let x := :: π (:: nil (:: π (:: id nil))) -- this has match_args in scope
  let nil_handler_old := :: π (:: (:: π (:: nil (:: π (:: nil (:: π (:: id nil)))))) nil)
  .cons both (:: (quote const) (:: both (:: x (:: both (:: (quote apply) (:: both (:: nil_handler_old (quote nil))))))))

def list.reverse.rec_with : Expr :=
  :: π (:: (:: π (:: id nil)) nil)

def list.reverse.succ_handler_old : Expr :=
  :: π (:: (:: π (:: nil (:: π (:: nil (:: π (:: nil id)))))) nil)

/-
Has all match args in context.
-/
def list.reverse.match_args' : Expr :=
  :: both (:: list.reverse.rec_with (:: both (:: list.reverse.rec_with (:: both (:: list.reverse.nil_handler' list.reverse.succ_handler_old)))))

def list.reverse.advance : Expr :=
  (:: both (:: (quote apply) (:: both (:: (:: both (:: (quote apply) list.reverse.match_args')) list.reverse.state''))))

def list.reverse.do_rec : Expr :=
  (:: list.rec_with (:: list.rec_with
    (:: list.reverse.nil_handler₀ list.reverse.advance)))

/-
Should have just l in scope.
-/
def list.reverse.state₀ : Expr := id

def list.reverse.app_rec : Expr :=
  (:: apply list.reverse.do_rec)

def list.reverse.mk_rec : Expr :=
  :: π (:: (quote apply) (quote list.reverse.do_rec))

/-
  (:: apply (:: list.reverse l))
-/
def list.reverse : Expr :=
  (:: both (:: (quote apply) (:: both (:: list.reverse.mk_rec list.reverse.state₀))))

namespace test_list

def test_list_reverse (l : Expr) : Except Error Expr :=
  try_step_n run 1000 (:: apply (:: list.reverse l))

#eval test_list_reverse (:: (symbol "a") (:: (symbol "b") (:: (symbol "c") nil)))
  >>= (pure <| · == (:: (symbol "c") (:: (symbol "b") (:: (symbol "a") nil))))

end test_list

def list.length : Expr :=
  let my_l := Expr.id
  let advance := :: both (:: (quote apply) (:: π (:: (:: both (:: (quote apply) id)) (:: π (:: nil id)))))

  let do_rec := (:: list.rec_with (:: list.rec_with
    (:: (quote (symbol "zero"))
    (:: both (:: (quote (symbol "succ")) advance)))))
  (:: both (:: (quote apply) (:: both (:: (quote (:: apply do_rec)) my_l))))

namespace test_list

def test_list_length (l : Expr) : Except Error Expr :=
  try_step_n run 100 (:: apply (:: list.length l))

#eval test_list_length (:: (symbol "a") nil)

end test_list

/-
(:: apply (:: list.prepend (:: m n)))
Recurse on m, base case n.

each level, cons on one of our own elements.
-/
def list.prepend : Expr :=
  /-
    For the xs case, we receive (:: (:: list.rec_with ... stuff) (:: x xs))
    so we just need to cons onto the (:: x xs).
    This may not be the right order but we'll see.
    We just want to cons the x part, not the xs.
    That gets handled later.

    TODO: see if this receives the very top head element.
    may need to change recursor.
    not sure.
    I think cons is actually offset.
    need to get the head element as well.
  -/
  -- let do_cons' := :: π (:: (
  let x := :: π (:: nil (:: π (:: id nil)))
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

/-
(:: apply (:: list.append (:: a b))) = a ++ b
This is implemented by prepending then reversing.
-/
def list.append : Expr :=
  :: both (::
    (quote apply) (:: both (::
      (quote list.reverse) (:: both
        (:: (quote apply) (:: both (::
        (quote list.prepend) id)))))))

namespace test_list

def test_list_prepend (a b : Expr) : Except Error Expr := do
  try_step_n run 100 (:: apply (:: list.prepend (:: a b)))

#eval test_list_prepend (:: (symbol "a") (:: (symbol "b") nil)) (:: (symbol "a") (:: (symbol "b") nil))

/-
Continue running the recursor on a list until we get to nil,
then display.
-/
def rec_with_descent : Except Error Expr := do
  let my_succ_case := :: π (:: nil id)
  let my_zero_case := Expr.id
  let out ← try_step_n run 50 (:: apply (:: (:: apply (:: list.rec_with (:: list.rec_with (:: my_zero_case my_succ_case)))) (:: (symbol "discard") nil)))
  pure out

#eval rec_with_descent

end test_list
