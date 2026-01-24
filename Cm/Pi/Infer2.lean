import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Std.Util
import Cm.Pi.Std.Except

open Expr

/-
Notes:
- with current valid_judgment setup, we have no way of expressing that both
is well-typed in a point-free way.
- we could use the infer fixpoint method, but this is time consuming
and we will need to finish the entire infer function for this to work

infer function is challenging to write, but ultimately, the meta theoretical
proofs should coincide with the actual usage of the system

- how can you be sure that the eval / infer function coincides with the model?
proofs will be gargantuan with infer function approach, but quite nice,
since we can transport them quite easily to the actual implementation vs just the model

- the other question is inductive types:
  - I want to support inductive types more natively, rather than just extending the infer
function, as this feels quite dangerous.
  - we were able to encode some basic "inductive" types
  
-/

def TData : Expr := .symbol "Data"
def TType : Expr := .symbol "Type"
def IList : Expr := .symbol "List"

def TFail : Expr := .symbol "sorry"

def expected_but_found : Expr :=
  (λ' 1 (λ' 2 (::
    (λ' 1 (::
      (var.store 1)
      (λ' 1 (:: (:: (var.store 0) <| symbol "expected:") (var.read 0)))))
        (:: (var.store 0) <| (λ' 1 (:: (:: (var.store 0) <| symbol "but found: ") (var.read 0)))))))

def assert_eq : Expr :=
  let my_v := var.read 0

  let eq_ok := (λ' 1 (:: (var.store 1) (λ' 1 (:: (:: (var.store 0) Except'.s_ok) my_v))))

  (λ' 1
    (:: (λ' 1 (:: (:: (var.store 0) eq) (λ' 1 (:: eq_ok
        (λ' 1 (λ' 2 (:: (:: (var.store 0) (:: (var.store 0) Except'.s_err))
        (λ' 1 (:: (:: (var.store 0) apply) (λ' 1 (:: (:: (var.store 0) expected_but_found) my_v)))))))))))
      my_v))

def or_fail : Expr :=
  (quote (:: apply (:: Except'.err TFail)))

def infer.match_with (match_fn then_do : Expr) (or_else : Expr := or_fail) (match_other : Expr := id) : Expr :=
  (:: both (:: (quote apply)
    (:: both (::
      (:: both (:: (:: both (:: (quote eq) (:: both (::
        then_do
        or_else))))
        match_fn))
     match_other))))

def infer.self : Expr :=
  :: π (:: id nil)

/-
Runs infer again. Unsafe.

get_e has all args in scope.
-/
def infer_self_unsafe (get_e : Expr := (:: π (:: nil id))) : Expr :=
  (:: both (:: (quote apply) (:: both (::
    infer.self (:: both (:: infer.self get_e))))))

/-
nil : IList α.
Its type is dependent and varies on the type of the rest of the list.

(:: apply (:: (:: apply (:: infer_nil (:: infer_global))) x))
= (:: IList (:: apply (:: infer_global (:: infer_global x))))
-/
def infer_nil (or_else : Expr := or_fail) : Expr :=
  (infer.match_with
    (match_fn := (:: π (:: id (quote nil))))
    (then_do := (quote (:: both (:: (quote both) (:: both (::
      (quote IList)
      (:: both (:: (quote both) (:: both (:: (quote (quote apply))
      (:: both (:: (quote const) (:: both (:: infer.self infer.self))))))))))))))
    (quote or_else))

def mk_tlist : Expr :=
  :: both (:: (quote IList) id)

def throw_generic_expected (msg : String) : Expr :=
  (quote (:: both (:: (quote apply) (:: both (::
      (quote Except'.err)
      (:: both (:: (quote apply) (:: both (::
        (quote (:: apply (:: expected_but_found (symbol msg)))) id)))))))))

/-
then_do should usually be quoted.
-/
def guard_list (then_do : Expr) : Expr :=
  (infer.match_with
    (match_fn := (:: π (:: id (:: π (:: id id)))))
    (then_do := then_do)
    (or_else := (throw_generic_expected "a list"))
    (match_other := id))

/-
List inference is the top-level infer rule if no application
is detected.
-/
def infer_list : Expr :=
  guard_list <|
    (quote (infer.match_with
      (match_fn := (:: both (:: (quote IList) (infer_self_unsafe (get_e := (:: π (:: nil (:: π (:: id nil)))))))))
      (match_other := (infer_self_unsafe (get_e := (:: π (:: nil (:: π (:: nil id)))))))
      -- the type of the tail must be List α
      -- and the head must be α
      (then_do := (quote (:: both (:: (quote apply) (:: both (:: (quote (:: apply (:: Except'.map_with (:: mk_tlist id)))) id))))))
      (or_else := assert_eq)))

/-
A version of infer both that forms the type of f and g
by inference on x.

both :: ∀  (α : Type), (f : α → β) (g : α → β), List β
-/

/-
Infer apps by inferring the left side of the app, fn
and applying the argument to it.

Similar guard to infer_list.
-/
def infer_fn : Expr :=
  guard_list <|
    (quote (:: both
      (:: (quote apply) (::
        (infer_self_unsafe (get_e := (:: π (:: nil (:: π (:: id nil))))))
        (:: π (:: nil (:: π (:: nil id))))))))

/-
Apply can induce a function application.
Otherwise, data are type-checked as lists.
-/
def infer_apply : Expr :=
  (infer.match_with
    (match_fn := (:: π (:: id (:: π (:: (quote apply) id)))))
    (match_other := id)
    (then_do := (quote infer_fn))
    (or_else := (throw_generic_expected "a function application")))

/-
(:: apply (:: (:: apply (:: (:: apply (:: infer_both infer_global)) (:: f g))) x))
This creates a curried function that asserts that
-/
def infer_both.f : Expr :=
  (:: both (:: (quote apply) (:: both (::
    args.read 0 id 
    args.read 1 (:: π (:: id nil))

def infer_both.g : Expr :=
  args.read 1 (:: π (:: nil id))

def infer_both.arg : Expr :=
  args.read 2 id

def infer_both : Expr :=
  (:: apply (:: curry (:: apply (:: curry (::
    (infer.match_with
      (
  sorry

/-
For use with infer.
-/
def nat.type : Expr :=
  let do_rec := :: both (:: (quote apply) (:: π (:: (:: both (:: (quote apply) id)) id)))
  let succ_case := :: both (:: (quote apply) (:: both (:: (:: both (:: (:: both (::
    (quote eq) (:: both (::
      (quote (quote (:: apply (:: Except'.ok TNat))))
      (:: both (:: (quote const) do_rec))))))
      (quote Nat'.zero)))
      (:: π (:: nil id)))))
  (:: both (:: (quote apply) (:: both (::
    (quote (:: apply (:: nat.rec_with (:: nat.rec_with (:: (quote (:: apply (:: Except'.ok TNat))) succ_case)))))
    (:: π (:: nil id))))))

def infer.match_whole (whole : Expr) : Expr :=
  (:: π (:: id whole))

def infer : Expr :=
  infer_nil
  infer_list

#eval try_step_n' 100 (:: apply (:: infer_nil (:: infer nil)))

def infer' : Expr :=
  (:: both (:: (quote apply) (:: both (:: (quote infer) (:: both (:: (quote infer) id))))))

set_option maxRecDepth 5000
example : try_step_n' 500 (:: apply (:: (:: π (:: id (:: π (:: id nil)))) (:: apply (:: infer' (symbol "hi"))))) = (.ok (:: (symbol "error") (:: (symbol "expected:") (symbol "a list")))) := rfl
example : try_step_n' 500 (:: apply (:: infer' (:: nil nil))) = (.ok (:: Except'.s_ok (:: IList TData))) := rfl
example : try_step_n' 100 (:: apply (:: infer' nil)) = (.ok (:: Except'.s_ok TData)) := rfl

/-
At the very least, we need some mechanism to pattern match on Symbol.
If something isn't a list
-/
