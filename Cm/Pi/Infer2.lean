import Cm.Pi.Ast
import Cm.Pi.Eval
import Cm.Pi.Std.Util
import Cm.Pi.Std.Except

open Expr

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

def infer_nil (or_else : Expr := or_fail) : Expr :=
  (infer.match_with
    (match_fn := (:: π (:: id (quote nil))))
    (then_do := (quote (quote (:: apply (:: Except'.ok TData)))))
    (quote or_else))

def mk_tlist : Expr :=
  :: both (:: (quote IList) id)

/-
List inference is the top-level infer rule if no application
is detected.
-/
def infer_list : Expr :=
  (infer.match_with
    (match_fn := (:: π (:: id (:: π (:: id id)))))
    (then_do :=
      (quote (infer.match_with
        (match_fn := (infer_self_unsafe (get_e := (:: π (:: nil (:: π (:: id nil)))))))
        (match_other := (infer_self_unsafe (get_e := (:: π (:: nil (:: π (:: nil id)))))))
        -- if the types of the head and the tail are equal, then the type is List α
        -- although, they might both be Except values, so map those
        (then_do := (quote (:: both (:: (quote apply) (:: both (:: (quote (:: apply (:: Except'.map_with (:: mk_tlist id)))) id))))))
        (or_else := assert_eq))))
    (or_else := (quote (:: both (:: (quote apply) (:: both (::
      (quote Except'.err)
      (:: both (:: (quote apply) (:: both (::
        (quote (:: apply (:: expected_but_found (symbol "a list")))) id))))))))))
    (match_other := id))

/-
A version of infer both that forms the type of f and g
by inference on x.

both :: ∀  (α : Type), (f : α → β) (g : α → β), List β
-/

def infer_fn : Expr :=
  sorry

/-def infer_apply : Expr :=
  (infer.match_with
    (match_fn := (:: π (:: id (:: π (:: (quote apply) id)))))
    (match_other := id)
    (then_do := (quote infer_fn))
    (or_else := -/

/-
(:: apply (:: (:: apply (:: (:: apply (:: infer_both infer_global)) (:: f g))) x))
-/
def infer_both : Expr :=
  sorry

def infer.match_whole (whole : Expr) : Expr :=
  (:: π (:: id whole))

def infer : Expr :=
  infer_nil
  infer_list

def infer' : Expr :=
  (:: both (:: (quote apply) (:: both (:: (quote infer) (:: both (:: (quote infer) id))))))

set_option maxRecDepth 5000
example : try_step_n' 500 (:: apply (:: (:: π (:: id (:: π (:: id nil)))) (:: apply (:: infer' (symbol "hi"))))) = (.ok (:: (symbol "error") (:: (symbol "expected:") (symbol "a list")))) := rfl
example : try_step_n' 500 (:: apply (:: infer' (:: nil nil))) = (.ok (:: Except'.s_ok (:: IList TData))) := rfl
example : try_step_n' 100 (:: apply (:: infer' nil)) = (.ok (:: Except'.s_ok TData)) := rfl
