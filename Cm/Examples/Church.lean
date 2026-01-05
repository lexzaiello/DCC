import Cm.Ast
import Cm.Eval
import Cm.Infer

/-
I derived from S with any t_x
-/
def mk_i (t_x : Expr) : Except Error Expr := do
  /-
    γ gets x and y, should return t_x
    γ (x :t_x) Data = t_x
    γ = K (K :t_t_x Data :t_x)
    γ :t_x Data = t_x
  -/
  let t_data ← infer ⟪₂ Data ⟫
  let t_t_x ← infer t_x
  let assert_t_x := ⟪₂ K' :t_t_x :t_data :t_x ⟫
  let t_assert_t_x ← infer assert_t_x

  let aa_t_x := ⟪₂ K' :t_assert_t_x :t_x :assert_t_x ⟫

  let t_t_data ← infer t_data

  pure ⟪₂ S :t_x (K' :t_t_data :t_x :t_data) :aa_t_x (K' :t_x :t_data) (K' :t_data :t_x Data) ⟫

def my_example : Except Error Expr := do
  let t_data ← infer ⟪₂ Data ⟫
  mk_i t_data

/-
I works, but we're probably messing up in at least one place.
-/
#eval Expr.display_infer <$> (my_example >>= (fun e => infer ⟪₂ :e Data ⟫))

def mk_flse (t_a t_b : Expr) : Except Error Expr := do
  let my_i ← ⟪₂ (#mk_i t_b) ⟫
  dbg_trace my_i
  let t_my_i ← infer my_i

  pure ⟪₂ K' :t_my_i :t_a :my_i ⟫

def test_my_i : Except Error Expr := do
  let t_data ← infer ⟪₂ Data ⟫

  mk_i t_data

/-
Testing a tuple / church-encoded bool storing the combinators S and K
next to each other.

false K S = S, but does it type-check?

An issue:
- in the explict type arguments for K' and S, we assume they are in "human readable format".

We were able to do mk_flse with just Data and Data,which is strange,
but we couldn't use the list formal.

Curious.

But we've been able to get nested examples working.

We did nested K.
So this shouldn't be a problem.
It's probably that we're assuming Data somewhere.

The issue is with our custom I.
-/
def mk_flse_test (a b : Expr) : Except Error Expr := do
  let t_a ← infer a
  let t_b ← infer b

  let my_false ← mk_flse t_a t_b

  pure ⟪₂ :my_false :a :b ⟫

#eval infer ⟪₂ Data ⟫
#eval Expr.display_infer <$> (infer ⟪₂ Data ⟫)
#eval Expr.display_infer <$> (mk_flse_test ⟪₂ Data ⟫ ⟪₂ Data ⟫
  >>= infer)


#eval mk_flse_test ⟪₂ K ⟫ ⟪₂ S ⟫
