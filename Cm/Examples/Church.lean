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

  /-
    It keeps getting stuck at the x argument.
    Why is this?
    x : ∀ (x : α) (y : β x), γ x y
    We've seen that γ works already.
  -/

  pure ⟪₂ S :t_x (K' :t_t_data :t_x :t_data) :aa_t_x (K' :t_x :t_data) (K' :t_data :t_x Data) ⟫

def my_examplebruh : Except Error Expr := do
  let t_data ← infer ⟪₂ Data ⟫
  let my_i ← mk_i t_data
  pure ⟪₂ :my_i Data ⟫

#eval my_examplebruh >>= infer

def my_examplebruh2 : Except Error Expr := do
  let t_data ← infer ⟪₂ K ⟫
  let my_i ← mk_i t_data
  pure ⟪₂ :my_i ⟫

#eval my_examplebruh2
  >>= infer

#eval Expr.display_infer <$> (my_example >>= infer)

def mk_i_example (x : Expr) : Except Error Expr := do
  let t_x ← infer x
  (fun e => ⟪₂ :e :x ⟫) <$> mk_i t_x

/-
I works, but we're probably messing up in at least one place.
-/

def mk_flse (t_a t_b : Expr) : Except Error Expr := do
  let my_i ← ⟪₂ (#mk_i t_b) ⟫
  let t_my_i ← infer my_i

  pure ⟪₂ K' :t_my_i :t_a :my_i ⟫

def test_my_i : Except Error Expr := do
  let t_data ← infer ⟪₂ Data ⟫

  mk_i t_data

def mk_flse_test (a b : Expr) : Except Error Expr := do
  let t_a ← infer a
  let t_b ← infer b

  let my_false ← mk_flse t_a t_b

  pure ⟪₂ :my_false :a :b ⟫

#eval infer ⟪₂ Data ⟫
#eval Expr.display_infer <$> (infer ⟪₂ Data ⟫)
#eval Expr.display_infer <$> (mk_flse_test ⟪₂ Data ⟫ ⟪₂ Data ⟫
  >>= infer)

#eval (mk_flse_test ⟪₂ K ⟫ ⟪₂ S ⟫
  >>= infer)
  >>= (fun t_out => do
    pure (t_out == (← infer ⟪₂ S ⟫)))



