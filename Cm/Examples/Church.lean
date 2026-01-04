import Cm.Ast
import Cm.Eval
import Cm.Infer

/-
I derived from S with any t_x
-/
def mk_i (t_x : Expr) : Option Expr := do
  /-
    γ gets x and y, should return t_x
    γ (x :t_x) Data = t_x
  -/
  let assert_t_x := ⟪₂ K' Data Data :t_x ⟫
  let t_assert_t_x ← infer assert_t_x

  let aa_t_x := ⟪₂ K' :t_assert_t_x :t_x :assert_t_x ⟫

  ⟪₂ S :t_x (K' Data :t_x Data) :aa_t_x (K' :t_x Data) (K' Data :t_x Data) ⟫

#eval mk_i ⟪₂ Data ⟫
  >>= (fun e => infer ⟪₂ :e Data ⟫ true >>= Expr.display_infer)

def mk_flse (t_a t_b : Expr) : Option Expr := do
  let my_i ← ⟪₂ (#mk_i t_b) ⟫
  let t_my_i ← infer my_i

  ⟪₂ K' :t_my_i :t_a :my_i ⟫

#eval mk_flse ⟪₂ Data ⟫ ⟪₂ Data ⟫
  >>= (fun c =>
    infer ⟪₂ :c Data ⟫ true)

def mk_test : Option Expr := do
  let a := ⟪₂ K ⟫
  let b := ⟪₂ S ⟫

  let t_a ← infer a
  let t_b ← infer b

  let my_flse ← mk_flse t_a t_b

  ⟪₂ :my_flse :a :b ⟫


