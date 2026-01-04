import Cm.Ast
import Cm.Eval
import Cm.Infer

/-
I derived from S with any t_x
-/
def mk_i (t_x : Expr) : Expr :=
  dbg_trace ⟪₂ K' :t_x Data ⟫
  ⟪₂ S :t_x (K' Data :t_x Data) (K' :t_x Data) (K' :t_x Data) (K' Data :t_x Data) ⟫

def nested_example : Option Expr := do
  let inner_k := ⟪₂ K' Data Data ⟫
  let t_k ← infer inner_k

  ⟪₂ K' :t_k Data :inner_k ⟫

#eval nested_example >>= (fun e => infer ⟪₂ :e Data Data Data ⟫)

#eval Expr.display_infer <$> infer ⟪₂ (#mk_i ⟪₂ Data ⟫) Data ⟫

def mk_tre (t_a t_b : Expr) : Expr :=
  ⟪₂ K' :t_a :t_b ⟫

def mk_flse (t_a t_b : Expr) : Option Expr := do
  let my_i := ⟪₂ (#mk_i t_b) ⟫
  dbg_trace my_i
  let t_my_i ← infer my_i

  ⟪₂ K' :t_my_i :t_a :my_i ⟫

def mk_test : Option Expr := do
  let a := ⟪₂ K ⟫
  let b := ⟪₂ S ⟫

  let t_a ← infer a
  let t_b ← infer b

  let my_flse ← mk_flse t_a t_b

  ⟪₂ :my_flse :a :b ⟫

#eval mk_test

def mk_church (t_f t_x : Expr) : Option Expr :=
  
