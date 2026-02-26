import Dcc.Ast
import Dcc.Types

register_simp_attr simp_dcc

@[simp] theorem K.step : IsStep ⟪K.{[m, n]} α β x y⟫ x := IsStep.K
@[simp] theorem K'.step : IsStep ⟪K'.{[m, n]} α β x y⟫ x := IsStep.K'
@[simp] theorem S.step : IsStep ⟪S.{[m, n, o]} α β γ f g x⟫ ⟪f x (g x)⟫ := IsStep.S
@[simp] theorem MK'₁.stepM : IsStepM ⟪(M K'.{[m, n]}) α⟫ ⟪Π.{[n.succ, m]} (Sort n) (M (K'.{[m, n]} α))⟫ := IsStepM.k'₁
@[simp] theorem MK'₂.stepM : IsStepM ⟪(M (K'.{[m, n]} α)) β⟫ ⟪Π.{[m, m]} α (M (K'.{[m, n]} α β))⟫ := IsStepM.k'₂
@[simp] theorem MK'₃.stepM : IsStepM ⟪(M (K'.{[m, n]} α β)) x⟫ ⟪Π.{[m, m]} β (K'.{[m.succ, n]} (Sort m) β α)⟫ := IsStepM.k'₃
@[simp] theorem MK'₄.step : IsStep ⟪(K'.{[m.succ, n]} (Sort m) β α) y⟫ α := by simp
