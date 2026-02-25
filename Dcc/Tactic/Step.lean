import Dcc.Ast
import Dcc.Types
import Dcc.Tactic.Register

@[simp_dcc] theorem K.step : IsStep ⟪K.{[m, n]} α β x y⟫ x := IsStep.K
@[simp_dcc] theorem K'.step : IsStep ⟪K'.{[m, n]} α β x y⟫ x := IsStep.K'
@[simp_dcc] theorem S.step : IsStep ⟪S.{[m, n, o]} α β γ f g x⟫ ⟪f x (g x)⟫ := IsStep.S
@[simp_dcc] theorem MK'₁.stepM : IsStepM ⟪(M K'.{[m, n]}) α⟫ ⟪Π.{[n.succ, m]} (Sort n) (M (K'.{[m, n]} α))⟫ := IsStepM.k'₁
@[simp_dcc] theorem MK'₂.stepM : IsStepM ⟪(M (K'.{[m, n]} α)) β⟫ ⟪Π.{[m, m]} α (M (K'.{[m, n]} α β))⟫ := IsStepM.k'₂
@[simp_dcc] theorem MK'₃.stepM : IsStepM ⟪(M (K'.{[m, n]} α β)) x⟫ ⟪Π.{[m, m]} β (K'.{[m.succ, n]} (Sort m) β α)⟫ := IsStepM.k'₃
@[simp_dcc] theorem MK'₄.step : IsStep ⟪(K'.{[m.succ, n]} (Sort m) β α) y⟫ α := IsStep.K'
