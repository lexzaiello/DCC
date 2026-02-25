import Dcc.Ast
import Dcc.Types
import Dcc.Tactic.Register

@[simp_dcc] theorem K.step : IsStep ⟪K.{[m, n]} α β x y⟫ x := IsStep.K
@[simp_dcc] theorem K'.step : IsStep ⟪K'.{[m, n]} α β x y⟫ x := IsStep.K'
@[simp_dcc] theorem S.step : IsStep ⟪S.{[m, n, o]} α β γ f g x⟫ ⟪f x (g x)⟫ := IsStep.S
@[simp_dcc] theorem MK'₁.defeq : DefEq ⟪Π.{[n.succ, m]} (Sort n) (M (K'.{[m, n]} α))⟫ ⟪(M K'.{[m, n]}) α⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k'₁
@[simp_dcc] theorem MK'₂.defeq : DefEq ⟪Π.{[m, m]} α (M (K'.{[m, n]} α β))⟫ ⟪(M (K'.{[m, n]} α)) β⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k'₂
@[simp_dcc] theorem MK'₃.defeq : DefEq ⟪Π.{[m, m]} β (K'.{[m.succ, n]} (Sort m) β α)⟫ ⟪(M (K'.{[m, n]} α β)) x⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k'₃
@[simp_dcc] theorem MK'₄.step : IsStep ⟪(K'.{[m.succ, n]} (Sort m) β α) y⟫ α := IsStep.K'
@[simp_dcc] theorem MK₁.defeq : DefEq ⟪Π.{[n.succ.succ, m]}
    (#α_to_set α m n)
    (M (K.{[m, n]} α))⟫ ⟪(M K.{[m, n]}) α⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k₁
@[simp_dcc] theorem MK₂.defeq : DefEq ⟪Π.{[m, m]} α (M (K.{[m, n]} α β))⟫ ⟪(M (K.{[m, n]} α)) β⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k₂
@[simp_dcc] theorem MK₃.defeq : DefEq  ⟪Π.{[m, m]} (β x) (M (K.{[m, n]} α β x))⟫ ⟪(M (K.{[m, n]} α β)) x⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k₃
@[simp_dcc] theorem MK₄.stepM : IsStepM ⟪(M (K.{[m, n]} α β x)) y⟫ α := IsStepM.k₄
@[simp_dcc] theorem Sγ₂.defeq : DefEq (βx_to_set β x n o) ⟪(M (Sγ.{[m, n, o]} α β)) x⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.γ₂
@[simp_dcc] theorem Sf₁.stepM : IsStepM ⟪(M (Sf.{[m, n, o]} α β γ)) x⟫ ⟪Π.{[n, o]} (β x) (γ x)⟫ := IsStepM.F₁
@[simp_dcc] theorem S₁.defeq : DefEq
  ⟪Π.{[n.succ.succ, o]} (#α_to_set α m n) (M (S.{[m, n, o]} α))⟫
  ⟪(M S.{[m, n, o]}) α⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₁
@[simp_dcc] theorem S₂.stepM : DefEq
  ⟪Π.{[o.succ.succ, o]}
    (Π.{[m, o.succ.succ]} α (M (Sγ.{[m, n, o]} α β)))
    (M (S.{[m, n, o]} α β))⟫
  ⟪(M (S.{[m, n, o]} α)) β⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₂
@[simp_dcc] theorem S₃.stepM : DefEq
  ⟪Π.{[o, o]} (Π.{[m, o]} α (M (Sf.{[m, n, o]} α β γ)))
    (M (S.{[m, n, o]} α β γ))⟫
  ⟪(M (S.{[m, n, o]} α β)) γ⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₃
@[simp_dcc] theorem S₄.stepM : DefEq
  ⟪Π.{[n, o]} (Π.{[m, n]} α β)
    (M (S.{[m, n, o]} α β γ x))⟫
  ⟪(M (S.{[m, n, o]} α β γ)) x⟫  := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₄
@[simp_dcc] theorem S₅.stepM : DefEq
  ⟪Π.{[m, o]} α
    (M (S.{[m, n, o]} α β γ x y))⟫
  ⟪(M (S.{[m, n, o]} α β γ x)) y⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₅
@[simp_dcc] theorem S₆.stepM : IsStepM ⟪(M (S.{[m, n, o]} α β γ x y)) z⟫ ⟪γ z (y z)⟫ := IsStepM.s₆

