import Dcc.Ast
import Dcc.Types

@[simp] theorem Pi.step {α β x : Expr} {m n : Level} : IsStep ⟪Π.{[m, n]} α β x⟫ ⟪β x⟫ := IsStep.pi
@[simp] theorem K.step {α β x y : Expr} {m n : Level} : IsStep ⟪K.{[m, n]} α β x y⟫ x := IsStep.K
@[simp] theorem K'.step {α β x y : Expr} {m n : Level} : IsStep ⟪K'.{[m, n]} α β x y⟫ x := IsStep.K'
@[simp] theorem S.step {α β γ x y z : Expr} {m n : Level} : IsStep ⟪S.{[m, n, o]} α β γ x y z⟫ ⟪x z (y z)⟫ := IsStep.S
@[simp] theorem MK'₁.defeq {α : Expr} {m n : Level}  : DefEq
  ⟪Π.{[n.succ, m]} (Sort n) (M (K'.{[m, n]} α))⟫ ⟪(M K'.{[m, n]}) α⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k'₁
@[simp] theorem MK'₂.defeq {α β : Expr} {m n : Level} : DefEq ⟪Π.{[m, m]} α (M (K'.{[m, n]} α β))⟫ ⟪(M (K'.{[m, n]} α)) β⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k'₂
@[simp] theorem MK'₃.defeq {α β x : Expr} {m n : Level} : DefEq ⟪Π.{[m, m]} β (K'.{[m.succ, n]} (Sort m) β α)⟫ ⟪(M (K'.{[m, n]} α β)) x⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k'₃
@[simp] theorem MK'₄.step {α β y : Expr} {m n : Level} : IsStep ⟪(K'.{[m.succ, n]} (Sort m) β α) y⟫ α := IsStep.K'
@[simp] theorem MK₁.defeq : DefEq ⟪Π.{[n.succ.succ, m]}
    α_to_set.{[m, n]}(α)
    (M (K.{[m, n]} α))⟫ ⟪(M K.{[m, n]}) α⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k₁
@[simp] theorem MK₂.defeq {α β : Expr} {m n : Level} : DefEq
  ⟪Π.{[m, m]} α (M (K.{[m, n]} α β))⟫ ⟪(M (K.{[m, n]} α)) β⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k₂
@[simp] theorem MK₃.defeq {α β x : Expr} {m n : Level} : DefEq
  ⟪Π.{[m, m]} (β x) (M (K.{[m, n]} α β x))⟫ ⟪(M (K.{[m, n]} α β)) x⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k₃
@[simp] theorem MK₄.stepM {α β x : Expr} {m n : Level} : IsStepM ⟪(M (K.{[m, n]} α β x)) y⟫ α := IsStepM.k₄
@[simp] theorem Sγ₂.defeq {α β x : Expr} {m n o : Level} : DefEq ⟪βx_to_set.{[n, o]}(β, x)⟫ ⟪(M (Sγ.{[m, n, o]} α β)) x⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.sγ
@[simp] theorem Sf₁.stepM {α β γ x : Expr} {m n o : Level} : IsStepM ⟪(M (Sf.{[m, n, o]} α β γ)) x⟫ ⟪Π.{[n, o]} (β x) (γ x)⟫ := IsStepM.sf
@[simp] theorem S₁.defeq {α : Expr} {m n o : Level} : DefEq
  ⟪Π.{[n.succ.succ, o]} (α_to_set.{[m, n]}(α)) (M (S.{[m, n, o]} α))⟫
  ⟪(M S.{[m, n, o]}) α⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₁
@[simp] theorem S₂.stepM {α β : Expr} {m n o : Level} : DefEq
  ⟪Π.{[o.succ.succ, o]}
    (Π.{[m, o.succ.succ]} α (M (Sγ.{[m, n, o]} α β)))
    (M (S.{[m, n, o]} α β))⟫
  ⟪(M (S.{[m, n, o]} α)) β⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₂
@[simp] theorem S₃.stepM {α β γ : Expr} {m n o : Level} : DefEq
  ⟪Π.{[o, o]} (Π.{[m, o]} α (M (Sf.{[m, n, o]} α β γ)))
    (M (S.{[m, n, o]} α β γ))⟫
  ⟪(M (S.{[m, n, o]} α β)) γ⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₃
@[simp] theorem S₄.stepM {α β γ x : Expr} {m n o : Level} : DefEq
  ⟪Π.{[n, o]} (Π.{[m, n]} α β)
    (M (S.{[m, n, o]} α β γ x))⟫
  ⟪(M (S.{[m, n, o]} α β γ)) x⟫  := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₄
@[simp] theorem S₅.stepM {α β γ x y : Expr} {m n o : Level} : DefEq
  ⟪Π.{[m, o]} α
    (M (S.{[m, n, o]} α β γ x y))⟫
  ⟪(M (S.{[m, n, o]} α β γ x)) y⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₅
@[simp] theorem S₆.stepM {α β γ x y z : Expr} {m n o : Level} : IsStepM ⟪(M (S.{[m, n, o]} α β γ x y)) z⟫ ⟪γ z (y z)⟫ := IsStepM.s₆

@[simp] theorem M.step {m₁ m₂ : Expr} : IsStepM m₁ m₂ → IsStep m₁ m₂ := IsStep.M
@[simp] theorem IsStep.defeq {x x' : Expr} : IsStep x x' → DefEq x x' := DefEq.step
@[simp] theorem IsStepM.defeq {x x' : Expr} : IsStepM x x' → DefEq x x' := DefEq.step ∘ IsStep.M

@[simp] theorem Sort.judge {m : Level} : ValidJudgment ⟪Sort.type.{[m]}⟫ ⟪Sort m⟫ := ValidJudgment.Sort
@[simp] theorem S.judge {m n o : Level} : ValidJudgment ⟪S.type.{[m, n, o]}⟫ ⟪S.{[m, n, o]}⟫ := ValidJudgment.S
@[simp] theorem K.judge {m n : Level} : ValidJudgment ⟪K.type.{[m, n]}⟫ ⟪K.{[m, n]}⟫ := ValidJudgment.K
@[simp] theorem K'.judge {m n : Level} : ValidJudgment ⟪K'.type.{[m, n]}⟫ ⟪K'.{[m, n]}⟫ := ValidJudgment.K'
@[simp] theorem Pi.judge {m n : Level} : ValidJudgment ⟪Π.type.{[m, n]}⟫ ⟪Π.{[m, n]}⟫ := ValidJudgment.Pi
@[simp] theorem MK.judge {m n : Level} : ValidJudgment ⟪MK.type.{[m, n]}⟫ ⟪M K.{[m, n]}⟫ := ValidJudgment.MK
@[simp] theorem MK'.judge {m n : Level} : ValidJudgment ⟪MK'.type.{[m, n]}⟫ ⟪M K'.{[m, n]}⟫ := ValidJudgment.MK'
@[simp] theorem MS.judge {m n o : Level} : ValidJudgment ⟪MS.type.{[m, n, o]}⟫ ⟪M S.{[m, n, o]}⟫ := ValidJudgment.MS
@[simp] theorem App.judge {m n : Level} {α cod f x : Expr} : ValidJudgment ⟪Π.{[m, n]} α cod⟫ f
    → ValidJudgment α x
    → ValidJudgment ⟪cod x⟫ ⟪f x⟫ := by
  intro h_t_f h_t_x
  apply ValidJudgment.app
  assumption
  assumption
@[simp] theorem Step.defeq : IsStep e e' → DefEq e e' := DefEq.step
@[simp] theorem StepM.defeq : IsStepM e e' → DefEq e e' := DefEq.step ∘ IsStep.M
