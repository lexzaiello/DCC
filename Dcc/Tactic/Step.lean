import Dcc.Ast
import Dcc.Types
import Dcc.Tactic.Register

@[simp_dcc] theorem Pi.step {α β x : Expr} {m n : Level} : IsStep ⟪Π.{[m, n]} α β x⟫ ⟪β x⟫ := IsStep.pi
@[simp_dcc] theorem K.defeq {α β x y : Expr} {m n : Level} : IsStep ⟪K.{[m, n]} α β x y⟫ x := IsStep.K
@[simp_dcc] theorem K'.defeq {α β x y : Expr} {m n : Level} : IsStep ⟪K'.{[m, n]} α β x y⟫ x := IsStep.K'
@[simp_dcc] theorem S.defeq {α β γ x y z : Expr} {m n : Level} : IsStep ⟪S.{[m, n, o]} α β γ x y z⟫ ⟪x z (y z)⟫ := IsStep.S
@[simp_dcc] theorem MK'₁.defeq {α : Expr} {m n : Level}  : DefEq
  ⟪Π.{[n.succ, m]} (Sort n) (M (K'.{[m, n]} α))⟫ ⟪(M K'.{[m, n]}) α⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k'₁
@[simp_dcc] theorem MK'₂.defeq {α β : Expr} {m n : Level} : DefEq ⟪Π.{[m, m]} α (M (K'.{[m, n]} α β))⟫ ⟪(M (K'.{[m, n]} α)) β⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k'₂
@[simp_dcc] theorem MK'₃.defeq {α β x : Expr} {m n : Level} : DefEq ⟪Π.{[m, m]} β (K'.{[m.succ, n]} (Sort m) β α)⟫ ⟪(M (K'.{[m, n]} α β)) x⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k'₃
@[simp_dcc] theorem MK'₄.step {α β y : Expr} {m n : Level} : IsStep ⟪(K'.{[m.succ, n]} (Sort m) β α) y⟫ α := IsStep.K'
@[simp_dcc] theorem MK₁.defeq : DefEq ⟪Π.{[n.succ.succ, m]}
    (#α_to_set α m n)
    (M (K.{[m, n]} α))⟫ ⟪(M K.{[m, n]}) α⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k₁
@[simp_dcc] theorem MK₂.defeq {α β : Expr} {m n : Level} : DefEq
  ⟪Π.{[m, m]} α (M (K.{[m, n]} α β))⟫ ⟪(M (K.{[m, n]} α)) β⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k₂
@[simp_dcc] theorem MK₃.defeq {α β x : Expr} {m n : Level} : DefEq
  ⟪Π.{[m, m]} (β x) (M (K.{[m, n]} α β x))⟫ ⟪(M (K.{[m, n]} α β)) x⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.k₃
@[simp_dcc] theorem MK₄.stepM {α β x : Expr} {m n : Level} : IsStepM ⟪(M (K.{[m, n]} α β x)) y⟫ α := IsStepM.k₄
@[simp_dcc] theorem Sγ₂.defeq {α β x : Expr} {m n o : Level} : DefEq (βx_to_set β x n o) ⟪(M (Sγ.{[m, n, o]} α β)) x⟫ :=
  DefEq.symm <|DefEq.step <| IsStep.M IsStepM.γ₂
@[simp_dcc] theorem Sf₁.stepM {α β γ x : Expr} {m n o : Level} : IsStepM ⟪(M (Sf.{[m, n, o]} α β γ)) x⟫ ⟪Π.{[n, o]} (β x) (γ x)⟫ := IsStepM.F₁
@[simp_dcc] theorem S₁.defeq {α : Expr} {m n o : Level} : DefEq
  ⟪Π.{[n.succ.succ, o]} (#α_to_set α m n) (M (S.{[m, n, o]} α))⟫
  ⟪(M S.{[m, n, o]}) α⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₁
@[simp_dcc] theorem S₂.stepM {α β : Expr} {m n o : Level} : DefEq
  ⟪Π.{[o.succ.succ, o]}
    (Π.{[m, o.succ.succ]} α (M (Sγ.{[m, n, o]} α β)))
    (M (S.{[m, n, o]} α β))⟫
  ⟪(M (S.{[m, n, o]} α)) β⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₂
@[simp_dcc] theorem S₃.stepM {α β γ : Expr} {m n o : Level} : DefEq
  ⟪Π.{[o, o]} (Π.{[m, o]} α (M (Sf.{[m, n, o]} α β γ)))
    (M (S.{[m, n, o]} α β γ))⟫
  ⟪(M (S.{[m, n, o]} α β)) γ⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₃
@[simp_dcc] theorem S₄.stepM {α β γ x : Expr} {m n o : Level} : DefEq
  ⟪Π.{[n, o]} (Π.{[m, n]} α β)
    (M (S.{[m, n, o]} α β γ x))⟫
  ⟪(M (S.{[m, n, o]} α β γ)) x⟫  := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₄
@[simp_dcc] theorem S₅.stepM {α β γ x y : Expr} {m n o : Level} : DefEq
  ⟪Π.{[m, o]} α
    (M (S.{[m, n, o]} α β γ x y))⟫
  ⟪(M (S.{[m, n, o]} α β γ x)) y⟫ := DefEq.symm <|DefEq.step <| IsStep.M IsStepM.s₅
@[simp_dcc] theorem S₆.stepM {α β γ x y z : Expr} {m n o : Level} : IsStepM ⟪(M (S.{[m, n, o]} α β γ x y)) z⟫ ⟪γ z (y z)⟫ := IsStepM.s₆

@[simp_dcc] theorem M.step {m₁ m₂ : Expr} : IsStepM m₁ m₂ → IsStep m₁ m₂ := IsStep.M
@[simp_dcc] theorem IsStep.defeq {x x' : Expr} : IsStep x x' → DefEq x x' := DefEq.step
@[simp_dcc] theorem IsStepM.defeq {x x' : Expr} : IsStepM x x' → DefEq x x' := DefEq.step ∘ IsStep.M

@[simp_dcc] theorem Sort.judge {m : Level} : ValidJudgment (Sort.type m) ⟪Sort m⟫ := ValidJudgment.Sort
@[simp_dcc] theorem S.judge {m n o : Level} : ValidJudgment (S.type m n o) ⟪S.{[m, n, o]}⟫ := ValidJudgment.S
@[simp_dcc] theorem K.judge {m n : Level} : ValidJudgment (K.type m n) ⟪K.{[m, n]}⟫ := ValidJudgment.K
@[simp_dcc] theorem K'.judge {m n : Level} : ValidJudgment (K'.type m n) ⟪K'.{[m, n]}⟫ := ValidJudgment.K'
@[simp_dcc] theorem Pi.judge {m n : Level} : ValidJudgment (Pi.type m n) ⟪Π.{[m, n]}⟫ := ValidJudgment.Pi
@[simp_dcc] theorem MK.judge {m n : Level} : ValidJudgment (MK.type m n) ⟪M K.{[m, n]}⟫ := ValidJudgment.MK
@[simp_dcc] theorem MK'.judge {m n : Level} : ValidJudgment (MK'.type m n) ⟪M K'.{[m, n]}⟫ := ValidJudgment.MK'
@[simp_dcc] theorem MS.judge {m n o : Level} : ValidJudgment (MS.type m n o) ⟪M S.{[m, n, o]}⟫ := ValidJudgment.MS
@[simp_dcc] theorem App.judge {m n : Level} {α cod f x t' : Expr} : ValidJudgment ⟪Π.{[m, n]} α cod⟫ f
    → ValidJudgment α x
    → DefEq ⟪cod x⟫ t'
    → ValidJudgment t' ⟪f x⟫ := by
  intro h_t_f h_t_x
  apply ValidJudgment.app
  assumption
  defeq refl
  assumption
@[simp_dcc] theorem App.judge' {m n : Level} {α cod f x : Expr} : ValidJudgment ⟪Π.{[m, n]} α cod⟫ f
    → ValidJudgment α x
    → ValidJudgment ⟪cod x⟫ ⟪f x⟫ := by
  intro h_t_f h_t_x
  apply ValidJudgment.app
  assumption
  defeq refl
  assumption
  defeq refl
@[simp_dcc] theorem Step.defeq : IsStep e e' → DefEq e e' := DefEq.step
@[simp_dcc] theorem StepM.defeq : IsStepM e e' → DefEq e e' := DefEq.step ∘ IsStep.M
