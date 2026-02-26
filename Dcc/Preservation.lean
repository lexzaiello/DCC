import Dcc.Ast
import Dcc.Types
import Dcc.Tactic.Simp

#print K'.judge

theorem K'.well_typed' (h_t_α : ValidJudgment ⟪Sort m⟫ α)
  (h_t_β : ValidJudgment ⟪Sort n⟫ β)
  (h_t_x : ValidJudgment α x)
  (h_t_y : ValidJudgment β y) : ValidJudgment α ⟪K'.{[m, n]} α β x y⟫ := by
  judge app, app, app, app
  simp [K'.judge]
  sorry

theorem K'.well_typed (h_t_α : ValidJudgment ⟪Sort m⟫ α)
  (h_t_β : ValidJudgment ⟪Sort n⟫ β)
  (h_t_x : ValidJudgment α x)
  (h_t_y : ValidJudgment β y) : ValidJudgment α ⟪K'.{[m, n]} α β x y⟫ := by
  judge app, app, app, app, K'
  defeq refl
  assumption
  defeq step
  stepM k'₁
  defeq refl
  assumption
  defeq step
  stepM k'₂
  defeq refl
  assumption
  defeq step
  stepM k'₃
  defeq refl
  assumption
  defeq step
  step K'

@[simp]
theorem K.well_typed (h_t_α : ValidJudgment ⟪Sort m⟫ α)
  (h_t_β : ValidJudgment (mk_arrow α ⟪Sort n⟫ m n.succ) β)
  (h_t_x : ValidJudgment α x)
  (h_t_y : ValidJudgment ⟪β x⟫ y) : ValidJudgment α ⟪K.{[m, n]} α β x y⟫ := by
  judge app, app, app, app, K
  defeq refl
  assumption
  defeq step
  stepM k₁
  defeq refl
  assumption
  defeq step
  stepM k₂
  defeq refl
  assumption
  defeq step
  stepM k₃
  defeq refl
  assumption
  defeq step
  stepM k₄

@[simp] theorem K.preservation  : ValidJudgment α x → ValidJudgment α x := id
@[simp] theorem K'.preservation : ValidJudgment α x → ValidJudgment α x := id

@[simp]
theorem S.well_typed (h_t_α : ValidJudgment ⟪Sort m⟫ α)
  (h_t_β : ValidJudgment (mk_arrow α ⟪Sort n⟫ m n.succ) β)
  (h_t_γ : ValidJudgment ⟪(Π.{[m, o.succ.succ]} α (M (Sγ.{[m, n, o]} α β)))⟫ γ)
  (h_t_f : ValidJudgment ⟪(Π.{[m, o]} α (M (Sf.{[m, n, o]} α β γ)))⟫ f)
  (h_t_g : ValidJudgment ⟪(Π.{[m, n]} α β)⟫ g)
  (h_t_x : ValidJudgment α x)
  : ValidJudgment ⟪γ x (g x)⟫ ⟪S.{[m, n, o]} α β γ f g x⟫ := by
  judge app, app, app, app, app, app, S
  defeq refl
  assumption
  defeq step
  stepM s₁
  defeq refl
  assumption
  defeq step
  stepM s₂
  defeq refl
  assumption
  defeq step
  stepM s₃
  defeq refl
  assumption
  defeq step
  stepM s₄
  defeq refl
  assumption
  defeq step
  stepM s₅
  defeq refl
  assumption
  defeq step
  stepM s₆

@[simp]
theorem S.preservation (h_t_f : ValidJudgment ⟪(Π.{[m, o]} α (M (Sf.{[m, n, o]} α β γ)))⟫ f)
  (h_t_g : ValidJudgment ⟪(Π.{[m, n]} α β)⟫ g)
  (h_t_x : ValidJudgment α x) :
  ValidJudgment ((γ.app x).app (g.app x)) ⟪f x (g x)⟫ := by
  judge app, app
  assumption
  defeq refl
  assumption
  defeq step
  stepM F₁
  defeq refl
  judge app
  assumption
  defeq refl
  assumption
  defeq refl
  defeq refl
