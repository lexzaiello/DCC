import Dcc.Ast
import Dcc.Types

@[simp] theorem K'.well_typed (h_t_α : ValidJudgment ⟪Sort m⟫ α)
  (h_t_β : ValidJudgment ⟪Sort n⟫ β)
  (h_t_x : ValidJudgment α x)
  (h_t_y : ValidJudgment β y) : ValidJudgment α ⟪K'.{[m, n]} α β x y⟫ := by
  judge.defeq [judge [app], judge [app], judge [app], judge [app]]
  judge [K']
  assumption
  ← defeq.step [step.M [stepM [k'₁]]]
  assumption
  ← defeq.step [step.M [stepM [k'₂]]]
  assumption
  ← defeq.step [step.M [stepM [k'₃]]]
  assumption
  ← defeq.step [step [K']]

@[simp] theorem K.well_typed (h_t_α : ValidJudgment ⟪Sort m⟫ α)
  (h_t_β : ValidJudgment ⟪mk_arrow.{[m, n.succ]}(α, Sort n)⟫ β)
  (h_t_x : ValidJudgment α x)
  (h_t_y : ValidJudgment ⟪β x⟫ y) : ValidJudgment α ⟪K.{[m, n]} α β x y⟫ := by
  judgeEq app, app, app, app
  judge K
  assumption
  stepM k₁
  step? refl
  assumption
  stepM k₂
  step? refl
  assumption
  stepM k₃
  step? refl
  assumption
  stepM k₄
  step? refl

@[simp] theorem K.preservation  : ValidJudgment α x → ValidJudgment α x := id
@[simp] theorem K'.preservation : ValidJudgment α x → ValidJudgment α x := id

@[simp] theorem S.well_typed (h_t_α : ValidJudgment ⟪Sort m⟫ α)
  (h_t_β : ValidJudgment ⟪mk_arrow.{[m, n.succ]}(α, Sort n)⟫ β)
  (h_t_γ : ValidJudgment ⟪(Π.{[m, o.succ.succ]} α (M (Sγ.{[m, n, o]} α β)))⟫ γ)
  (h_t_f : ValidJudgment ⟪(Π.{[m, o]} α (M (Sf.{[m, n, o]} α β γ)))⟫ f)
  (h_t_g : ValidJudgment ⟪(Π.{[m, n]} α β)⟫ g)
  (h_t_x : ValidJudgment α x)
  : ValidJudgment ⟪γ x (g x)⟫ ⟪S.{[m, n, o]} α β γ f g x⟫ := by
  judgeEq app, app, app, app, app, app
  judge S
  assumption
  stepM s₁
  step? refl
  assumption
  stepM s₂
  step? refl
  assumption
  stepM s₃
  step? refl
  assumption
  stepM s₄
  step? refl
  assumption
  stepM s₅
  step? refl
  assumption
  stepM s₆
  step? refl

@[simp] theorem S.preservation (h_t_f : ValidJudgment ⟪(Π.{[m, o]} α (M (Sf.{[m, n, o]} α β γ)))⟫ f)
  (h_t_g : ValidJudgment ⟪(Π.{[m, n]} α β)⟫ g)
  (h_t_x : ValidJudgment α x) :
  ValidJudgment ((γ.app x).app (g.app x)) ⟪f x (g x)⟫ := by
  judge app, app
  repeat assumption
  stepM sf
  judge app
  repeat assumption
  step? refl, refl, refl

theorem preservation (h_t : ValidJudgment t e) (h_step : IsStep e e') : ValidJudgment t e' := by
  induction h_t generalizing e'
  repeat contradiction
  case defeq ih =>
    judge defeq
    exact ih h_step
    assumption
  case app m n α cod f x t' h_t_f h_t_x h_step_t ih₁ ih₂ =>
    cases h_step with
    | left h_step_f' =>
      judge app
      exact ih₁ h_step_f'
      repeat assumption
    | right h_step_x' =>
      have h₁ := ih₂ h_step_x'
      judge app
      assumption
      exact h₁
      
      sorry
