import Dcc.Ast
import Dcc.Types

@[simp] theorem K'.well_typed (h_t_α : ValidJudgment ⟪Sort m⟫ α)
  (h_t_β : ValidJudgment ⟪Sort n⟫ β)
  (h_t_x : ValidJudgment α x)
  (h_t_y : ValidJudgment β y) : ValidJudgment α ⟪K'.{[m, n]} α β x y⟫ := by
  judge [m, app, m, app, m, app, m, app, K']
  assumption
  step.M [k'₁]
  assumption
  step.M [k'₂]
  assumption
  step.M [k'₃]
  assumption
  step [K']

@[simp] theorem K.well_typed (h_t_α : ValidJudgment ⟪Sort m⟫ α)
  (h_t_β : ValidJudgment ⟪mk_arrow.{[m, n.succ]}(α, Sort n)⟫ β)
  (h_t_x : ValidJudgment α x)
  (h_t_y : ValidJudgment ⟪β x⟫ y) : ValidJudgment α ⟪K.{[m, n]} α β x y⟫ := by
  judge [m, app, m, app, m, app, m, app, K]
  assumption
  step.M [k₁]
  assumption
  step.M [k₂]
  assumption
  step.M [k₃]
  assumption
  step.M [k₄]

@[simp] theorem K.preservation  : ValidJudgment α x → ValidJudgment α x := id
@[simp] theorem K'.preservation : ValidJudgment α x → ValidJudgment α x := id

@[simp] theorem S.well_typed (h_t_α : ValidJudgment ⟪Sort m⟫ α)
  (h_t_β : ValidJudgment ⟪mk_arrow.{[m, n.succ]}(α, Sort n)⟫ β)
  (h_t_γ : ValidJudgment ⟪(Π.{[m, o.succ.succ]} α (M (Sγ.{[m, n, o]} α β)))⟫ γ)
  (h_t_f : ValidJudgment ⟪(Π.{[m, o]} α (M (Sf.{[m, n, o]} α β γ)))⟫ f)
  (h_t_g : ValidJudgment ⟪(Π.{[m, n]} α β)⟫ g)
  (h_t_x : ValidJudgment α x)
  : ValidJudgment ⟪γ x (g x)⟫ ⟪S.{[m, n, o]} α β γ f g x⟫ := by
  judge [m, app, m, app, m, app, m, app, m, app, m, app, S]
  assumption
  step.M [s₁]
  assumption
  step.M [s₂]
  assumption
  step.M [s₃]
  assumption
  step.M [s₄]
  assumption
  step.M [s₅]
  assumption
  step.M [s₆]

@[simp] theorem S.preservation (h_t_f : ValidJudgment ⟪(Π.{[m, o]} α (M (Sf.{[m, n, o]} α β γ)))⟫ f)
  (h_t_g : ValidJudgment ⟪(Π.{[m, n]} α β)⟫ g)
  (h_t_x : ValidJudgment α x) :
  ValidJudgment ⟪(γ x) (g x)⟫ ⟪f x (g x)⟫ := by
  judge [app, m, app]
  repeat assumption
  step.M [sf]
  judge [app]
  repeat assumption

theorem K.preservation' (h_t_k : ValidJudgment α ⟪K.{[m, n]} α β x y⟫) : ValidJudgment α x := by
  cases h_t_k with
  | app h_t_f =>
    cases h_t_f with
    | app h =>
      cases h with
      | app h =>
        cases h with
        | app h =>
          case app.app.app.app h _ =>
            cases h
            
