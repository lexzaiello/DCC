import Dcc.Ast

def mk_arrow (α β : Expr) (m n : Level) : Expr :=
  ⟪Kβ.{[m, n]} α β⟫

inductive IsDom : Expr → Expr → Prop
  /-
    Nondependent K type:
  -/
  | kβ₁ : IsDom ⟪M Kβ.{[m, n]}⟫ ⟪Sort m⟫
  | kβ₂ : IsDom ⟪M (Kβ.{[m, n]} α)⟫ ⟪Sort n⟫
  | kβ₃ : IsDom ⟪M (Kβ.{[m, n]} α β)⟫ α
  | k'₁ : IsDom ⟪M K'.{[m, n]}⟫ ⟪Sort m⟫
  | k'₂ : IsDom ⟪M (K'.{[m, n]} α)⟫ ⟪Sort n⟫
  | k'₃ : IsDom ⟪M (K'.{[m, n]} α β)⟫ α
  | k'₄ : IsDom ⟪M (K'.{[m, n]} α β x)⟫ β
  /-
    Dependnet K type:
  -/
  | k₁  : IsDom ⟪M K.{[m, n]}⟫ ⟪Sort m⟫
  | k₂  : IsDom ⟪M (K.{[m, n]} α)⟫ ⟪M (Kβ.{[m, n.succ]} α (Sort n))⟫
  | k₃  : IsDom ⟪M (K.{[m, n]} α β)⟫ α
  | k₄  : IsDom ⟪M (K.{[m, n]} α β x)⟫ ⟪β x⟫
  /-
    S type:
  -/
  | s₁  : IsDom ⟪M (S.{[m, n, o]})⟫ ⟪Sort m⟫
  | s₂  : IsDom ⟪M (S.{[m, n, o]})⟫ ⟪M (Kβ.{[m, n.succ]} α (Sort n))⟫
  | s₃  : IsDom ⟪M (S.{[m, n, o]} α β)⟫ ⟪M (Sγ.{[m, n, o]} α β)⟫
  | s₄  : IsDom ⟪M (S.{[m, n, o]} α β γ)⟫ ⟪M (Sf.{[m, n, o]} α β γ)⟫
  | s₅  : IsDom ⟪M (S.{[m, n, o]} α β γ x)⟫ ⟪M (Sg.{[m, n]} α β)⟫
  | s₆  : IsDom ⟪M (S.{[m, n, o]} α β γ x y)⟫ α
  /-
    γ and f arguments to S both have the same domains
  -/
  | sγ₁ : IsDom ⟪M (Sγ.{[m, n, o]})⟫ ⟪Sort m⟫
  | sγ₂ : IsDom ⟪M (Sγ.{[m, n, o]} α)⟫ ⟪M (Kβ.{[m, n.succ]} α (Sort n))⟫
  | sγ₃ : IsDom ⟪M (Sγ.{[m, n, o]} α β x)⟫ ⟪β x⟫
  | sf₁ : IsDom ⟪M (Sf.{[m, n, o]})⟫ ⟪Sort m⟫
  | sf₂ : IsDom ⟪M (Sf.{[m, n, o]} α)⟫ ⟪M (Kβ.{[m, n.succ]} α (Sort n))⟫
  | sf₃ : IsDom ⟪M (Sf.{[m, n, o]} α β)⟫ ⟪M Sγ.{[m, n, o]}⟫
  | sf₄ : IsDom ⟪M (Sf.{[m, n, o]} α β γ)⟫ α
  | sf₅ : IsDom ⟪M (Sf.{[m, n, o]} α β γ x)⟫ ⟪β x⟫
  | sg₁ : IsDom ⟪M (Sg.{[m, n]} α β)⟫ α
  | sg₂ : IsDom ⟪M (Sg.{[m, n]} α β x)⟫ ⟪β x⟫

/-
For substitution later.
-/
def IsCod : Expr → Expr → Prop
  | ⟪M (Kβ.{[_m, _n]} _α β)⟫, β' => β = β'
  | ⟪M (K'.{[_m, _n]} α _β _x _y)⟫, α'
  | ⟪M (K.{[_m, _n]} α _β _x _y)⟫, α' => α = α'
  | ⟪M (S.{[_m, _n, _o]} _α _β γ _x y z)⟫, α' => ⟪γ z (y z)⟫ = α'
  | ⟪M (Sγ.{[_m, _n, o]} _α _β _x)⟫, α' => ⟪Sort o⟫ = α'
  | ⟪M (Sf.{[_m, _n, _o]} _α _β γ x y)⟫, α' => ⟪γ x y⟫ = α'
  | ⟪M (Sg.{[_m, _n]} _α β x)⟫, α' => ⟪β x⟫ = α'
  | ⟪M e⟫, α' => e = α'
  | _, _ => false

inductive IsStep : Expr → Expr → Prop
  | left    : IsStep f f'  → IsStep ⟪f x⟫ ⟪f' x⟫
  | right   : IsStep x x'  → IsStep ⟪f x⟫ ⟪f x'⟫
  | K       : IsStep ⟪K.{[m, n]} α β x y⟫ x
  | K'      : IsStep ⟪K'.{[m, n]} α β x y⟫ x
  | S       : IsStep ⟪S.{[m, n, o]} α β γ x y z⟫ ⟪(x z) (y z)⟫
  | pi      : IsStep ⟪Π.{[m, n]} α β x⟫ ⟪β x⟫

inductive ValidJudgment : Expr → Expr → Prop
  | Sort : ValidJudgment ⟪Sort m.succ⟫ ⟪Sort m⟫
  | S    : ValidJudgment ⟪M S.{[m, n, o]}⟫ ⟪S.{[m, n, o]}⟫
  | K    : ValidJudgment ⟪M K.{[m, n]}⟫ ⟪K.{[m, n]}⟫
  | K'   : ValidJudgment ⟪M K'.{[m, n]}⟫ ⟪K'.{[m, n]}⟫
  | app  : ValidJudgment Tf f
    → IsDom α Tf
    → ValidJudgment α x
    → IsCod ⟪Tf x⟫ β
    → ValidJudgment β ⟪f x⟫

theorem K'.preservation (h_t : ValidJudgment α ⟪K'.{[m, n]} α β x y⟫) : ValidJudgment α x := by
  cases h_t with
  | app h_t_f _ h_cod =>
  cases h_t_f with
  | app h_t_f _ h_cod =>
  cases h_t_f with
  | app h_t_f _ h_cod =>
  cases h_t_f with
  | app h_t_f _ h_cod =>
  cases h_t_f
  case app.app.app.app.K' h_cod_y _ _ _ _ _ _ _ _ _ _ _ _ _  =>
    cases h_cod_y

theorem K.preservation (h_t : ValidJudgment α ⟪K.{[m, n]} α β x y⟫) : ValidJudgment α x := by
  cases h_t with
  | app h_t_f _ h_cod =>
  cases h_t_f with
  | app h_t_f _ h_cod =>
  cases h_t_f with
  | app h_t_f _ h_cod =>
  cases h_t_f with
  | app h_t_f _ h_cod =>
  cases h_t_f
  case app.app.app.app.K h_cod_y _ _ _ _ _ _ _ _ _ _ _ _ _  =>
    cases h_cod_y

theorem S.preservation (h_t : ValidJudgment ⟪γ z (y z)⟫ ⟪S.{[m, n, o]} α β γ x y z⟫) : ValidJudgment ⟪γ z (y z)⟫ ⟪x z (y z)⟫ := by
  cases h_t with
  | app h_t_f _ h_cod =>
  cases h_t_f with
  | app h_t_f _ h_cod =>
  cases h_t_f with
  | app h_t_f _ h_cod =>
  cases h_t_f with
  | app h_t_f _ h_cod =>
  cases h_t_f with
  | app h_t_f _ h_cod =>
  cases h_t_f with
  | app h_t_f _ h_cod =>
  cases h_t_f
  case app.app.app.app.app _ _ _ _  h_cod_t' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ __ _ _ _ _ _ _  =>
    cases h_cod_t'

