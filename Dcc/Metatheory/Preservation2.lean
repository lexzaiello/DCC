import Dcc.Judge2
import Dcc.Eta.Reduce

namespace GenericExpr

def to_from_eta_expr_some (e : GenericExpr τ) : ((e' : GenericExpr τ) × (PLift (e.expr_to_eta.eta_to_expr = .some e'))) := by
  cases e
  any_goals (exact ⟨_, ⟨rfl⟩⟩)
  any_goals (
    rename_i x
    have ⟨_, ⟨h⟩⟩ := to_from_eta_expr_some x
    simp [expr_to_eta, eta_to_expr, h]
    exact ⟨_, ⟨rfl⟩⟩
  )
  any_goals (
    rename_i x y z
    have ⟨_, ⟨h₁⟩⟩ := to_from_eta_expr_some x
    have ⟨_, ⟨h₂⟩⟩ := to_from_eta_expr_some y
    have ⟨_, ⟨h₃⟩⟩ := to_from_eta_expr_some z
    simp [expr_to_eta, eta_to_expr] at *
    simp [h₁, h₂, h₃]
    exact ⟨_, ⟨rfl⟩⟩)
  any_goals (
    rename_i x y
    have ⟨_, ⟨h₁⟩⟩ := to_from_eta_expr_some x
    have ⟨_, ⟨h₂⟩⟩ := to_from_eta_expr_some y
    simp [expr_to_eta, eta_to_expr] at *
    simp [h₁, h₂]
    exact ⟨_, ⟨rfl⟩⟩)

def to_from_eta_expr_comm (h : eta_to_expr (expr_to_eta e₁) = .some e₂) : e₁ = e₂ := by
  induction e₁ generalizing e₂
  any_goals (
    focus
    simp [expr_to_eta, eta_to_expr] at h
    exact h)
  any_goals (
    focus
    try (
      rename_i ih
      simp [expr_to_eta, eta_to_expr] at h
      split at h
      case h_1 heq => cases h; cases ih heq; rfl
      · simp_all)
    done)
  any_goals (
    focus
    try (
      rename_i ih₁ ih₂ ih₃
      simp [expr_to_eta, eta_to_expr] at h
      split at h
      case h_1 heq₁ heq₂ heq₃ =>
        have ha := ih₁ heq₁
        have hb := ih₂ heq₂
        have hc := ih₃ heq₃
        simp_all
      · simp_all)
    done)
  any_goals (
    focus
    try (
      rename_i ih₁ ih₂
      simp [expr_to_eta, eta_to_expr] at h
      split at h
      case h_1 heq₁ heq₂ =>
        have ha := ih₁ heq₁
        have hb := ih₂ heq₂
        simp_all
      · simp_all))

def to_from_eta_expr_eq : (expr_to_eta e).eta_to_expr = e := by
  have ⟨_, ⟨heq⟩⟩ := to_from_eta_expr_some e
  have h' := to_from_eta_expr_comm heq
  simp_all

def expr_to_eta_holds_red (hr : RedAff e e') : RedAff e.expr_to_eta e'.expr_to_eta := by
  induction hr
  any_goals (
    rename_i ih
    simp [expr_to_eta]
    constructor
    try assumption)

namespace RedAffReflTrans

theorem elim_head_norm (h : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B :=
  hn.unique_refl h

end RedAffReflTrans

namespace Reduces₂

/-
If there is some intermediate step A → B in a reduction

A =-=> C

then B =-=> C

This is useful for preservation, since you can do congruence as such.
-/
def push.{u} {τ : Type u} [DecidableEq τ] [BEq τ] {A B C : GenericExpr τ}
  (h₁ : Reduces₂ A C) (h₂ : RedAff A B) : Reduces₂ B C :=
  match h₁ with
  | ⟨hr₁, hn₁, hr₂⟩ =>
    have ⟨_D, h₁, h₂⟩  := hr₁.conf (.single h₂)
    have heq := h₁.elim_head_norm hn₁
    ⟨heq.symm ▸ h₂, hn₁, hr₂⟩

end Reduces₂

end GenericExpr

namespace Expr

namespace Judge2

open GenericExpr

theorem preservation {e : Expr} (ht : Judge₂ e τ) (hr : RedAff e e') : Judge₂ e' τ := by
  induction ht generalizing e'
  any_goals (
    focus
    cases hr
    done)
  case eq x α y h_t_x h_t_y ih₁ ih₂ =>
    cases hr with
    | eql' hr => exact .eq (ih₁ hr) h_t_y
    | eqr' hr => exact .eq h_t_x (ih₂ hr)
  case coup f_β α n τ h_t_β hr_t_x hr_τ ih =>
    cases hr with
    | coup hr => exact .coup (ih hr) hr_t_x hr_τ
  case mk h_t_x h_t_β harr hr_t_x h_t_y h_r_τ ih₁ ih₂ ih₃ =>
    cases hr with
    | sigl hr => exact .mk (ih₁ hr) h_t_β harr (hr_t_x.push (.congrArg hr)) h_t_y h_r_τ
    | sigr hr => exact .mk h_t_x h_t_β harr hr_t_x (ih₃ hr) h_r_τ
  case pair h_t_f hr_β h_t_g h_r_γ₁ h_r_pi_snd hr_γ h_r_snd_arg_τ h_r_γ h_r_τ_fst h_r_τ ih₁ ih₂ =>
    cases hr with
    | pairl hr => apply Judge₂.pair (ih₁ hr) <;> assumption
    | pairr hr => apply Judge₂.pair (by assumption) (by assumption) (ih₂ hr) <;> assumption
  case pi h_t_f_α h_arr h_t_f_β h_t_f_β_shape h_r_τ ih₁ ih₂ =>
    cases hr with
    | pil hr =>
      apply Judge₂.pi (ih₁ hr)
      any_goals (assumption)
      
      sorry
    | pir hr =>
      sorry

end Judge2

end Expr
