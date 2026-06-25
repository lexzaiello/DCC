import Dcc.Judge2
import Dcc.Eta.Reduce

namespace GenericExpr

def to_from_eta_expr_comm (h : eta_to_expr (expr_to_eta e₁) = .some e₂) : e₁ = e₂ := by
  induction e₁ generalizing e₂
  any_goals (
    focus
    simp [eta_to_expr, expr_to_eta] at h
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

def eta_to_expr_norm (h : eta_to_expr e = .some e') (hn : IsNorm RedAff e) : IsNorm RedAff e' := by
  induction e generalizing e'
  any_goals (
    focus
    simp [eta_to_expr] at h
    cases h
    intro ⟨_, h⟩
    cases h
    done)
  case map ih =>
    have h := ih (by sorry)
    sorry

def eta_to_expr_norm (h : eta_to_expr e = .some e') (hn : IsNorm RedAff e) : IsNorm RedAff e' := by
  unfold eta_to_expr at h
  split at h
  any_goals (
    focus
    cases h
    intro ⟨_, h⟩
    cases h
    done)
  case h_4 x y =>
    split at h
    case h_1 heq₁ heq₂ =>
      have ha := eta_to_expr_norm heq₁ (fun ⟨_, h⟩ => hn ⟨_, .eql' h⟩)
      have hb := eta_to_expr_norm heq₂ (fun ⟨_, h⟩ => hn ⟨_, .eqr' h⟩)
      cases h
      intro ⟨_, h⟩
      cases h with
      | eql' h => exact ha ⟨_, h⟩
      | eqr' h => exact hb ⟨_, h⟩
  case h_5 =>
    split at h
    case h_1 heq₁ =>
      cases h
      intro ⟨_, h⟩
      cases h
  

namespace TmEtaReduces

def norm.{u} {τ : Type u} [DecidableEq τ] {A B : GenericExpr (EtaConst (τ := τ))}
  (h : TmEtaReduces level A B) (hn : IsNorm RedAff A) : IsNorm RedAff B := by
  sorry

end TmEtaReduces

namespace FnEtaReduces

def norm.{u} {τ : Type u} [DecidableEq τ] {A B : GenericExpr (EtaConst (τ := τ))}
  (h : FnEtaReduces level A B) (hn : IsNorm RedAff A) : IsNorm RedAff B := by
  induction h with
  | pi hr₁ hr₂ ih₁ ih₂ =>
    have ha := ih₁ hn.pil
    have hb := ih₂ hn.pir
    intro ⟨_, h⟩
    cases h with
    | pil h => exact ha ⟨_, h⟩
    | pir h => exact hb ⟨_, h⟩
  | tm₁ hneq harity hr => exact hr.norm hn

end FnEtaReduces

namespace RedEta?

def norm.{u} {τ : Type u} [DecidableEq τ] {A B : GenericExpr τ} (h : RedEta? A B) (hn : IsNorm RedAff A) : IsNorm RedAff B := by
  induction h with
  | mk₁ hr heq =>
    have h := hr.norm hn
    
    sorry
  | mk₂ =>
    sorry

end RedEta?

namespace RedEta??

def norm.{u} {τ : Type u} [DecidableEq τ] {A B : GenericExpr τ} (h : RedEta?? A B) (hn : IsNorm RedAff A) : IsNorm RedAff B := by
  induction h with
  | pi₁ h_r_f_α h_domain h_δ_eq h_r_env h_r_f_env_β hn_f_β_env h_r_f_β hneq ih₁ ih₂ ih₃ =>
    have hn₁' := ih₁ hn.congrFun.pil
    have hn₂' := ih₂ hn.congrArg
    have hn₃' := ih₃ hn_f_β_env
    intro ⟨_, h⟩
    cases h with
    | congrFun h =>
      cases h with
      | pil h => exact hn₁' ⟨_, h⟩
      | pir h => cases h
    | congrArg h => exact hn₂' ⟨_, h⟩
  | pi₂ h_r_f_α h_r_f_β ih₁ ih₂ =>
    have hn₁' := ih₁ hn.pil
    have hn₂' := ih₂ hn.pir
    intro ⟨_, h⟩
    cases h with
    | pil h => exact hn₁' ⟨_, h⟩
    | pir h => exact hn₂' ⟨_, h⟩
  | pi₃ hrt₁ hn₁ h_r_f_α hrt₂ hn₂ h_r_f_β ih₁ ih₂ =>
    have hn₃ := ih₁ (fun ⟨_, h⟩ => by cases h)
    have hn₄ := ih₂ (fun ⟨_, h⟩ => by cases h)
    intro ⟨_, h⟩
    cases h with
    | pil h => exact hn₃ ⟨_, h⟩
    | pir h => exact hn₄ ⟨_, h⟩
  | coup hr_β ih =>
    have hn₂ := ih (fun ⟨_, h⟩ => by
      exact hn ⟨_, .coup h⟩)
    intro ⟨_, h⟩
    cases h with
    | coup h =>
      exact hn₂ ⟨_, h⟩
  | bang hr_β ih =>
    have hn := ih (fun ⟨_, h⟩ => by
      exact hn ⟨_, .bang h⟩)
    intro ⟨_, h⟩
    cases h with
    | bang h => exact hn ⟨_, h⟩
  | tm₁ hneq₁ hneq₂ hneq₃ hneq₄ hneq₅ hr => exact hr.norm hn
  | tm₂ => assumption
  | pi₁' h_r_f_α h_domain h_eq_δ h_r_env hrt₁ hn₁ h_r_f_β heq₂ ih₁ ih₂ ih₃ =>
    have ha := ih₁ hn.congrFun.pil
    have hb := ih₃ hn₁
    have hc := ih₂ (heq₂ ▸ hb).congrArg
    have hd := (heq₂ ▸ hb)
    intro ⟨_, h⟩
    cases h with
    | congrFun h =>
      cases h with
      | pil h => exact ha ⟨_, h⟩
      | pir h => exact hd.congrFun ⟨_, h⟩
    | congrArg h => exact hc ⟨_, h⟩

end RedEta??

namespace RedEta₂

def norm.{u} {τ : Type u} [DecidableEq τ] {A B : GenericExpr τ} (h : RedEta₂ A B) (hn : IsNorm RedAff A) : IsNorm RedAff B :=
  match h with
  | .refl _hn => hn
  | .step hrη => by
    induction hrη
    
    sorry

end RedEta₂

--theorem RedEta₂.

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

namespace Pi.f_β.type

namespace Judge2

theorem norm_aff.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {e τ : GenericExpr τ_c} (h : Judge₂ e τ) : IsNorm RedAff τ := by
  induction h
  any_goals (focus
    intro ⟨_, h⟩
    cases h
    done)
  · have h := Reduces₂.

theorem preservation {e : GenericExpr τ_c} [DecidableEq τ_c] (ht : Judge₂ e τ) (hr : RedAff e e') : Judge₂ e' τ := by
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

end GenericExpr
