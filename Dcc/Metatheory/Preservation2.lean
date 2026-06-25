import Dcc.Judge2
import Dcc.Eta.Reduce

namespace GenericExpr

namespace RedEta?

def norm.{u} {τ : Type u} [DecidableEq τ] {A B : GenericExpr τ} (h : RedEta? A B) (hn : IsNorm RedAff A) : IsNorm RedAff B := by
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
