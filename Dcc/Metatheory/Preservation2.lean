import Dcc.Judge2
import Dcc.Eta.Reduce

namespace GenericExpr

def to_from_eta_expr_some (e : GenericExpr τ) : ((e' : GenericExpr τ) × (PLift (e.expr_to_eta.eta_to_expr = .some e'))) := by
  cases e
  any_goals (exact ⟨_, ⟨rfl⟩⟩)
  any_goals (
    rename_i x
    have ⟨_, ⟨h⟩⟩ := to_from_eta_expr_some x
    simp [expr_to_eta, Functor.map]
    dsimp [functor_map]
    simp [expr_to_eta, Functor.map] at h
    simp [eta_to_expr, h]
    exact ⟨_, ⟨rfl⟩⟩)
  any_goals (
    rename_i x y z
    have ⟨_, ⟨h₁⟩⟩ := to_from_eta_expr_some x
    have ⟨_, ⟨h₂⟩⟩ := to_from_eta_expr_some y
    have ⟨_, ⟨h₃⟩⟩ := to_from_eta_expr_some z
    simp [expr_to_eta, Functor.map]
    dsimp [functor_map]
    simp [expr_to_eta, Functor.map] at h₁
    simp [expr_to_eta, Functor.map] at h₂
    simp [expr_to_eta, Functor.map] at h₃
    simp [eta_to_expr, h₁, h₂, h₃]
    exact ⟨_, ⟨rfl⟩⟩)
  any_goals (
    rename_i x y
    have ⟨_, ⟨h₁⟩⟩ := to_from_eta_expr_some x
    have ⟨_, ⟨h₂⟩⟩ := to_from_eta_expr_some y
    simp [expr_to_eta, Functor.map]
    dsimp [functor_map]
    simp [expr_to_eta, Functor.map] at h₁
    simp [expr_to_eta, Functor.map] at h₂
    simp [eta_to_expr, h₁, h₂]
    exact ⟨_, ⟨rfl⟩⟩)

def to_from_eta_expr_comm (h : eta_to_expr (expr_to_eta e₁) = .some e₂) : e₁ = e₂ := by
  simp [expr_to_eta, Functor.map] at h
  induction e₁ generalizing e₂
  any_goals (
    focus
    dsimp [functor_map] at h
    simp [eta_to_expr] at h
    exact h)
  any_goals (
    focus
    try (
      rename_i ih
      dsimp [functor_map] at h
      simp [eta_to_expr] at h
      split at h
      case h_1 heq => cases h; cases ih heq; rfl
      · simp_all)
    done)
  any_goals (
    focus
    try (
      rename_i ih₁ ih₂ ih₃
      dsimp [functor_map] at h
      simp [eta_to_expr] at h
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
      dsimp [functor_map] at h
      simp [eta_to_expr] at h
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

def from_to_eta_expr_eq (h : eta_to_expr e = .some e') : expr_to_eta e' = e := by
  induction e generalizing e'
  any_goals (
    simp [eta_to_expr] at h
    rw [← h]
    dsimp [expr_to_eta, Functor.map, functor_map])
  any_goals (
    rename_i ih
    simp [eta_to_expr] at h
    split at h
    case h_1 heq =>
      have h₂ := ih heq
      rw [← h₂]
      simp at h
      rw [← h]
      simp [expr_to_eta, Functor.map]
      dsimp [functor_map]
    case h_2 => simp_all)
  case const x =>
    unfold eta_to_expr at h
    split at h
    any_goals (grind)
    case h_31 heq =>
      simp at h
      rw [← h]
      simp [heq]
      dsimp [expr_to_eta, Functor.map, functor_map]

def step_expr_steps_eta {e : GenericExpr (EtaConst (τ := τ))} {e' : GenericExpr τ}
  (heq : eta_to_expr e = .some e') (hr : RedAff e' e'') : ((e''' : GenericExpr (EtaConst (τ := τ))) × (PLift (RedAff e e'''))) :=
  ⟨e''.expr_to_eta, ⟨by
    induction hr generalizing e
    case pil hr ih =>
      rename_i f_α f_α' f_β
      have h_some : e.eta_to_expr.isSome := by simp_all
      have h_to_expr : (e.eta_to_expr.get h_some) = f_α.pi f_β := by
        simp_all
      unfold eta_to_expr at heq
      split at heq
      any_goals (grind)
      case h_15 e x y =>
        split at heq
        case h_1 heq₁ heq₂ =>
          cases heq
          have h := ih heq₁
          simp_all
          simp [expr_to_eta, Functor.map]
          dsimp [functor_map]
          change RedAff _ (.pi (expr_to_eta _) (expr_to_eta _))
          have heq₃ := from_to_eta_expr_eq heq₁
          simp [from_to_eta_expr_eq heq₂]
          have heq₄ :=  heq₃.symm ▸ heq₁
          simp [← heq₃]
          exact RedAff.pil (ih heq₄)
        · simp_all
    case pir hr ih =>
      rename_i f_β f_β' f_α
      unfold eta_to_expr at heq
      split at heq
      any_goals (grind)
      case h_15 e x y =>
        split at heq
        case h_1 heq₁ heq₂ =>
          cases heq
          have h := ih heq₂
          simp_all
          simp [expr_to_eta, Functor.map]
          dsimp [functor_map]
          change RedAff _ (.pi (expr_to_eta _) (expr_to_eta _))
          have heq₃ := from_to_eta_expr_eq heq₂
          simp [from_to_eta_expr_eq heq₁]
          have heq₄ :=  heq₃.symm ▸ heq₂
          simp [← heq₃]
          exact RedAff.pir (ih heq₄)
        · simp_all
    case eql =>
      
      sorry⟩⟩

def expr_to_eta_norm (h : IsNorm RedAff e) : IsNorm RedAff e.expr_to_eta := by
  unfold expr_to_eta
  split
  

def eta_to_expr_norm (h : eta_to_expr e = .some e') (hn : IsNorm RedAff e) : IsNorm RedAff e' := by
  intro ⟨_, h⟩
  induction h generalizing e
  case congrFun hr ih =>
    unfold eta_to_expr at h
    split at h
    any_goals (grind)
    case h_29 =>
      split at h
      case h_1 heq₁ heq₂ =>
        cases h
        exact ih heq₁ hn.congrFun
      · simp_all
  case congrArg hr ih =>
    unfold eta_to_expr at h
    split at h
    any_goals (grind)
    case h_29 =>
      split at h
      case h_1 heq₁ heq₂ =>
        cases h
        exact ih heq₂ hn.congrArg
      · simp_all
  case pil hr ih =>
    unfold eta_to_expr at h
    split at h
    any_goals (grind)
    split at h
    case h_1 heq₁ heq₂ =>
      cases h
      exact ih heq₁ hn.pil
    · simp_all
  case pir hr ih =>
    unfold eta_to_expr at h
    split at h
    any_goals (grind)
    split at h
    case h_1 heq₁ heq₂ =>
      cases h
      exact ih heq₂ hn.pir
    · simp_all
  case eql =>
    unfold eta_to_expr at h
    split at h
    any_goals (grind)
    split at h
    case h_1 heq₁ heq₂ =>
      cases h
      unfold eta_to_expr at *
      split at heq₁
      any_goals (grind)
      split at heq₂
      any_goals (grind)
      

/-def eta_to_expr_norm (h : eta_to_expr e = .some e') (hn : IsNorm RedAff e) : IsNorm RedAff e' := by
  unfold eta_to_expr at h
  split at h
  any_goals (
    focus
    simp at h
    cases h
    intro ⟨_, h⟩
    cases h
    done)
  case h_4 =>
    split at h
    case h_1 heq₁ heq₂ =>
      have ha := eta_to_expr_norm heq₁ (fun ⟨_, h⟩ => hn ⟨_, .eql' h⟩)
      have hb := eta_to_expr_norm heq₂ (fun ⟨_, h⟩ => hn ⟨_, .eqr' h⟩)
      cases h
      intro ⟨_, h⟩
      cases h with
      | eql' h => exact ha ⟨_, h⟩
      | eqr' h => exact hb ⟨_, h⟩
    · simp_all
  case h_29 =>
    
    sorry
  /-any_goals (
    focus
    try (
      rename_i ih
      simp at h
      split at h
      case h_1 heq =>
        cases h
        first
        | intro ⟨_, h⟩
          cases h
        | have h := ih heq (fun ⟨_, h⟩ => hn ⟨_, by constructor; exact h⟩)
          simp_all
      · simp_all)
    done)-/
  sorry-/

/-def eta_to_expr_norm (h : eta_to_expr e = .some e') (hn : IsNorm RedAff e) : IsNorm RedAff e' := by
  let h₀  := h
  let hn₀ := hn
  induction e generalizing e'
  any_goals (
    focus
    simp [eta_to_expr] at h
    cases h
    intro ⟨_, h⟩
    cases h
    done)
  any_goals (
    focus
    try (
      rename_i ih
      simp [eta_to_expr] at h
      split at h
      case h_1 heq =>
        cases h
        first
        | intro ⟨_, h⟩
          cases h
        | have h := ih heq (fun ⟨_, h⟩ => hn ⟨_, by constructor; exact h⟩)
          simp_all
      · simp_all)
    done)
  /-any_goals (
    focus
    try (
      rename_i ih₁ ih₂ ih₃
      simp [eta_to_expr] at h
      split at h
      case h_1 heq₁ heq₂ heq₃ =>
        have ha := ih₁ heq₁ (
      · simp_all)
    done)-/
  case bang ih =>
    simp [eta_to_expr] at h
    split at h
    case h_1 heq =>
      have hb := ih heq (fun ⟨_, h⟩ => hn ⟨_, .bang h⟩)
      cases h
      intro ⟨_, h⟩
      cases h with
      | bang h => exact hb ⟨_, h⟩
    · simp_all
  case pair ih₁ ih₂ ih₃ =>
    simp [eta_to_expr] at h
    split at h
    case h_1 heq₁ heq₂ heq₃ =>
      cases h
      have ha := ih₂ heq₂ (fun ⟨_, h⟩ => hn ⟨_, .pairl h⟩)
      have hb := ih₃ heq₃ (fun ⟨_, h⟩ => hn ⟨_, .pairr h⟩)
      intro ⟨_, h⟩
      cases h with
      | pairl h => exact ha ⟨_, h⟩
      | pairr h => exact hb ⟨_, h⟩
    · simp_all
  case mkc ih₁ ih₂ ih₃ =>
    simp [eta_to_expr] at h
    split at h
    case h_1 heq₁ heq₂ heq₃ =>
      cases h
      have ha := ih₂ heq₂ (fun ⟨_, h⟩ => hn ⟨_, .sigl h⟩)
      have hb := ih₃ heq₃ (fun ⟨_, h⟩ => hn ⟨_, .sigr h⟩)
      intro ⟨_, h⟩
      cases h with
      | sigl h => exact ha ⟨_, h⟩
      | sigr h => exact hb ⟨_, h⟩
    · simp_all
  case eq ih₁ ih₂ =>
    simp [eta_to_expr] at h
    split at h
    case h_1 heq₁ heq₂ =>
      have ha := ih₁ heq₁ (fun ⟨_, h⟩ => hn ⟨_, .eql' h⟩)
      have hb := ih₂ heq₂ (fun ⟨_, h⟩ => hn ⟨_, .eqr' h⟩)
      cases h
      intro ⟨_, h⟩
      cases h with
      | eql' h => exact ha ⟨_, h⟩
      | eqr' h => exact hb ⟨_, h⟩
    · simp_all
  case pi ih₁ ih₂ =>
    simp [eta_to_expr] at h
    split at h
    case h_1 hpi₁ hpi₂ =>
      have ha := ih₁ hpi₁ (fun ⟨_, h⟩ => hn ⟨_, .pil h⟩)
      have hb := ih₂ hpi₂ (fun ⟨_, h⟩ => hn ⟨_, .pir h⟩)
      cases h
      intro ⟨_, h⟩
      cases h with
      | pil h => exact ha ⟨_, h⟩
      | pir h => exact hb ⟨_, h⟩
    · simp_all
  case coup ih =>
    simp [eta_to_expr] at h
    split at h
    case h_1 heq =>
      have ha := ih heq (fun ⟨_, h⟩ => hn ⟨_, .coup h⟩)
      cases h
      intro ⟨_, h⟩
      cases h with
      | coup h => exact ha ⟨_, h⟩
    · simp_all
  case app ih₁ ih₂ =>
    simp [eta_to_expr] at h
    split at h
    case h_1 heq₁ heq₂ =>
      have ha := ih₁ heq₁ (fun ⟨_, h⟩ => hn ⟨_, .congrFun h⟩)
      have hb := ih₂ heq₂ (fun ⟨_, h⟩ => hn ⟨_, .congrArg h⟩)
      cases h
      simp_all
      
      sorry-/

/-def eta_to_expr_norm (h : eta_to_expr e = .some e') (hn : IsNorm RedAff e) : IsNorm RedAff e' := by
  induction e generalizing e'
  any_goals (
    focus
    simp [eta_to_expr] at h
    cases h
    intro ⟨_, h⟩
    cases h
    done)
  case map ih =>
    simp [eta_to_expr] at h
    split at h
    case h_1 heq =>
      
      sorry
    · simp_all

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
  -/

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
