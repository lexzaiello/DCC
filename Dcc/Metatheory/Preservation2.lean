import Dcc.Judge2
import Dcc.Eta.Reduce

namespace GenericExpr

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

namespace IsNorm

def elim_head_norm.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c] {A B : GenericExpr τ_c}
  (h : Reduces₂ A B) (hn : IsNorm RedAff A) : (red_eta A).fst = B :=
  match h with
  | ⟨hr₁, hn₁, hr₂⟩ => by
    cases hr₁.elim_head_norm hn
    simp [hr₂.complete]

end IsNorm

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

def unqiue.{u} {τ : Type u} [DecidableEq τ] {f_α₁ δ₁ f_α₂ δ₂ τ : GenericExpr τ}
  (h₁ : Pi.f_β.type f_α₁ δ₁ o₁ n₁ τ)
  (h₂ : Pi.f_β.type f_α₂ δ₂ o₂ n₂ τ) : f_α₁ = f_α₂ ∧ δ₁ = δ₂ ∧ o₁ = o₂ ∧ n₁ = n₂ := by
  cases h₁ <;> (cases h₂; grind)

/-def is_norm.{u} {τ : Type u} [DecidableEq τ] {f_α₁ δ₁ τ : GenericExpr τ} (h₁ : Pi.f_β.type f_α₁ δ₁ o₁ n₁ τ) : IsNorm RedAff τ := by
  cases h₁
  
  sorry-/

end Pi.f_β.type

namespace Judge₂

def invert_app.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c] {f x τ : GenericExpr τ_c} (ht : Judge₂ (DCC? (f x)) τ) :
  ((f_α f_β x_α α₂ : GenericExpr τ_c) × (PLift (Judge₂ f (DCC? (Π(f_α, f_β) x_α)))) × (PLift (Judge₂ x α₂)) × (PLift (DefEq (reduce_all₂ (DCC? (f_α x_α))) α₂)) × (PLift (Judge₂ (DCC? (f x)) (reduce_all₂ (DCC? (f_β #(reduce_all₂ x_α) x)))))) := by
  sorry

theorem invert_app (ht : Judge₂ e τ) (heq : e = (DCC? (f x))) : ∃ f_α f_β x_α α x_α',
  (Judge₂ f (DCC? (Π(f_α, f_β) x_α)) ∧ Reduces₂ (DCC? (f_α x_α)) α
    ∧ Judge x α ∧ Reduces env env' ∧ Reduces (DCC (f_β env' x)) τ) := by
  induction ht with
  | app h_t_f h_r_α h_t_x h_r_env h_r_τ =>
    cases heq
    exact ⟨_, _, _, _, _, h_t_f, h_r_α, h_t_x, h_r_env, h_r_τ⟩
  | _ => grind

def is_norm.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c] {e τ : GenericExpr τ_c} (h : Judge₂ e τ) : IsNorm RedAff τ := by
  cases h
  any_goals (
    focus
    intro ⟨_, h⟩; cases h; done)
  any_goals (exact Reduces₂.is_norm (by assumption))
  case box ht =>
    intro ⟨_, h⟩; cases h
    exact (ht.is_norm) ⟨_, by assumption⟩

end Judge₂

end GenericExpr

namespace Expr

namespace Judge2

open GenericExpr

theorem preservation {e : Expr} (ht : Judge₂ e τ) (hr : RedAff e e') : Judge₂ e' τ := by
  induction ht generalizing e' with
  | app h_t_f h_r_α h_t_x h_deq h_r_x_α h_r_τ ih₁ ih₂ =>
    cases hr with
    | eql =>
      cases h_t_f with
      | app h_t_f =>
        cases h_t_f with
        | eql _ _ h_r_τ_eql =>
          cases h_t_x with
          | box h_t_x =>
            simp [eql.type] at h_r_τ_eql
            -- δ should already be a normal form, since it's in an arrow that is part
            -- of a judge
            sorry
            /-simp [eql.type] at h_r_τ_eql
            have h := h_r_τ_eql.is_norm.congrArg
            have heq := h_r_τ_eql.complete
            simp [GenericExpr.reduce_all₂, GenericExpr.reduce', GenericExpr.reduce] at heq
            dcc_simp (! !) at heq
            split at heq
            case h_1 heq₁ =>
              split at heq₁
              · simp_all
              case h_2 h_r_δ heq₂ ih₂ =>
                simp_all
                
                rw [← heq₁.left] at heq
                
                sorry
            case h_2 =>
              sorry-/
    
  | eq h_t_x h_t_y ih₁ ih₂ =>
    cases hr with
    | eql' hr => exact .eq (ih₁ hr) h_t_y
    | eqr' hr => exact .eq h_t_x (ih₂ hr)
  | coup h_t_β hr_t_x hr_τ ih =>
    cases hr with
    | coup hr => exact .coup (ih hr) hr_t_x hr_τ
  | mk h_t_x h_t_β harr hr_t_x h_t_y h_r_τ ih₁ ih₂ ih₃ =>
    cases hr with
    | sigl hr => exact .mk (ih₁ hr) h_t_β harr (hr_t_x.push (.congrArg hr)) h_t_y h_r_τ
    | sigr hr => exact .mk h_t_x h_t_β harr hr_t_x (ih₃ hr) h_r_τ
  | pair h_t_f hr_β h_t_g h_r_γ₁ h_r_pi_snd hr_γ h_r_snd_arg_τ h_r_γ h_r_τ_fst h_r_τ ih₁ ih₂ =>
    cases hr with
    | pairl hr => apply Judge₂.pair (ih₁ hr) <;> assumption
    | pairr hr => apply Judge₂.pair (by assumption) (by assumption) (ih₂ hr) <;> assumption
  | pi h_t_f_α h_arr h_t_f_β h_r_f_α h_shape_f_β h_r_τ ih₁ ih₂ =>
    cases hr with
    | pil hr =>
      /-
        type of β, τ_f_β is a normal form, and this is the same as Pi.f_β.type,
        so f_α is a normal form
      -/
      have h_r_f_α' := h_r_f_α.push hr
      apply Judge₂.pi (ih₁ hr) <;> assumption
    | pir hr =>
      apply Judge₂.pi h_t_f_α h_arr (ih₂ hr) <;> assumption
  | bang ht ih =>
    cases hr with
    | bang hr =>
      exact .bang (ih hr)
  | refl | eql | id | sort | comp | comp₂ | comp' | fstc | sndc
  | sigma | curr | curr' | map | fmap | unmap | eval | quot | top | bot
  | tintro | box | unbox => cases hr
  /-case eq x α y h_t_x h_t_y ih₁ ih₂ =>
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
  case pi f_α τ_f_α δ m o f_β τ_f_β n τ -/

end Judge2

end Expr
