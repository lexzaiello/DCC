import Dcc.Judge2
import Dcc.Aff.Red
import Dcc.Eta.Reduce

namespace GenericExpr

def expr_to_eta_holds_red (hr : RedAff e e') : RedAff e.expr_to_eta e'.expr_to_eta := by
  induction hr
  any_goals (
    rename_i ih
    simp [expr_to_eta]
    constructor
    try assumption)

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

/-
5. Turn "should already be a normal form" into a lemma. Your comment — δ is normal because it's in an arrow inside a judge — is a real invariant, so prove it: Arrow δ s o τ → Normal δ (or whatever the true statement is). Then hred : Reduces₂ δ δ' collapses via Normal.reduces_eq to δ' = δ and you subst. Right now you're re-deriving that fact inline every time it comes up; do it once.

prove these invariants.
-/

end Pi.f_β.type

namespace Judge₂

theorem invert_app.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c]
  {f x τ : GenericExpr τ_c} (ht : Judge₂ (DCC? (f x)) τ) :
  (∃ (f_α f_β x_α α₂ : GenericExpr τ_c), (Judge₂ f (DCC? (Π(f_α, f_β) x_α))) ∧ (Judge₂ x α₂)
  ∧ (DefEq (reduce_all₂ (DCC? (f_α x_α))) α₂) ∧ (Reduces₂ (DCC? (f_β #(reduce_all₂ x_α) x)) τ)) :=
  match ht with
  | .app (f_α := f_α) (f_β := f_β) (x_α := x_α) (α₂ := α₂) h_t_f hr₁ h_t_x h_deq hr₂ hr₃ =>
    ⟨f_α, f_β, x_α, α₂, h_t_f, h_t_x, hr₁.complete ▸ h_deq, hr₂.complete ▸ hr₃⟩

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
  | pair h_t_f hr_β h_t_g h_r_γ₁ h_r_pi_snd hr_γ h_r_snd_arg_τ h_r_γ h_r_τ_fst ih₁ ih₂ =>
     cases hr with
     | pairl hr => apply Judge₂.pair (ih₁ hr) <;> assumption
     | pairr hr => apply Judge₂.pair (by assumption) (by assumption) (ih₂ hr) <;> assumption
  | pi h_t_f_α h_arr h_t_f_β h_r_f_α h_shape_f_β h_r_τ ih₁ ih₂ =>
     cases hr with
     | pil hr =>
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

end Judge2

end Expr
