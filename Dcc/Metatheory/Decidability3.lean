import Dcc.Judge3

namespace Expr

def comp_is_norm (hn₁ : IsNorm Red x) (hn₂ : IsNorm Red y) : IsNorm Red (DCC (∘ x y)) := fun ⟨_, h⟩ =>
  match h with
  | .point 0 hn h => hn₁ ⟨_, h⟩
  | .point 1 hn h => hn₂ ⟨_, h⟩

open Dsl in
def pi_is_norm (hn₁ : IsNorm Red B) (hn₂ : IsNorm Red C) (hn₃ : IsNorm Red x) : IsNorm Red (DCC ((Π B C) x)) := fun ⟨_, h⟩ =>
  match h with
  | .congrFun (.point 0 hn h) => hn₁ ⟨_, h⟩
  | .congrFun (.point 1 hn h) => hn₂ ⟨_, h⟩
  | .congrArg h => hn₃ ⟨_, h⟩

open Dsl in
def quot_is_norm (hn₁ : IsNorm Red B) (hn₂ : IsNorm Red x) : IsNorm Red (DCC (`B x)) := fun ⟨_, h⟩ =>
  match h with
  | .point 0 hn h => hn₁ ⟨_, h⟩
  | .point 1 hn h => hn₂ ⟨_, h⟩

open Dsl in
def sigma_is_norm (hn₁ : IsNorm Red B) (hn₂ : IsNorm Red C) (hn₃ : IsNorm Red x) : IsNorm Red (DCC ((Σ B C) x)) := fun ⟨_, h⟩ =>
  match h with
  | .congrFun (.point 0 hn h) => hn₁ ⟨_, h⟩
  | .congrFun (.point 1 hn h) => hn₂ ⟨_, h⟩
  | .congrArg h => hn₃ ⟨_, h⟩

open Dsl in
def arr_is_norm (hn₁ : IsNorm Red A) (hn₂ : IsNorm Red B) : IsNorm Red (DCC (→ A B)) := fun ⟨_, h⟩ =>
  match h with
  | .congrFun (.point n hlt h) => by
    simp [point_arity] at hlt
    match n with
    | 0 =>
      simp [points, Vector.get] at h
      match h with
      | .point 0 hn h =>
        nomatch h
      | .point 1 hn h => exact hn₁ ⟨_, h⟩
    | 1 =>
      simp [points, Vector.get] at h
      match h with
      | .point 0 hn h =>
        simp [points, Vector.get] at h
        nomatch h
      | .point 1 hn h =>
        simp [points, Vector.get] at h
        match h with
        | .point 0 hn h => exact hn₁ ⟨_, h⟩
        | .point 1 hn h => exact hn₂ ⟨_, h⟩
  | .congrArg h => nomatch h

namespace Judge

set_option maxHeartbeats 20000000000 in
def complete (h : Judge e τ) : e.infer = .ok ⟨τ, h⟩ := by
  induction h <;> (dsimp [infer]; try (dcc_aesop' [reduce]))

def unique (h₁ : Judge e τ₁) (h₂ : Judge e τ₂) : τ₁ = τ₂ := by
  have heq₁ := h₁.complete
  have heq₂ := h₂.complete
  grind

def is_norm {e τ : Expr} (h : Judge e τ) : IsNorm Red τ := by
  induction h
  any_goals (
    focus
    try (
      intro ⟨_, h⟩
      cases h
      grind)
    done)
  any_goals (
    focus
    apply RedNorm.is_norm
    assumption)
  case id =>
    exact arr_is_norm (RedNorm.is_norm (by assumption)) (RedNorm.is_norm (by assumption))
  case unbox =>
    apply arr_is_norm
    · intro ⟨_, h⟩
      match h with
      | .point 0 hn h => exact RedNorm.is_norm (by assumption) ⟨_, h⟩
    · exact RedNorm.is_norm (by assumption)
  case box => exact (fun ⟨_, .point 0 hn h⟩ => by dcc_aesop' [force_reduce])
  case sigma =>
    expose_names
    have ⟨hn₁, hn₂⟩ := a_1.is_norm (by assumption)
    exact arr_is_norm hn₁ (fun ⟨_, h⟩ => nomatch h)
  case comp =>
    expose_names
    exact pi_is_norm
      (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (Arrow.is_norm a_1 a_ih).1)
      (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (comp_is_norm (fun ⟨_, h⟩ => a_ih_1 ⟨_, .congrFun (.point 1 (by grind) (.point 1 (by point_arity) h))⟩) a_3.is_norm))
      (fun ⟨_, h⟩ => nomatch h)
  case fstc =>
    expose_names
    have ⟨hn₁, hn₂⟩ := a_1.is_norm (by assumption)
    have hn₃ := a_2.is_norm
    exact arr_is_norm (sigma_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (by assumption)) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (by assumption)) (fun ⟨_, h⟩ => nomatch h)) (by assumption)
  case sndc =>
    expose_names
    have ⟨hn₁, hn₂⟩ := a_1.is_norm (by assumption)
    have hn₃ := a_2.is_norm
    exact pi_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (sigma_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (by assumption)) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (by assumption)) (fun ⟨_, h⟩ => nomatch h))) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (comp_is_norm (by assumption) (fun ⟨_, .point 0 hn h⟩ => hn₃ ⟨_, h⟩))) (fun ⟨_, h⟩ => nomatch h)

end Judge

end Expr
