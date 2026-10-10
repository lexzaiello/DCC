import Dcc.Judge3

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

open Dsl in
def arr_is_norm (hn₁ : IsNorm RedAff A) (hn₂ : IsNorm RedAff B) (m : Level) : IsNorm RedAff (DCC? (→ (: A (Sort m)) B)) := fun ⟨_, h⟩ =>
  match h with
  | .congrFun (.point n hlt h) => by
    simp [point_arity] at hlt
    match n with
    | 0 =>
      simp [points, Vector.get] at h
      match h with
      | .point 0 hn h =>
        nomatch h
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
  | .congrArg h => hn₁ ⟨_, h⟩

namespace Judge

set_option maxHeartbeats 20000000000 in
def complete (h : Judge (τ_c := τ_c) e τ) : e.infer = .ok ⟨τ, h⟩ := by
  induction h <;> (dsimp [infer]; try (dcc_aesop' [reduce]))

def unique (h₁ : Judge (τ_c := τ_c) e τ₁) (h₂ : Judge e τ₂) : τ₁ = τ₂ := by
  have heq₁ := h₁.complete
  have heq₂ := h₂.complete
  grind

def is_norm {e τ : GenericExpr τ_c} (h : Judge e τ) : IsNorm RedAff τ := by
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
    apply Reduces.is_norm
    assumption)
  case id =>
    exact arr_is_norm (Reduces.is_norm (by assumption)) (Reduces.is_norm (by assumption)) _
  case unbox =>
    exact arr_is_norm (fun ⟨_, .point 0 hn h⟩ => (Reduces.is_norm (by assumption)) ⟨_, h⟩) (Reduces.is_norm (by assumption)) _
  case box => exact (fun ⟨_, .point 0 hn h⟩ => by dcc_aesop' [force_reduce])

end Judge

end GenericExpr
