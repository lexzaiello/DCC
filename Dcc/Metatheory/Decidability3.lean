import Dcc.Judge3

namespace Expr

open Dsl in
def arr_is_norm (hn₁ : IsNorm Red A) (hn₂ : IsNorm Red B) : IsNorm Red (DCC (→ A B)) := fun _ h => by
  cases h
  case head h => nomatch h
  any_goals (
    focus
    try (
      expose_names
      nomatch hp)
    done)
  case congr_fun =>
    expose_names
    cases a
    case head h => nomatch h
    any_goals (
      focus
      try (
        expose_names
        cases hp)
      done)
    case point₂₁ =>
      expose_names
      cases hp
      cases a
      case head h => nomatch h
      any_goals (
        focus
        try (
          expose_names
          cases hp)
        done)
      case point₂₁ =>
        expose_names
        cases hp
        nomatch a
      case point₂₂ =>
        expose_names
        cases hp
        exact hn₁ a
    case point₂₂ =>
      expose_names
      cases hp
      cases a
      case head h => nomatch h
      any_goals (
        focus
        try (
          expose_names
          cases hp)
        done)
      case point₂₁ =>
        expose_names
        cases hp
        nomatch a
      case point₂₂ =>
        expose_names
        cases hp
        cases a
        case head h => nomatch h
        any_goals (
          focus
          try (
            expose_names
            cases hp)
          done)
        case point₂₁ =>
          expose_names
          cases hp
          exact hn₁ a
        case point₂₂ =>
          expose_names
          cases hp
          exact hn₂ a
  case congr_arg =>
    expose_names
    nomatch a

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
  · intro _ h
    cases h
    case head h => nomatch h
    any_goals (
      focus
      try (
        expose_names
        cases hp))
  any_goals (
    focus
    apply AndNorm.is_norm
    assumption)
  case fstc =>
    expose_names
    have ⟨hn₁, hn₂⟩ := a_1.is_norm a_ih
    exact arr_is_norm (mk_norm_congr (fun _ h => nomatch h) (mk_norm₂ (hp := .sigma) (mk_norm₂ (hp := .quot) mk_norm_top hn₁) (mk_norm₂ (hp := .quot) mk_norm_top a_2.is_norm)) mk_norm_tintro) (by sorry)
  case sndc =>
    sorry
  case id =>
    exact arr_is_norm (AndNorm.is_norm (by assumption)) (AndNorm.is_norm (by assumption))
  case unbox =>
    exact arr_is_norm (mk_norm₁ (AndNorm.is_norm (by assumption))) (AndNorm.is_norm (by assumption))
  case box => exact mk_norm₁ (by assumption)
  case sigma =>
    expose_names
    exact arr_is_norm a_4.is_norm.snd (fun _ h => nomatch h)
  case sort | top | bot | tintro | false | true | bool | bang =>
    intro _ h
    nomatch h

end Judge

end Expr
