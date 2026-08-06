import Dcc.Eta.Nbe.Canonicalize
import Dcc.Eta.Nbe.Normal

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace NormExpr

open GenericExpr

/-
eta-reduce all points, then canonicalize again
-/

inductive RedAll : (e : @GenericExpr τ_c) → (e' : @GenericExpr τ_c) → Type (u + 1)
  | pi₁ : (h_dom : Domain (τ_c := τ_c) ⟨f_α, hn_f_α⟩ ⟨δ, hn_δ⟩)
    → (hr₁ : RedAll f_α f_α')
    → (hr₂ : RedAll env env')
    → (hr₃ : RedAffNorm (DCC? (f_β env)) ⟨f_β_env, hn_f_β_env⟩)
    → (hr₄ : RedAll f_β_env f_β')
    → RedAll (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', `(δ, f_β')) env'))
  | pi₂ : (hn_dom : ∀ {δ}, Domain ⟨f_α, hn_f_α⟩ δ → PEmpty.{u + 1})
    → (hr₁ : RedAll f_α f_α')
    → (hr₂ : RedAll env env')
    → (hr₄ : RedAll f_β f_β')
    → RedAll (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', `(δ, f_β')) env'))
  | pi₃ : (hr₁ : RedAll (DCC? (f_α ∘' g)) f_α')
    → (hr₂ : RedAll (DCC? (f_β ∘' g)) f_β')
    → RedAll (DCC? Π(f_α, f_β) ∘' g) (DCC? (Π(f_α', f_β')))
  | tm  : (hn  : ViewEta f → False)
    → f.Canonicalize! f'
    → RedAll f f'

end NormExpr
