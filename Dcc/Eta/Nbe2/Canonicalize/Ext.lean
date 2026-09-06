import Dcc.Eta.Nbe2.Canonicalize

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

def Canonicalize.max_hole_preserved
  {f   : GenericExpr τ_c}
  (lv  : ℕ)
  (hlt : f.max_hole < lv)
  (hc  : f.Canonicalize f') : f'.max_hole < lv := by
  induction hc
  case single hrb =>
    have h := hrb.max_hole_preserved
    grind
  any_goals (grind)

/-
Later show that well-typed expressions cannot contain holes then use that to eliminate lv.
-/
def Canonicalize.no_hole_preserved (heq : max_hole e = 0) (hc : Canonicalize e e') : max_hole e'= 0 := by
  have h := hc.max_hole_preserved 1 (by grind)
  grind

def Canonicalize.preservation_view
  {f     : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h   : Hole A lv x}
  {hlt   : f.max_hole < lv}
  (hn    : max_hole f = 0)
  (hrt   : f.ViewAppHole x lv hlt e_h.max_hole)
  (hc    : f.Canonicalize f') : f'.ViewAppHole x f.max_hole.succ (by have h := hc.no_hole_preserved hn; grind) (by have h := e_h.max_hole; grind) := by
  cases hc
  case single h_dom' e_h' hrt' hrb =>
    cases h_dom'.unique h_dom
    cases e_h'.unique e_h
    exact hrb.preservation_view
  case comp h_dom' e_h' hrt' hnrb h₁ h₂ =>
    cases h_dom'.unique h_dom
    cases e_h'.unique e_h
    cases hrt'.complete.symm.trans hrt.complete
    cases hrt
    case quot => exact (hnrb (.quot rfl)).elim
    case _ =>
      have h₁ := h₂.preservation_view (by grind) (by assumption)
      constructor
      

/-def Canonicalize.same_length
  (hr₁ : RedSpineNorm (DCC? (f x)) B)
  (hr₂ : RedSpineNorm (DCC? (g x)) B)
  (h_dom₁ : Domain f A)
  (h_dom₂ : Domain g A)
  (e_h    : Hole A lv x)
  (hlt₁   : f.max_hole < lv)
  (hlt₂   : g.max_hole < lv)
  (hrt₁   : f.ViewAppHole x lv hlt₁ e_h.max_hole)
  (hrt₂   : g.ViewAppHole x lv hlt₂ e_h.max_hole)
  (hc₁    : Canonicalize f f')
  (hc₂    : Canonicalize g g')
  (hrt₃   : g'.ViewAppHole x lv : -/

/-def Canonicalize.ext (hr₁ : RedSpineNorm (DCC? (f x)) B)
  (hr₂    : RedSpineNorm (DCC? (g x)) B)
  (h_dom₁ : Domain f A)
  (h_dom₂ : Domain g A)
  (e_h    : Hole A lv x)
  (hlt₁   : f.max_hole < lv)
  (hlt₂   : g.max_hole < lv)
  (hrt₁   : f.ViewAppHole x lv hlt₁ e_h.max_hole)
  (hrt₂   : g.ViewAppHole x lv hlt₂ e_h.max_hole)
  (hc₁    : Canonicalize f f')
  (hc₂    : Canonicalize g g') : f' = g' := by
  induction hc₁ generalizing g g' with
  | comp =>
    induction hc₂ generalizing f f' with
    | comp =>
      expose_names
      
      sorry-/

end GenericExpr

/-
Ext for canonicalize:

Compare parallel cases:

Λ(.., ..., ...) vs ... ∘ ...

Simple example:

Λ(..., ..., Snd) y hole vs Id(...) ∘ Id(...)

these would both have the same RedSpineNorm

What is true if there is no RedSpineNorm?

Really like the reduction length argument.

Canonicalization is uniquely determined by B and the domain

Some condition to force funext.

If B contains something OTHER than the hole.

Operations that aren't Readback introduce something from their points.

Λ(..., ..., Λ(..., ..., ...) f) y hole

vs

induction on the reduction length

because if we canonicalize with ReadbackHead length = 1, then they are the same
so show they have the same length
-/
