import Dcc.Eta.Nbe2.Canonicalize

namespace GenericExpr

def Canonicalize.reductions_same_length
  (h₁     : Canonicalize f f')
  (h₂     : Canonicalize g g')
  (h_dom₁ : Domain f A)
  (h_dom₂ : Domain g A)
  (e_h    : Hole A lv x)
  (hrt₁   : f.ViewAppHole x lv hlt₁ e_h.max_hole)
  (hrt₂   : g.ViewAppHole x lv hlt₂ e_h.max_hole) : hrt₁.reduction.length = hrt₂.reduction.length := by
  
  sorry

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
    cases hc₂ with
    | comp =>
      
      sorry-/

end GenericExpr
