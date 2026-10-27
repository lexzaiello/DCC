import Dcc.Eta.Nbe2.Canonicalize

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

def Canonicalize.max_hole_preserved
  {f   : GenericExpr τ_c}
  (lv  : ℕ)
  (hlt : f.max_hole < lv)
  (hc  : f.Canonicalize lv hlt f') : f'.max_hole < lv := by
  induction hc
  case single hrb =>
    have h := hrb.max_hole_preserved
    grind
  any_goals (grind)

def ReadbackHead.preservation_reduct_hole
  {f     : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h   : Hole A lv x}
  {hlt   : f.max_hole < lv}
  {hrt   : ViewAppHole f x lv hlt e_h.max_hole}
  (hc    : ReadbackHead f h_dom e_h hlt hrt f') : hc.preservation_view.reduction.fst = hrt.reduction.fst := by
  cases hc with
  | id heq | fst heq | snd heq | quot heq =>
    simp [heq]
    simp [preservation_view]
    simp [ViewAppHole.reduction]

def Canonicalize.reduct_unique
  (hlt₁   : f.max_hole < lv)
  (hlt₂   : g.max_hole < lv)
  (hc₁    : Canonicalize (τ_c := τ_c) f lv hlt₁ f')
  (hc₂    : Canonicalize g lv hlt₂ g')
  (h_dom₁ : Domain f' A)
  (h_dom₂ : Domain g' A)
  (e_h    : Hole A lv x)
  (hlt₃   : f'.max_hole < lv)
  (hlt₄   : g'.max_hole < lv)
  (hn₁    : IsNorm RedAff f')
  (hn₂    : IsNorm RedAff g')
  (hrt₁   : RedSpineNorm (DCC? (f' x)) B)
  (hrt₂   : RedSpineNorm (DCC? (g' x)) B) : f' = g' := by
  /-have hrt'₁ := hc₁.hole_reduction
  have hrt'₂ := hc₂.hole_reduction-/
  induction hc₁ generalizing g g' with
  | single h_dom₁' e_h'₁ hrt''₁ hrb₁ =>
    induction hc₂ generalizing f f' with
    | single h_dom₂' e_h'₂ hrt''₂  hrb₂ =>
      have h_dom_a := hrb₁.preservation
      cases h_dom₁.unique h_dom_a
      have h_dom_b := hrb₂.preservation
      cases h_dom₂.unique h_dom_b
      cases e_h.unique e_h'₁
      cases e_h.unique e_h'₂
      cases e_h.eq e_h'₁
      cases e_h.eq e_h'₂
      exact ReadbackHead.ext hrt₁ hrt₂ hrb₁.preservation hrb₂.preservation e_h hrb₁.max_hole_preserved hrb₂.max_hole_preserved hrb₁.preservation_view hrb₂.preservation_view hrb₁.self hrb₂.self

/-def Canonicalize.preservation_reduct_hole
  {f     : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h   : Hole A f.max_hole.succ x}
  (hc    : Canonicalize f f')
  (hrt   : RedSpineNorm (DCC? (f x)) B) : RedSpineNorm (DCC? (f' x)) B := by
  cases hc
  case single h_dom' e_h' hrt' hrb =>
    cases h_dom'.unique h_dom
    cases e_h'.unique e_h
    have hrt₁ := hrb.preservation_view.reduction.snd
    have hrt₂ := hrt'.reduction.snd
    have heq := hrb.preservation_reduct_hole
    rw [← heq] at hrt₂
    cases hrt₂.unique hrt
    assumption
  case comp h_dom' e_h' hrt' hnrb h₁ h₂ =>
    cases hrt'
    case quot => exact (hnrb (.quot rfl)).elim
    case _ hrt'' hsp hgt hrtg =>
      cases h_dom.unique h_dom'
      cases e_h.unique e_h'
      cases hrt.unique hrt''
      match hrt''.head_rest.cases_head with
      | .inl ⟨h⟩ =>
        simp_all
        have hnorm := hrt''.is_norm
        cases h
        
        sorry
      | .inr h =>
        sorry-/

/-
To prove preservation_view, show that ¬ ViewAppHole implies there is no spine reduction on x.
-/

/-theorem no_hole_app_no_spine (h_dom : Domain f A) (e_h : Hole A lv x) (h : ViewAppHole (τ_c := τ_c) f x lv hlt (Hole.max_hole e_h) → False) : ∀ ⦃B⦄, RedSpineNorm (DCC? (f x)) B → False := by
  have hnorm := e_h.is_norm
  intro B hrt
  match heq : hrt.head with
  | ⟨e', ⟨hr⟩, hn⟩ =>
    cases hn
    case fstc =>
      cases (hrt.push_head (by constructor) (by constructor)).fst.elim_norm hnorm.sigl.to_head
      have hlt₁ := hrt.max_hole_preserved
      have hlt₂ := e_h.min_hole
      have hlt₃ := e_h.max_hole
      cases hlt₂
      exact h (.fst hrt (by grind) heq)
    case sndc =>
      cases (hrt.push_head (by constructor) (by constructor)).fst.elim_norm hnorm.sigr.to_head
      have hlt₁ := hrt.max_hole_preserved
      have hlt₂ := e_h.min_hole
      have hlt₃ := e_h.max_hole
      cases hlt₂
      exact h (.snd hrt (by grind) heq)
    case eval =>
      have hlt₁ := hrt.max_hole_preserved
      have hlt₂ := e_h.min_hole
      have hlt₃ := e_h.max_hole
      cases hlt₂
      expose_names
      if hnlt : B.max_hole < (_B.mkc y z).min_hole then
        exact h (.quot hrt hnlt)
      else
        exact h (.eval hrt (by grind) heq)
    case eql =>
      have hlt₁ := hrt.max_hole_preserved
      have hlt₂ := e_h.min_hole
      have hlt₃ := e_h.max_hole
      cases hlt₂
      expose_names
      cases hrt.unique ⟨.single .eql .eql, fun _ _ h => by cases h⟩
      exact h (.eql hrt (by grind) heq)
    case map =>
      have hlt₁ := hrt.max_hole_preserved
      have hlt₂ := e_h.min_hole
      have hlt₃ := e_h.max_hole
      cases hlt₂
      expose_names
      if hnlt : B.max_hole < y.box.min_hole then
        exact h (.quot hrt hnlt)
      else
        exact h (.map hrt (by grind) heq)
    case fmap =>
      have hlt₁ := hrt.max_hole_preserved
      have hlt₂ := e_h.min_hole
      have hlt₃ := e_h.max_hole
      cases hlt₂
      expose_names
      if hnlt : B.max_hole < y.box.min_hole then
        exact h (.quot hrt hnlt)
      else
        exact h (.fmap hrt (by grind) heq)
    case unmap =>
      have hlt₁ := hrt.max_hole_preserved
      have hlt₂ := e_h.min_hole
      have hlt₃ := e_h.max_hole
      cases hlt₂
      expose_names
      if hnlt : B.max_hole < y.box.min_hole then
        exact h (.quot hrt hnlt)
      else
        exact h (.unmap hrt (by grind) heq)
    case pair =>
      have hlt₁ := hrt.max_hole_preserved
      have hlt₂ := e_h.min_hole
      have hlt₃ := e_h.max_hole
      cases hlt₂
      expose_names
      cases (hrt.push_head (by constructor) (by constructor)).fst.elim_norm (fun _ _ h => by cases h)
      exact h (.pair hrt (by grind) heq)
    case curr' =>
      have hlt₁ := hrt.max_hole_preserved
      have hlt₂ := e_h.min_hole
      have hlt₃ := e_h.max_hole
      cases hlt₂
      expose_names
      match heq : x.view_app_hole? (DCC? &(⟦B_1⟧(y, z))) z.box.min_hole (by grind) (by grind) with
      | .some h =>
        sorry
      | .none =>
        /-have h := view_app_hole_none_sound heq
        have h_dom'  := Domain.curr'₁ (A := A_1) (B := B_1) (x := x) (y := y)
        have h_dom'' := Domain.curr' (A := A_1) (B := B_1) (x := x)
        cases h_dom.unique h_dom'
        have hn'' := no_hole_app_no_spine (f := x) x.domain.snd (x.domain.fst.mk_hole z.box.min_hole).snd (hlt := by grind)-/
        --have hn'' := no_hole_app_no_spine (by sorry) (by sorry) h (e_h := .bang (.coup (by sorry) (by sorry) (by sorry) (by sorry)))
        
        sorry
termination_by f.size-/

/-def Canonicalize.preservation_view
  {f     : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h   : Hole A lv x}
  {hlt   : f.max_hole < lv}
  (hrt   : f.ViewAppHole x lv hlt e_h.max_hole)
  (hc    : f.Canonicalize lv hlt f') : f'.ViewAppHole x lv (by have h := hc.max_hole_preserved; grind) (by have h := e_h.max_hole; grind) := by
  cases hc
  case single h_dom' e_h' hrt' hrb =>
    cases h_dom'.unique h_dom
    cases e_h'.unique e_h
    exact hrb.preservation_view
  case comp f g A x f' g' h_dom' e_h' hrt' hnrb h₁ h₂ =>
    cases h_dom'.unique h_dom
    cases e_h'.unique e_h
    cases hrt'.complete.symm.trans hrt.complete
    cases hrt
    case quot => exact (hnrb (.quot rfl)).elim
    case _ hrg =>
      expose_names
      have h_dec₁ := hrt.max_hole_preserved
      have hrt' := h₂.preservation_view (h_dom := h_dom'.elim_comp) hrg (e_h := e_h')
      have ⟨C, h⟩ := red_spineD ((f'.comp g').app x) .comp .comp
      have hlt₁ := h.max_hole_preserved
      have hlt₂ := h₁.max_hole_preserved lv (by grind)
      have hlt₃ := h₂.max_hole_preserved lv (by grind)
      expose_names
      
      exact .comp h (by sorry) (by sorry) (by sorry)-/

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

Suppose we have that

f -c> f' and g -c> g'

and that (f x) -β> B and (g x) -β> B
and (f' x) -β> B and (g' x) -β> B

Λ is only analagous to ∘ if it has a parapp y such that Λ(..., ..., ...) y arity = 1

All heads after canonicalization with the same hole are unique?

e_h : Hole A lv x

(f' x) -β> B
(g' x) -β> B

f' = g'

^ This is B unique determinism proof essentially



(f' x) -β> B should absolutely be provable

Problems:
- Domain preservation doesn't hold due to Λ not recursing enough
-/
