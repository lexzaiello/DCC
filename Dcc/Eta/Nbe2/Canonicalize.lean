import Dcc.Eta.Nbe2.Readback

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

/-
Readback can halt at composition (f ∘ g) x = f (g x), since (g x) might not be a head reduction.
Hence, we recurse down g. We stop when we hit something that is not a composition.
-/

inductive ReadbackFold : (f : GenericExpr τ_c)
  → (h_dom : Domain f A)
  → (e_h   : Hole A lv x)
  → (hlt   : f.max_hole < lv)
  → (hrt   : ViewAppHole f x lv hlt e_h.max_hole)
  → (f'    : GenericExpr τ_c) → Type u
  | single {f : GenericExpr τ_c}
    {h_dom : Domain f A}
    {e_h   : Hole A lv x}
    {hlt   : f.max_hole < lv}
    {hrt   : ViewAppHole f x lv hlt e_h.max_hole}
    {f'    : GenericExpr τ_c} :
    (hneq  : ∀ ⦃g h⦄, hrt.reduction.fst ≠ (DCC? (g (h x))))
    → (hrb   : Readback f h_dom e_h hlt hrt f')
    → ReadbackFold f h_dom e_h hlt hrt f'
  | comp  {f  : GenericExpr τ_c}
    {h_dom    : Domain f A}
    {e_h      : Hole A lv x}
    {hlt      : f.max_hole < lv}
    {hrt      : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq      : hrt.reduction.fst = (DCC? (g (h x))))
    → (hdg    : Domain h A)
    → (hlt₁   : max_hole h < lv)
    → (hrtg   : ViewAppHole h x lv hlt₁ e_h.max_hole)
    → (hrbg   : ReadbackFold h hdg e_h hlt₁ hrtg g')
    → (h_dom' : Domain (DCC? (g ∘ g')) A)
    → (hlt₂   : (DCC? (g ∘ g')).max_hole < lv)
    → (hrt'   : ViewAppHole (DCC? (g ∘ g')) x lv hlt₂ e_h.max_hole)
    → (hrb'   : Readback (DCC? (g ∘ g')) h_dom' e_h hlt₂ hrt' f')
    → ReadbackFold f h_dom e_h hlt hrt f'

def RedSpineNorm.cases_comp (h : RedSpineNorm A B) : (Σ g h x, RedSpineNorm A (DCC? (g (h x)))) ⊕ (PLift (∀ ⦃g h x⦄, B ≠ (DCC? (g (h x))))) := by
  cases B
  case app f x =>
    cases x
    case app =>
      exact .inl ⟨_, _, _, h⟩
    all_goals (exact .inr ⟨fun g h x heq => by cases heq⟩)
  all_goals (exact .inr ⟨fun g h x heq => by cases heq⟩)

def readback_fold {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackFold f h_dom e_h hlt hrt f') :=
  match hrt.reduction.snd.cases_comp with
  | .inl ⟨g, h, x', hrt'⟩ =>
    have heq' : hrt.reduction = ⟨DCC? (g (h x')), hrt'⟩ := by
      let hr₀ := hrt.reduction.snd
      have h := hrt'.eq ((hrt'.unique hr₀) ▸ hr₀)
      grind
    if heq : x' = x then
      have heq₁ : hrt.reduction.fst = (DCC? (g (h x))) := by grind
      if heq_dom : h.domain.fst = A then
        if hlt' : max_hole h < lv then
          match view_app_hole? h x lv hlt' e_h.max_hole with
          | .some hrt_h =>
            have h_dec : h.size < f.size := by
              have h_dec := hrt.reduction.snd.decreasing
              have h_size_zero := e_h.size_zero
              grind
            match readback_fold (heq_dom ▸ h.domain.snd) e_h hlt' hrt_h with
            | .some ⟨g', hrbf⟩ =>
              if heq_dom' : (DCC? (g ∘ g')).domain.fst = A then
                if hlt'' : (DCC? (g ∘ g')).max_hole < lv then
                  match view_app_hole? (DCC? (g ∘ g')) x lv hlt'' e_h.max_hole with
                  | .some hrt_h' =>
                    match hrt_h'.readback_head? (heq_dom' ▸ (DCC? (g ∘ g')).domain.snd) e_h hlt'' with
                    | .some ⟨_, hrb''⟩ =>
                      .some ⟨_, .comp heq₁ (heq_dom ▸ h.domain.snd) (by assumption) (by assumption) hrbf (heq_dom' ▸ (DCC? (g ∘ g')).domain.snd) (by assumption) (by assumption) hrb''⟩
                    | .none => .none
                  | .none => .none
                else .none
              else .none
            | .none => .none
          | .none => .none
        else .none
      else .none
    else
      have hn : ∀ ⦃g₁ h₁⦄, hrt.reduction.fst ≠ (DCC? (g₁ (h₁ x))) := by
        intro g₁ h₁ heq
        cases heq.symm.trans (Sigma.ext_iff.mp heq').left
        exact heq rfl
      match hrt.readback_head? h_dom e_h hlt with
      | .some ⟨_, hrb⟩ => .some ⟨_, .single hn hrb⟩
      | .none => .none
  | .inr ⟨hn⟩ =>
    match hrt.readback_head? h_dom e_h hlt with
    | .some ⟨_, hrb⟩ => .some ⟨_, .single (fun ⦃g₁⦄ ⦃h₁⦄ heq => hn heq) hrb⟩
    | .none => .none
termination_by f.size

end GenericExpr
