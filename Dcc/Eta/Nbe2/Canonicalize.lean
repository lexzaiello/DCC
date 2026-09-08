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
    {h_dom   : Domain f A}
    {e_h     : Hole A lv x}
    {hlt     : f.max_hole < lv}
    {hrt     : ViewAppHole f x lv hlt e_h.max_hole}
    {f'      : GenericExpr τ_c} :
    (hneq₁   : ∀ ⦃g h⦄, hrt.reduction.fst ≠ (DCC? (g (h x))))
    → (hneq₂ : ∀ ⦃g y⦄, hrt.reduction.fst ≠ (DCC? (g y x)))
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
  | congr {f  : GenericExpr τ_c}
    {h_dom    : Domain f A}
    {e_h      : Hole A lv x}
    {hlt      : f.max_hole < lv}
    {hrt      : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq      : hrt.reduction.fst = (DCC? (g y x)))
    → (hr     : RedSpineStar (DCC? (g y)) g₁)
    → (hn     : NormHead g₁)
    → (hdg    : Domain g₁ A)
    → (hlt₁   : max_hole g₁ < lv)
    → (hrtg   : ViewAppHole g₁ x lv hlt₁ e_h.max_hole)
    → (hrbg   : ReadbackFold g₁ hdg e_h hlt₁ hrtg g')
    → (h_dom' : Domain g' A)
    → (hlt₂   : g'.max_hole < lv)
    → (hrt'   : ViewAppHole g' x lv hlt₂ e_h.max_hole)
    → (hrb'   : Readback g' h_dom' e_h hlt₂ hrt' f')
    → ReadbackFold f h_dom e_h hlt hrt f'

def RedSpineNorm.cases_comp (x : GenericExpr τ_c) (h : RedSpineNorm A B) : (Σ g h, RedSpineNorm A (DCC? (g (h x)))) ⊕ (PLift (∀ ⦃g h⦄, B ≠ (DCC? (g (h x))))) := by
  cases B
  case app f x =>
    cases x
    case app a b =>
      if heq : b = x then
        subst heq
        exact .inl ⟨_, _, h⟩
      else
        (exact .inr ⟨fun g h heq => by cases heq; grind⟩)
    all_goals (exact .inr ⟨fun g h heq => by cases heq⟩)
  all_goals (exact .inr ⟨fun g h heq => by cases heq⟩)

def RedSpineNorm.cases_congr (x : GenericExpr τ_c) (h : RedSpineNorm A B) : (Σ g y, RedSpineNorm A (DCC? (g y x))) ⊕ (PLift (∀ ⦃g y⦄, B ≠ (DCC? (g y x)))) := by
  cases B
  case app f y =>
    cases f
    case app =>
      if heq : y = x then
        subst heq
        exact .inl ⟨_, _, h⟩
      else
        (exact .inr ⟨fun g h heq => by cases heq; grind⟩)
    all_goals (exact .inr ⟨fun g h heq => by cases heq⟩)
  all_goals (exact .inr ⟨fun g h heq => by cases heq⟩)

def readback_fold {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackFold f h_dom e_h hlt hrt f') :=
  match hrt.reduction.snd.cases_comp x,  hrt.reduction.snd.cases_congr x with
  | .inl ⟨g, h, hrt'⟩, _ =>
    have heq' : hrt.reduction = ⟨DCC? (g (h x)), hrt'⟩ := by
      let hr₀ := hrt.reduction.snd
      have h := hrt'.eq ((hrt'.unique hr₀) ▸ hr₀)
      grind
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
  | _, .inl ⟨g, y, hrt'⟩ =>
    have heq' : hrt.reduction = ⟨DCC? (g y x), hrt'⟩ := by
      let hr₀ := hrt.reduction.snd
      have h := hrt'.eq ((hrt'.unique hr₀) ▸ hr₀)
      grind
    have heq₁ : hrt.reduction.fst = (DCC? (g y x)) := by grind
    let g₁ := (red_spine_star (DCC? (g y))).fst
    if heq_dom : g₁.domain.fst = A then
      if hlt' : max_hole g₁ < lv then
        match view_app_hole? g₁ x lv hlt' e_h.max_hole with
        | .some hrt_h =>
          have h_dec : g₁.size < f.size := by
            have h_dec := hrt.reduction.snd.decreasing
            have h_size_zero := e_h.size_zero
            have h_dec₂ := (red_spine_star (DCC? (g y))).snd.fst.decreasing?
            grind
          match readback_fold (heq_dom ▸ g₁.domain.snd) e_h hlt' hrt_h with
          | .some ⟨g', hrbf⟩ =>
            if heq_dom' : g'.domain.fst = A then
              if hlt'' : g'.max_hole < lv then
                match view_app_hole? g' x lv hlt'' e_h.max_hole with
                | .some hrt_h' =>
                  match hrt_h'.readback_head? (heq_dom' ▸ g'.domain.snd) e_h hlt'' with
                  | .some ⟨_, hrb''⟩ =>
                    .some ⟨_, .congr heq₁ (red_spine_star (DCC? (g y))).snd.fst (red_spine_star (DCC? (g y))).snd.snd.down (heq_dom ▸ g₁.domain.snd) (by assumption) (by assumption) hrbf (heq_dom' ▸ g'.domain.snd) (by assumption) (by assumption) hrb''⟩
                  | .none => .none
                | .none => .none
              else .none
            else .none
          | .none => .none
        | .none => .none
      else .none
    else .none
  | .inr ⟨hn₁⟩, .inr ⟨hn₂⟩ =>
    match hrt.readback_head? h_dom e_h hlt with
    | .some ⟨_, hrb⟩ => .some ⟨_, .single (fun ⦃g₁⦄ ⦃h₁⦄ heq => hn₁ heq) (fun ⦃g₁⦄ ⦃h₁⦄ heq => hn₂ heq) hrb⟩
    | .none => .none
termination_by f.size

def try_readback (f : GenericExpr τ_c) : Option (GenericExpr τ_c) :=
  let h_dom : Domain f f.domain.fst := f.domain.snd
  let lv := f.max_hole.succ
  have hlt : f.max_hole < lv := by aesop
  let ⟨x, e_h⟩ := mk_hole f.domain.fst lv
  match view_app_hole? f x lv hlt e_h.max_hole with
  | .some h =>
    match readback_fold h_dom e_h hlt h with
    | .some ⟨f', _⟩ => .some f'
    | .none => .none
  | .none => .none

--#eval try_readback (DCC (Λ(Sort 1, Id(Sort 1), Fst(Id(Sort 1))) (Sort 0)))
#eval try_readback (DCC (Λ(Sort 1, `(Sort 1, Sort 1), Eval(Sort 1, `(Sort 1, Sort 1), `(Sort 1, `(Sort 1, ⊤)))) (Sort 0)))
-- ^ this is not reducing to `(Sort 1, `(Sort 1, ⊤)) due to left congruence. What is the left-congruence version of ∘? Idk.
-- ^ this left congruence can only be caused by combinators of arity 2, which are Curry
-- ^ actually, Eval is the only one that could introduce a left-congruence.

/-
Example:

Λ(Sort 1, Id(Sort 1), Fst(Id(Sort 1))) (Sort 0)
-/

end GenericExpr
