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
    (hneq₁ : ∀ ⦃g y⦄, hrt.reduction.fst ≠ (DCC? (g y x)))
    → (hrb   : Readback f h_dom e_h hlt hrt f')
    → ReadbackFold f h_dom e_h hlt hrt f'
  /-| comp  {f  : GenericExpr τ_c}
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
    → ReadbackFold f h_dom e_h hlt hrt f'-/
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

def assert_domain (f τ : GenericExpr τ_c) : Option (Domain f τ) :=
  match f.domain with
  | ⟨τ', h⟩ =>
    if heq : τ' = τ then by
      subst heq
      exact .some h
    else .none

def Domain.assert_complete (h : Domain (τ_c := τ_c) f τ) : assert_domain f τ = .some h := by
  have h := h.complete
  simp [assert_domain, h]
  grind

def readback_fold {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackFold f h_dom e_h hlt hrt f') :=
  match hrt.reduction.snd.cases_comp x,  hrt.reduction.snd.cases_congr x with
  /-| .inl ⟨g, h, hrt'⟩, _ =>
    have heq' : hrt.reduction = ⟨DCC? (g (h x)), hrt'⟩ := by
      let hr₀ := hrt.reduction.snd
      have h := hrt'.eq ((hrt'.unique hr₀) ▸ hr₀)
      grind
    have heq₁ : hrt.reduction.fst = (DCC? (g (h x))) := by grind
    match h.assert_domain A with
    | .some h_dom_h =>
      if hlt' : max_hole h < lv then
        match view_app_hole? h x lv hlt' e_h.max_hole with
        | .some hrt_h =>
          have h_dec : h.size < f.size := by
            have h_dec := hrt.reduction.snd.decreasing
            have h_size_zero := e_h.size_zero
            grind
          match readback_fold h_dom_h e_h hlt' hrt_h with
          | .some ⟨g', hrbf⟩ =>
            match (DCC? (g ∘ g')).assert_domain A with
            | .some hrt_comp =>
              if hlt'' : (DCC? (g ∘ g')).max_hole < lv then
                match view_app_hole? (DCC? (g ∘ g')) x lv hlt'' e_h.max_hole with
                | .some hrt_h' =>
                  match hrt_h'.readback_head? hrt_comp e_h hlt'' with
                  | .some ⟨_, hrb''⟩ =>
                    .some ⟨_, .comp heq₁ (by assumption) (by assumption) (by assumption) hrbf (by assumption) (by assumption) (by assumption) hrb''⟩
                  | .none => .none
                | .none => .none
              else .none
            | .none => .none
          | .none => .none
        | .none => .none
      else .none
    | .none => .none-/
  | _, .inl ⟨g, y, hrt'⟩ =>
    have heq' : hrt.reduction = ⟨DCC? (g y x), hrt'⟩ := by
      let hr₀ := hrt.reduction.snd
      have h := hrt'.eq ((hrt'.unique hr₀) ▸ hr₀)
      grind
    have heq₁ : hrt.reduction.fst = (DCC? (g y x)) := by grind
    let g₁ := (red_spine_star (DCC? (g y))).fst
    match g₁.assert_domain A with
    | .some h_dom_g₁ =>
      if hlt' : max_hole g₁ < lv then
        match view_app_hole? g₁ x lv hlt' e_h.max_hole with
        | .some hrt_h =>
          have h_dec : g₁.size < f.size := by
            have h_dec := hrt.reduction.snd.decreasing
            have h_size_zero := e_h.size_zero
            have h_dec₂ := (red_spine_star (DCC? (g y))).snd.fst.decreasing?
            grind
          match readback_fold h_dom_g₁ e_h hlt' hrt_h with
          | .some ⟨g', hrbf⟩ =>
            match g'.assert_domain A with
            | .some h_dom_g' =>
              if hlt'' : g'.max_hole < lv then
                match view_app_hole? g' x lv hlt'' e_h.max_hole with
                | .some hrt_h' =>
                  match hrt_h'.readback_head? h_dom_g' e_h hlt'' with
                  | .some ⟨_, hrb''⟩ =>
                    .some ⟨_, .congr heq₁ (red_spine_star (DCC? (g y))).snd.fst (red_spine_star (DCC? (g y))).snd.snd.down (by assumption) (by assumption) (by assumption) hrbf (by assumption) (by assumption) (by assumption) hrb''⟩
                  | .none => .none
                | .none => .none
              else .none
            | .none => .none
          | .none => .none
        | .none => .none
      else .none
    | .none => .none
  | _, .inr ⟨hn₂⟩ =>
    match hrt.readback_head? h_dom e_h hlt with
    | .some ⟨_, hrb⟩ => .some ⟨_, .single (fun ⦃g₁⦄ ⦃h₁⦄ heq => hn₂ heq) hrb⟩
    | .none => .none
termination_by f.size

def ReadbackFold.complete (h : ReadbackFold (τ_c := τ_c) f h_dom e_h hlt hrt f') : readback_fold h_dom e_h hlt hrt = .some ⟨f', h⟩ := by
  induction h with
  | single hn₁ =>
    unfold readback_fold
    simp
    split
    /-case h_1 hrt' heq =>
      expose_names
      have heq_hrt_fst : hrt_1.reduction.fst = g.app (h.app hole_e) :=
        (hrt'.unique hrt_1.reduction.snd).symm
      exact (hn₁ heq_hrt_fst).elim-/
    case h_1 hrt' heq =>
      expose_names
      have heq_hrt_fst : hrt_1.reduction.fst = (g.app y).app hole_e :=
        (hrt'.unique hrt_1.reduction.snd).symm
      exact (hn₁ heq_hrt_fst).elim
    case h_2 hn₁' heq₁ heq₂ =>
      expose_names
      simp [hrb.complete]
  | congr heq =>
    unfold readback_fold
    simp
    split
    /-case h_1 hrt' heq =>
      expose_names
      cases hrt'.unique (heq_1 ▸ hrt_1.reduction.snd)-/
    case h_1 hrt' heq =>
      expose_names
      cases hrt'.unique (heq_1 ▸ hrt_1.reduction.snd)
      have heq_star := red_spine_star_complete hr (by assumption)
      have heq_star' : (g.app y).red_spine_star.fst = g₁ := by grind
      have heq_dom₁ := hdg.complete
      have heq_dom₂ := h_dom'.complete
      have heq_dom_g' : g'.domain.fst = a := by grind
      subst heq_dom_g'
      subst heq_star'
      simp [hdg.assert_complete, hlt₁, hrtg.complete, hrbg_ih, h_dom'.assert_complete, hlt₂, hrt'_1.complete, hrb'.complete]
      exact hr.eq.symm
    case h_2 hn₁ heq₁ =>
      exact (hn₁ (by assumption)).elim
  /-| comp heq =>
    unfold readback_fold
    simp
    split
    case h_2 hrt' heq hn =>
      expose_names
      cases hrt'.unique (heq_1 ▸ hrt_1.reduction.snd)
    case h_1 hrt' heq =>
      expose_names
      cases hrt'.unique (heq_1 ▸ hrt_1.reduction.snd)
      have heq_dom₁ := hdg.complete
      have heq_dom₂ := h_dom'.complete
      have heq_dom_g' : (g.comp g').domain.fst = a := by grind
      subst heq_dom_g'
      simp [hdg.assert_complete, hlt₁, hrtg.complete, hrbg_ih, h_dom'.assert_complete, hlt₂, hrt'_1.complete, hrb'.complete]
    case h_3 hn₁ hn₂ heq₁ heq₂ =>
      exact (hn₁ (by assumption)).elim-/

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
#eval try_readback (DCC (Λ(Sort 1, `(Sort 1, Sort 1), `(Sort 1, ⊤) ∘ Fst(`(Sort 1, Sort 1))) (Sort 0)))

/-
Example:

Λ(Sort 1, Id(Sort 1), Fst(Id(Sort 1))) (Sort 0)

Have no refl case in η so that funext is forced.
-/

def ReadbackFold.unique (hrb₁ : ReadbackFold (τ_c := τ_c) f h_dom₁ e_h hlt₁ hrt₁ f')
  (hrb₂ : ReadbackFold f h_dom₁ e_h hlt₁ hrt₁ g') : f' = g' := by
  have ha := hrb₁.complete
  have hb := hrb₂.complete
  grind

def ReadbackFold.eq (hrb₁ hrb₂ : ReadbackFold (τ_c := τ_c) f h_dom₁ e_h hlt₁ hrt₁ f') : hrb₁ = hrb₂ := by
  have ha := hrb₁.complete
  have hb := hrb₂.complete
  grind

def ReadbackFold.ext (hr₁ : RedSpineCongrNorm (DCC? (f x)) B)
  (hr₂    : RedSpineCongrNorm (DCC? (g x)) B)
  (h_dom₁ : Domain f A)
  (h_dom₂ : Domain g A)
  (e_h    : Hole A lv x)
  (hlt₁   : f.max_hole < lv)
  (hlt₂   : g.max_hole < lv)
  (hrt₁   : f.ViewAppHole x lv hlt₁ e_h.max_hole)
  (hrt₂   : g.ViewAppHole x lv hlt₂ e_h.max_hole)
  (hrb₁   : ReadbackFold f h_dom₁ e_h hlt₁ hrt₁ f')
  (hrb₂   : ReadbackFold g h_dom₂ e_h hlt₂ hrt₂ g') : f' = g' := by
  induction hrb₁ with
  | single =>
    induction hrb₂ with
    | single =>
      expose_names
      have h := hrb.ext (by sorry) hrb_1
      sorry

end GenericExpr
