import Dcc.Eta.Nbe2.Readback

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

open CasesHead
open Single
open ElimNorm

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
    (hneq₁ : ∀ ⦃g⦄, hrt.reduction.fst ≠ (DCC? (g x)))
    → (hneq₂ : ∀ ⦃g h⦄, hrt.reduction.fst ≠ (DCC? (g (h x))))
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
    → (h_dom' : Domain (DCC? (∘ g g')) A)
    → (hlt₂   : (DCC? (∘ g g')).max_hole < lv)
    → (hrt'   : ViewAppHole (DCC? (∘ g g')) x lv hlt₂ e_h.max_hole)
    → (hrb'   : Readback (DCC? (∘ g g')) h_dom' e_h hlt₂ hrt' f')
    → ReadbackFold f h_dom e_h hlt hrt f'
  | congr {f  : GenericExpr τ_c}
    {h_dom    : Domain f A}
    {e_h      : Hole A lv x}
    {hlt      : f.max_hole < lv}
    {hrt      : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq      : hrt.reduction.fst = (DCC? (g x)))
    → (hr     : DSL(g →!wh⋆ g₁))
    → (hdg    : Domain g₁ A)
    → (hlt₁   : max_hole g₁ < lv)
    → (hrtg   : ViewAppHole g₁ x lv hlt₁ e_h.max_hole)
    → (hrbg   : ReadbackFold g₁ hdg e_h hlt₁ hrtg g')
    → (h_dom' : Domain g' A)
    → (hlt₂   : g'.max_hole < lv)
    → (hrt'   : ViewAppHole g' x lv hlt₂ e_h.max_hole)
    → (hrb'   : Readback g' h_dom' e_h hlt₂ hrt' f')
    → ReadbackFold f h_dom e_h hlt hrt f'
deriving Repr

def AndNorm.cases_comp (x : GenericExpr τ_c) (h : DSL(A →!wh⁺ B)) : (Σ g h, DSL(A →!wh⁺ (g (h x)))) ⊕ (PLift (∀ ⦃g h⦄, B ≠ (DCC? (g (h x))))) := by
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

def AndNorm.cases_congr (x : GenericExpr τ_c) (h : DSL(A →!wh⁺ B)) : (Σ g, DSL(A →!wh⁺ (g x))) ⊕ (PLift (∀ ⦃g⦄, B ≠ (DCC? (g x)))) := by
  cases B
  case app f y =>
    if heq : y = x then
      subst heq
      exact .inl ⟨_, h⟩
    else
      (exact .inr ⟨fun g heq => by cases heq; grind⟩)
  all_goals (exact .inr ⟨fun g heq => by cases heq⟩)

def assert_domain (f τ : GenericExpr τ_c) : Option (Domain f τ) :=
  match f.domain with
  | ⟨τ', h⟩ =>
    if heq : τ' = τ then by
      subst heq
      exact .some h
    else .none

def Domain.assert_complete (h : Domain (τ_c := τ_c) f τ) : assert_domain f τ = .some h := by
  have h := complete h
  simp [Run.run, pure] at h
  simp [assert_domain, h]
  grind

def readback_fold {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackFold f h_dom e_h hlt hrt f') :=
  dbg_trace repr hrt.reduction.fst
  match hrt.reduction.snd.cases_comp x,  hrt.reduction.snd.cases_congr x with
  | .inl ⟨g, h, hrt'⟩, _ =>
    have heq' : hrt.reduction = ⟨DCC? (g (h x)), hrt'⟩ := by
      let hr₀ := hrt.reduction.snd
      have h := proof_eq hrt' ((unique hrt' hr₀) ▸ hr₀)
      grind
    have heq₁ : hrt.reduction.fst = (DCC? (g (h x))) := by grind
    match h.assert_domain A with
    | .some h_dom_h =>
      if hlt' : max_hole h < lv then
        match view_app_hole? h x lv hlt' e_h.max_hole with
        | .some hrt_h =>
          have h_dec : h.size < f.size := by
            have h_dec := decreasing hrt.reduction.snd
            have h_size_zero := e_h.size_zero
            grind
          match readback_fold h_dom_h e_h hlt' hrt_h with
          | .some ⟨g', hrbf⟩ =>
            match (DCC? (∘ g g')).assert_domain A with
            | .some hrt_comp =>
              if hlt'' : (DCC? (∘ g g')).max_hole < lv then
                match view_app_hole? (DCC? (∘ g g')) x lv hlt'' e_h.max_hole with
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
    | .none => .none
  | _, .inl ⟨g, hrt'⟩ =>
    have heq' : hrt.reduction = ⟨DCC? (g x), hrt'⟩ := by
      let hr₀ := hrt.reduction.snd
      have h := proof_eq hrt' ((unique hrt' hr₀) ▸ hr₀)
      grind
    have heq₁ : hrt.reduction.fst = (DCC? (g x)) := by grind
    let g₁ := (run_norm RedHead g).fst
    match g₁.assert_domain A with
    | .some h_dom_g₁ =>
      if hlt' : max_hole g₁ < lv then
        match view_app_hole? g₁ x lv hlt' e_h.max_hole with
        | .some hrt_h =>
          have h_dec : g₁.size < f.size := by
            have h_dec := decreasing hrt.reduction.snd
            have h_size_zero := e_h.size_zero
            have h_dec₂ := Decreasing?.decreasing?' (run_norm RedHead g).snd.fst
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
                    .some ⟨_, .congr heq₁ (run_norm RedHead g).snd (by assumption) (by assumption) (by assumption) hrbf (by assumption) (by assumption) (by assumption) hrb''⟩
                  | .none => .none
                | .none => .none
              else .none
            | .none => .none
          | .none => .none
        | .none => .none
      else .none
    | .none => .none
  | .inr ⟨hn₁⟩, .inr ⟨hn₂⟩ =>
    match hrt.readback_head? h_dom e_h hlt with
    | .some ⟨_, hrb⟩ => .some ⟨_, .single (fun ⦃g₁⦄ heq => hn₂ heq) (fun ⦃g₁ h₁⦄ heq => hn₁ heq) hrb⟩
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

def ReadbackFold.complete (h : ReadbackFold (τ_c := τ_c) f h_dom e_h hlt hrt f') : readback_fold h_dom e_h hlt hrt = .some ⟨f', h⟩ := by
  induction h with
  | single hn₁ =>
    unfold readback_fold
    simp
    split
    case h_1 hn₁ hn₂ _ _ _ _ _ hrt' heq =>
      expose_names
      have heq_hrt_fst : hrt_1.reduction.fst = g.app (h.app hole_e) :=
        (unique hrt' hrt_1.reduction.snd).symm
      exact (hn₂ heq_hrt_fst).elim
    case h_2 hrt' _ heq =>
      expose_names
      have heq_hrt_fst : hrt_1.reduction.fst = g.app hole_e :=
        (unique hrt' hrt_1.reduction.snd).symm
      exact (hn₁ heq_hrt_fst).elim
    case h_3 hn₁' heq₁ heq₂ =>
      expose_names
      simp [hrb.complete]
  | congr heq =>
    unfold readback_fold
    simp
    split
    case h_1 hrt' heq =>
      expose_names
      cases unique hrt' (heq_1 ▸ hrt_1.reduction.snd)
    case h_2 hrt' _ heq =>
      expose_names
      cases unique hrt' (heq_1 ▸ hrt_1.reduction.snd)
      have heq_star := RedChoiceStar.complete hr
      have heq_star' : (run_norm RedHead g).fst = g₁ := by grind
      have heq_dom₁ := Complete'.complete hdg
      have heq_dom₂ := Complete'.complete h_dom'
      simp [Run.run, pure] at heq_dom₁
      simp [Run.run, pure] at heq_dom₂
      have heq_dom_g' : g'.domain.fst = a := by grind
      subst heq_dom_g'
      subst heq_star'
      simp [hdg.assert_complete, hlt₁, hrtg.complete, hrbg_ih, h_dom'.assert_complete, hlt₂, hrt'_1.complete, hrb'.complete]
      apply proof_eq
    case h_3 hn₁ _ heq₁ =>
      exact (hn₁ (by assumption)).elim
  | comp heq =>
    unfold readback_fold
    simp
    split
    case h_2 hrt' heq hn =>
      expose_names
      cases unique hrt' (heq_1 ▸ hrt_1.reduction.snd)
    case h_1 hrt' heq =>
      expose_names
      cases unique hrt' (heq_1 ▸ hrt_1.reduction.snd)
      have heq_dom₁ := Complete'.complete hdg
      have heq_dom₂ := Complete'.complete h_dom'
      simp [Run.run, pure] at heq_dom₁
      simp [Run.run, pure] at heq_dom₂
      have heq_dom_g' : (g.comp g').domain.fst = a := by grind
      subst heq_dom_g'
      simp [hdg.assert_complete, hlt₁, hrtg.complete, hrbg_ih, h_dom'.assert_complete, hlt₂, hrt'_1.complete, hrb'.complete]
    case h_3 hn₁ hn₂ heq₁ heq₂ =>
      exact (hn₁ (by assumption)).elim

--#eval try_readback (DCC (Λ(Sort 1, Id(Sort 1), Fst(Id(Sort 1))) (Sort 0)))
open Dsl in
#eval try_readback (DCC
  ((Λ (Sort 1)
      (` (Sort 1) Sort 1)
      (Eval (Sort 1)
            (` (Sort 1) Sort 1)
            (` (Sort 1) (` (Sort 1) ⊤))))
   (Sort 0)))

open Dsl in
#eval try_readback (DCC
  ((Λ (Sort 1)
      (` (Sort 1) Sort 1)
      (∘ (` (Sort 1) ⊤)
         (Fst (` (Sort 1) Sort 1))))
   (Sort 0)))

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

/-def ReadbackFold.ext (hr₁ : DSL((f x) →!whᶠ⁺ B))
  (hr₂    : DSL((g x) →!whᶠ⁺ B))
  (h_dom₁ : Domain f A)
  (h_dom₂ : Domain g A)
  (e_h    : Hole A lv x)
  (hlt₁   : f.max_hole < lv)
  (hlt₂   : g.max_hole < lv)
  (hrt₁   : f.ViewAppHole x lv hlt₁ e_h.max_hole)
  (hrt₂   : g.ViewAppHole x lv hlt₂ e_h.max_hole)
  (hrb₁   : ReadbackFold f h_dom₁ e_h hlt₁ hrt₁ f')
  (hrb₂   : ReadbackFold g h_dom₂ e_h hlt₂ hrt₂ g') : f' = g' := by
  match cases_head hr₁.raw, cases_head hr₂.raw with
  | .inl ⟨hr₁, heq₁⟩, .inl ⟨hr₂, heq₂⟩ =>
    cases hr₁ with
    | single hr₁ =>
      cases hr₂ with
      | single hr₂ =>
        match hrb₁, hrb₂ with
        | .single hneq₁ hrb₁, .single hneq₂ hrb₂ =>
          sorry
        | .congr heq₁ hrg₁ hdg₁ hlt₁ hrtg₁ hrbg₁ h_dom'₁ hlt₂₁ hrt'₁ hrb'₁, _
        | _, .congr heq₁ hrg₁ hdg₁ hlt₁ hrtg₁ hrbg₁ h_dom'₁ hlt₂₁ hrt'₁ hrb'₁ =>
          
          sorry
      | congrFun hr₂ hn₂ =>
        sorry
    | congrFun hr₁ hn₁ =>
      cases hr₂ with
      | single hr₂ =>
        sorry
      | congrFun hr₂ hn₂ =>
        sorry
  | .inl h₁, .inr h₂ =>
    sorry
  | .inr h₁, .inl h₂ =>
    sorry
  | .inr h₁, .inr h₂ =>
    sorry-/

/-def ReadbackFold.ext (hr₁ : DSL((f x) →!whᶠ⋆ B))
  (hr₂    : DSL((g x) →!whᶠ⋆ B))
  (h_dom₁ : Domain (τ_c := τ_c) f A)
  (h_dom₂ : Domain g A)
  (e_h    : Hole A lv x)
  (hlt₁   : f.max_hole < lv)
  (hlt₂   : g.max_hole < lv)
  (hrt₁   : f.ViewAppHole x lv hlt₁ e_h.max_hole)
  (hrt₂   : g.ViewAppHole x lv hlt₂ e_h.max_hole)
  (hrb₁   : ReadbackFold f h_dom₁ e_h hlt₁ hrt₁ f')
  (hrb₂   : ReadbackFold g h_dom₂ e_h hlt₂ hrt₂ g') : f' = g' := by
  match cases_star hr₁.raw, cases_star hr₂.raw with
  | .inl heq₁, _ =>
    sorry
  | _, .inl heq₂ =>
    sorry
  | .inr (.inl ⟨h₁, heq₁⟩), .inr (.inl ⟨h₂, heq₂⟩) =>
    
    match h₁, h₂ with
    | .single h₁, .single h₂ =>
      have hrt'₁ : DSL((f x) →!wh⁺ B) := ⟨Single.single (by assumption), ⟨hr₁.is_norm.to_single⟩⟩
      have hrt'₂ : DSL((g x) →!wh⁺ B) := ⟨Single.single (by assumption), ⟨hr₂.is_norm.to_single⟩⟩
      have heq_points : hrt₁.reduction.fst = hrt₂.reduction.fst := by
        have h₁ := Unique.unique hrt'₁ hrt₁.reduction.snd
        have h₂ := Unique.unique hrt'₂ hrt₂.reduction.snd
        grind
      have heq_B₁ : B = hrt₁.reduction.fst := by
        have h₁ := Unique.unique hrt'₁ hrt₁.reduction.snd
        have h₂ := Unique.unique hrt'₂ hrt₂.reduction.snd
        grind
      have heq_B₂ : B = hrt₂.reduction.fst := by
        have h₁ := Unique.unique hrt'₁ hrt₁.reduction.snd
        have h₂ := Unique.unique hrt'₂ hrt₂.reduction.snd
        grind
      cases hrb₁ with
      | single =>
        cases hrb₂ with
        | single =>
          expose_names
          exact Readback.ext
            (hrb₁   := hrb)
            (hrb₂   := hrb_1)
            (h_dom₁ := h_dom₁)
            (h_dom₂ := h_dom₂)
            (e_h    := e_h)
            (hlt₁   := hlt₁)
            (hlt₂   := hlt₂)
            (hrt₁   := by assumption)
            (hrt₂   := by assumption)
            (hr₁    := hrt'₁)
            (hr₂    := hrt'₂)
        | congr =>
          expose_names
          have heq_reduction : g_1.app x = B :=
            heq.symm.trans (Unique.unique hrt₂.reduction.snd hrt'₂)
          have heq_reduction₁ : hrt₁.reduction.fst = g_1.app x := by
            have h := Unique.unique hrt₁.reduction.snd hrt'₁
            grind
          cases heq_reduction.symm
          exact (hneq₁ heq_reduction₁).elim
      | congr =>
        expose_names
        cases hrb₂ with
        | single =>
          expose_names
          have heq_reduction : g_1.app x = B :=
            heq.symm.trans (Unique.unique hrt₁.reduction.snd hrt'₁)
          have heq_reduction₁ : hrt₂.reduction.fst = g_1.app x := by
            have h := Unique.unique hrt₂.reduction.snd hrt'₂
            grind
          cases heq_reduction.symm
          exact (hneq₁ heq_reduction₁).elim
        | congr =>
          expose_names
          have heq_red_fst := (heq_1.symm.trans heq_points.symm).trans heq
          cases heq_red_fst
          cases heq_B₂.trans heq_1
          have hna : IsNorm' RedCongrFun (g_1.app x) := hr₁.is_norm
          cases elim_norm hna.congrFun.to_single hr
          cases elim_norm hna.congrFun.to_single hr_1
          have hn'₁ : DSL((g_1 x) →!whᶠ⋆ (g_1 x)) := ⟨.refl, ⟨hna⟩⟩
          cases hdg.eq hdg_1
          cases hrtg.eq hrtg_1
          cases hrbg.unique hrbg_1
          cases hrbg.eq hrbg_1
          cases h_dom'_1.unique h_dom'
          cases h_dom'_1.eq h_dom'
          cases hrt'_1.eq hrt'
          cases readback_unique hrb' hrb'_1
          rfl
    | .congrFun hn₁ hr₁, .single hr₂ =>
      expose_names
      have h_dec := decreasing hr₁
      have hr₁_1' : DSL((f'_1 x) →!whᶠ⋆ (f'_1 x)) := ⟨.refl, ⟨hr₁_1.is_norm⟩⟩
      apply ReadbackFold.ext
      exact hr₁_1'
      any_goals (assumption)
      
      /-have hrt'₁ : DSL((f x) →!wh⁺ B) := ⟨Single.single (by assumption), ⟨hr₁.is_norm.to_single⟩⟩
      have hrt'₂ : DSL((g x) →!wh⁺ B) := ⟨Single.single (by assumption), ⟨hr₂.is_norm.to_single⟩⟩-/
      sorry
  | .inr (.inr ⟨h₁, heq₁⟩), .inr (.inr ⟨h₂, heq₂⟩) =>
    sorry
termination_by f.size + x.size-/

open Dsl in
inductive Readback₂ : (f : GenericExpr τ_c) → (f' : GenericExpr τ_c) → Type u
  -- Contains x and y
  | curr  : (h_dom : Domain x τ₀)
    → (e_h    : Hole τ₀ (DCC? (Λ A B x)).max_hole.succ (DCC? (,B₀ x₀ y₀)))
    → (hrt    : ViewAppHole x (DCC? (,B₀ x₀ y₀)) (DCC? (Λ A B x)).max_hole.succ (by grind) e_h.max_hole)
    → (hrb    : ReadbackFold (lv := (DCC? (Λ A B x)).max_hole.succ) (f := x) (f' := f') h_dom' (x := (DCC? (,B₀ x₀ y₀))) e_h (by grind) hrt)
    -- This is handled by Id instead of curry eval
    → (hneq   : hrt.reduction.fst ≠ (DCC? (x₀ y₀)))
    → (hrτ_y  : RedAffNorm (DCC? (B x₀)) ⟨τ_y, hn⟩)
    -- This is handled by quotation
    → (hgt    : (¬ hrt.reduction.fst.max_hole < (DCC? (Λ A B x)).max_hole.succ) ∨ (x₀.max_hole ≤ τ_y.max_hole))
    → Readback₂ (DCC? (Λ A B x)) (DCC? (Λ A B f'))
  -- Is exactly x y
  | id    : (h_dom : Domain x τ₀)
    → (e_h     : Hole τ₀ (DCC? (Λ A B x)).max_hole.succ (DCC? (,B₀ x₀ y₀)))
    → (hrt     : ViewAppHole x (DCC? (,B₀ x₀ y₀)) (DCC? (Λ A B x)).max_hole.succ (by grind) e_h.max_hole)
    → (heq     : hrt.reduction.fst = (DCC? (x₀ y₀)))
    -- This is handled by quotation
    → (h_dom_B : Domain B A')
    → Readback₂ (DCC? (Λ A B x)) (DCC? (Id A'))
  | quot  : (h_dom : Domain x τ₀)
    → (e_h     : Hole τ₀ (DCC? (Λ A B x)).max_hole.succ (DCC? (,B₀ x₀ y₀)))
    → (hrt     : ViewAppHole x (DCC? (,B₀ x₀ y₀)) (DCC? (Λ A B x)).max_hole.succ (by grind) e_h.max_hole)
    → (hgt     : hrt.reduction.fst.max_hole < (DCC? (Λ A B x)).max_hole.succ)
    → (hrτ_y   : RedAffNorm (DCC? (B x₀)) ⟨τ_y, hn⟩)
    → (hmem_τy : ¬ x₀.max_hole ≤ τ_y.max_hole)
    → (h_dom_B : Domain B A')
    → Readback₂ (DCC? (Λ A B x)) (DCC? (`A (` τ_y hrt.reduction.fst)))
  | curr' : (h_dom : Domain x τ₀)
    → (e_h    : Hole τ₀ (DCC? (!Λ A B x)).max_hole.succ (DCC? (& (,B₀ x₀ y₀))))
    → (hrt    : ViewAppHole x (DCC? (& (,B₀ x₀ y₀))) (DCC? (!Λ A B x)).max_hole.succ (by grind) e_h.max_hole)
    → (hrb    : ReadbackFold (lv := (DCC? (!Λ A B x)).max_hole.succ) (f := x) (f' := f') h_dom' (x := (DCC? (& (,B₀ x₀ y₀)))) e_h (by grind) hrt)
    -- This is handled by Id instead of curry eval
    → (hrτ_y  : RedAffNorm (DCC? (B x₀)) ⟨τ_y, hn⟩)
    -- This is handled by quotation
    → (hgt    : (¬ hrt.reduction.fst.max_hole < (DCC? (!Λ A B x)).max_hole.succ) ∨ (x₀.max_hole ≤ τ_y.max_hole))
    → Readback₂ (DCC? (!Λ A B x)) (DCC? (!Λ A B f'))
  | quot' : (h_dom : Domain x τ₀)
    → (e_h     : Hole τ₀ (DCC? (!Λ A B x)).max_hole.succ (DCC? (& (,B₀ x₀ y₀))))
    → (hrt     : ViewAppHole x (DCC? (& (,B₀ x₀ y₀))) (DCC? (!Λ A B x)).max_hole.succ (by grind) e_h.max_hole)
    → (hgt     : hrt.reduction.fst.max_hole < (DCC? (!Λ A B x)).max_hole.succ)
    → (hrτ_y   : RedAffNorm (DCC? (B x₀)) ⟨τ_y, hn⟩)
    → (hmem_τy : ¬ x₀.max_hole ≤ τ_y.max_hole)
    → (h_dom_B : Domain B A')
    → Readback₂ (DCC? (!Λ A B x)) (DCC? (`(! A) (` (! τ_y) hrt.reduction.fst)))
deriving Repr

def readback₂ (f : GenericExpr τ_c) : Option (Σ' (f' : GenericExpr τ_c), Readback₂ f f') :=
  match f with
  | DCC? (Λ A B x) =>
    let A'    := x.domain.fst
    let h_dom := x.domain.snd
    match mk_hole A' (DCC? (Λ A B x)).max_hole.succ with
    | ⟨DCC? (,B₀ x₀ y₀), e_h⟩ =>
      match view_app_hole? x (DCC? (,B₀ x₀ y₀)) (DCC? (Λ A B x)).max_hole.succ (by grind) e_h.max_hole with
      | .some hrt =>
        if heq : hrt.reduction.fst = (DCC? (x₀ y₀)) then
          .some ⟨_, .id h_dom e_h hrt heq B.domain.snd⟩
        else if hgt : hrt.reduction.fst.max_hole < (DCC? (Λ A B x)).max_hole.succ ∧ (¬ x₀.max_hole ≤ (reduce RedAff (DCC? (B x₀))).fst.max_hole) then
          .some ⟨_, .quot h_dom e_h hrt hgt.left ⟨reduce_sound rfl, reduce_norm rfl⟩ hgt.right B.domain.snd⟩
        else
          match readback_fold h_dom e_h (by grind) hrt with
          | .some ⟨_, hrb⟩ => .some ⟨_, .curr h_dom e_h hrt hrb (by grind) ⟨reduce_sound rfl, reduce_norm rfl⟩ (by grind)⟩
          | .none => .none
      | .none => .none
    | _ => .none
  | DCC? (!Λ A B x) =>
    let A'    := x.domain.fst
    let h_dom := x.domain.snd
    match mk_hole A' (DCC? (!Λ A B x)).max_hole.succ with
    | ⟨DCC? (& (,B₀ x₀ y₀)), e_h⟩ =>
      match view_app_hole? x (DCC? (& (,B₀ x₀ y₀))) (DCC? (!Λ A B x)).max_hole.succ (by grind) e_h.max_hole with
      | .some hrt =>
        if hgt : hrt.reduction.fst.max_hole < (DCC? (!Λ A B x)).max_hole.succ ∧ (¬ x₀.max_hole ≤ (reduce RedAff (DCC? (B x₀))).fst.max_hole) then
          .some ⟨_, .quot' h_dom e_h hrt hgt.left ⟨reduce_sound rfl, reduce_norm rfl⟩ hgt.right B.domain.snd⟩
        else
          match readback_fold h_dom e_h (by grind) hrt with
          | .some ⟨_, hrb⟩ => .some ⟨_, .curr' h_dom e_h hrt hrb ⟨reduce_sound rfl, reduce_norm rfl⟩ (by grind)⟩
          | .none => .none
      | .none => .none
    | _ => .none
  | _ => .none

def Readback₂.complete (h : Readback₂ (τ_c := τ_c) f f') : readback₂ f = .some ⟨f', h⟩ := by
  unfold readback₂
  cases h with
  | quot' h_dom e_h hrt hgt hrτ_y hmem_τy h_dom_B =>
    have h₁ := Complete'.complete h_dom
    have h₁_fst := complete_fst h_dom
    have h₂ := e_h.complete
    have h₃ := hrτ_y.complete
    have h₄ := hrt.complete
    have h₅ := Complete'.complete h_dom_B
    simp [Run.run, pure] at h₁
    simp [Run.run] at h₁_fst
    simp [Run.run, pure] at h₅
    cases h₁_fst
    cases h₅
    simp [h₂, h₄]
    expose_names
    simp [hgt]
    simp [red_aff] at h₃
    cases h₃
    replace hmem_τy : (reduce RedAff (B.app x₀)).fst.max_hole < x₀.max_hole := by
      grind
    simp [hmem_τy]
    unfold GenericExpr.domain
    simp
    cases hrτ_y.eq
    exact ⟨by apply proof_eq, rfl⟩
  | quot h_dom e_h hrt hgt hrτ_y hmem_τy h_dom_B =>
    have h₁ := Complete'.complete h_dom
    have h₁_fst := complete_fst h_dom
    have h₂ := e_h.complete
    have h₃ := hrτ_y.complete
    have h₄ := hrt.complete
    have h₅ := Complete'.complete h_dom_B
    simp [Run.run, pure] at h₁
    simp [Run.run] at h₁_fst
    simp [Run.run, pure] at h₅
    cases h₁_fst
    cases h₅
    simp [h₂, h₄]
    expose_names
    have hneq : hrt.reduction.fst ≠ x₀.app y₀ := fun h => by
      have h := e_h.max_hole
      grind
    simp [hneq, hgt]
    simp [red_aff] at h₃
    cases h₃
    replace hmem_τy : (reduce RedAff (B.app x₀)).fst.max_hole < x₀.max_hole := by
      grind
    simp [hmem_τy]
    unfold GenericExpr.domain
    simp
    cases hrτ_y.eq
    exact ⟨by apply proof_eq, rfl⟩
  | id h_dom e_h hrt heq h_dom_B =>
    have h₁ := Complete'.complete h_dom
    have h₁_fst := complete_fst h_dom
    have h₂ := e_h.complete
    have h₃ := hrt.complete
    have h₄ := Complete'.complete h_dom_B
    simp [Run.run, pure] at h₁
    simp [Run.run] at h₁_fst
    simp [Run.run, pure] at h₄
    cases h₁_fst
    cases h₄
    simp [h₂, h₃, heq]
    unfold GenericExpr.domain
    simp
    apply proof_eq
  | curr h_dom e_h hrt hrb hneq hrτ_y hgt =>
    have h₁ := Complete'.complete h_dom
    have h₁_fst := complete_fst h_dom
    have h₂ := e_h.complete
    have h₃ := hrt.complete
    have h₄ := hrτ_y.complete_fst
    have h₅ := hrb.complete
    simp [Run.run, pure] at h₁
    simp [Run.run] at h₁_fst
    cases h₁_fst
    cases h₄
    simp [h₂, h₃, hneq]
    expose_names
    cases proof_eq h_dom' h_dom
    cases hrτ_y.eq
    cases proof_eq x.domain.snd h_dom'
    match hgt with
    | .inl h =>
      simp [h, h₅]
      rfl
    | .inr h =>
      split
      · grind
      case isFalse =>
        simp [h₅]
        rfl
  | curr' h_dom e_h hrt hrb hrτ_y hgt =>
    have h₁ := Complete'.complete h_dom
    have h₁_fst := complete_fst h_dom
    have h₂ := e_h.complete
    have h₃ := hrt.complete
    have h₄ := hrτ_y.complete_fst
    have h₅ := hrb.complete
    simp [Run.run, pure] at h₁
    simp [Run.run] at h₁_fst
    simp
    cases h₁_fst
    cases h₄
    simp [h₂, h₃]
    expose_names
    cases proof_eq h_dom' h_dom
    cases hrτ_y.eq
    cases proof_eq x.domain.snd h_dom'
    match hgt with
    | .inl h =>
      simp [h, h₅]
      rfl
    | .inr h =>
      split
      · grind
      case isFalse =>
        simp [h₅]
        rfl

instance : Run Option (Readback₂ (τ_c := τ_c)) := ⟨readback₂⟩
instance : Complete' Option (Readback₂ (τ_c := τ_c)) := ⟨Readback₂.complete⟩

open Dsl in
inductive Canonicalize : (e : GenericExpr τ_c) → (e' : GenericExpr τ_c) → Type u
  | sort   : Canonicalize (DCC? Sort m) (DCC? Sort m)
  | top    : Canonicalize (DCC? ⊤) (DCC? ⊤)
  | bot    : Canonicalize (DCC? ⊥) (DCC? ⊥)
  | tintro : Canonicalize (DCC? ∗) (DCC? ∗)
  | eq     : Canonicalize x x' → Canonicalize y y' → Canonicalize (DCC? x = y) (DCC? x' = y')
  | refl₂  : Canonicalize B B' → Canonicalize env env' → Canonicalize x x' → Canonicalize (DCC? ((refl B) env x)) (DCC? ((refl B') env' x'))
  | refl   : Canonicalize B B' → Canonicalize (DCC? (refl B)) (DCC? (refl B'))
  | eql    : Canonicalize B B' → Canonicalize (DCC? (Eql B)) (DCC? (Eql B'))
  | mkc    : Canonicalize B B' → Canonicalize x x' → Canonicalize y y' → Canonicalize (DCC? (,B x y)) (DCC? (,B' x' y'))
  | bang   : Canonicalize A A' → Canonicalize (DCC? (! A)) (DCC? (! A'))
  | box    : Canonicalize x x' → Canonicalize (DCC? (& x)) (DCC? (& x'))
  | coup   : Canonicalize B B' → Canonicalize (DCC? (Σ B)) (DCC? (Σ B'))
  | pi     : Canonicalize B B'
    → RedAffNorm (DCC? (C env)) ⟨C₁, hn⟩
    → Canonicalize C₁ C'
    → Canonicalize env env'
    → Domain C τ
    → RedAffNorm (DCC? (B' env')) ⟨A, hn_A⟩
    → Canonicalize (DCC? ((Π B C) env)) (DCC? ((Π (Id τ) (`τ C')) A))
  | pi₀    : Canonicalize B B' → Canonicalize C C' → Canonicalize (DCC? (Π B C)) (DCC? (Π B' C'))
  | fn     : (h_dom : Domain f A) → (e_h : Hole A f.max_hole.succ x)
    → (hrt : f.ViewAppHole x f.max_hole.succ (by grind) e_h.max_hole)
    → (hrb : ReadbackFold f h_dom e_h (by grind) hrt f')
    → Canonicalize f f'
  | fn₂    : (h_dom : Domain f A) → (e_h : Hole A f.max_hole.succ x)
    → (hn  : f.ViewAppHole x f.max_hole.succ (by grind) e_h.max_hole → False)
    → (hrb : Readback₂ f f')
    → Canonicalize f f'
  -- In this case, (f x) must be congruence
deriving Repr

def canonicalize (e : GenericExpr τ_c) : Option (Σ' (e' : GenericExpr τ_c), Canonicalize e e') :=
  open Dsl in match e with
  | DCC? ∗ | DCC? ⊥ | DCC? ⊤ | DCC? Sort _m => .some ⟨_, by constructor⟩
  | DCC? x = y =>
    match x.canonicalize, y.canonicalize with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => .some ⟨_, .eq h₁ h₂⟩
    | _, _ => .none
  | DCC? ((refl B) env x) =>
    match B.canonicalize with
    | .some ⟨_, h₁⟩ =>
      match env.canonicalize, x.canonicalize with
      | .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ => .some ⟨_, .refl₂ h₁ h₂ h₃⟩
      | _, _ => .none
    | .none => .none
  | DCC? (,B x y) =>
    match B.canonicalize with
    | .some ⟨_, h₁⟩ =>
      match x.canonicalize, y.canonicalize with
      | .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ => .some ⟨_, .mkc h₁ h₂ h₃⟩
      | _, _ => .none
    | .none => .none
  | DCC? (! A) =>
    match A.canonicalize with
    | .some ⟨_, h⟩ => .some ⟨_, .bang h⟩
    | .none => .none
  | DCC? (Σ B) =>
    match B.canonicalize with
    | .some ⟨_, h⟩ => .some ⟨_, .coup h⟩
    | .none => .none
  | DCC? (& x) =>
    match x.canonicalize with
    | .some ⟨_, h⟩ => .some ⟨_, .box h⟩
    | .none => .none
  | DCC? (Π B C) =>
    match B.canonicalize, C.canonicalize with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .pi₀ h₁ h₂⟩
    | _, _ => .none
  | DCC? ((Π B C) x) =>
    match B.canonicalize with
    | .some ⟨_, h₁⟩ =>
      match (reduce RedAff (DCC? (C x))).fst.canonicalize with
      | .some ⟨_, h₂⟩ =>
        match x.canonicalize with
        | .some ⟨_, h₃⟩ =>
          .some ⟨_, .pi h₁ ⟨reduce_sound rfl, reduce_norm rfl⟩ h₂ h₃ C.domain.snd ⟨reduce_sound rfl, reduce_norm rfl⟩⟩
        | .none => .none
      | .none => .none
    | .none => .none
  | DCC? (refl B) =>
    match B.canonicalize with
    | .some ⟨_, h⟩ => .some ⟨_, .refl h⟩
    | .none => .none
  | DCC? (Eql B) =>
    match B.canonicalize with
    | .some ⟨_, h⟩ => .some ⟨_, .eql h⟩
    | .none => .none
  | f =>
    let h_dom := f.domain.snd
    let ⟨x, e_h⟩ := mk_hole f.domain.fst f.max_hole.succ
    match heq : view_app_hole? f x f.max_hole.succ (by grind) e_h.max_hole with
    | .some h =>
      match readback_fold h_dom e_h (by grind) h with
      | .some ⟨_, hrb⟩ => .some ⟨_, .fn h_dom e_h h hrb⟩
      | .none => .none
    | .none =>
      have hn : f.ViewAppHole x f.max_hole.succ (by grind) e_h.max_hole → False := by
        intro h
        simp_all [h.complete]
      match readback₂ f with
      | .some ⟨_, hrb⟩ =>
        .some ⟨_, .fn₂ h_dom e_h hn hrb⟩
      | .none => .none
termination_by (e.size, sizeOf e)
decreasing_by any_goals (grind)

def Canonicalize.complete (h : Canonicalize (τ_c := τ_c) e e') : canonicalize e = .some ⟨e', h⟩ := by
  induction h with
  | fn₂ h_dom e_h hn hrb =>
    have h₁ := Complete'.complete h_dom
    have h₂ := e_h.complete_fst
    have h₀ := e_h.complete
    expose_names
    have h₃ : f.view_app_hole? x f.max_hole.succ (by grind) e_h.max_hole = .none := by
      apply Option.eq_none_iff_forall_ne_some.mpr
      intro h
      cases hn h
    have h₄ := Complete'.complete hrb
    simp [Run.run, pure] at h₁
    simp [Run.run, pure] at h₄
    unfold canonicalize
    split
    any_goals (
      focus
      simp [readback₂] at h₄
      done)
    case h_15 =>
      expose_names
      cases h₁
      simp [domain]
      split
      case h_1 =>
        cases h₂
        grind
      · simp [h₄, h₂]
        grind
  | eql | refl | pi₀ | coup | box | bang | mkc | refl₂ | eq | top | bot | tintro | sort => simp_all [canonicalize]
  | pi hr_B hr_env_C hr_C hr_env h_dom hrid =>
    have heq  := hr_env_C.complete_fst
    have heq₁ := hrid.complete_fst
    have heq₂ := Complete'.complete h_dom
    cases heq.symm
    cases heq₁.symm
    expose_names
    simp_all [canonicalize, hr_env_C.eq, hrid.eq]
    cases unique C.domain.snd h_dom
    simp [proof_eq C.domain.snd h_dom]
    constructor <;> apply RedAffNorm.eq
  | fn h_dom e_h hrt hrb =>
    unfold canonicalize
    split
    any_goals (
      focus
      try (
        cases hrt
        expose_names
        cases elim_norm (fun _ ⟨_, h⟩ => by cases h) hrt
        grind)
      done)
    case h_15 =>
      expose_names
      have h₁ := Complete'.complete h_dom
      simp [Run.run, pure] at h₁
      have h₂ := e_h.complete
      have h₃ := hrt.complete
      have h₄ := hrb.complete
      grind

instance [Repr τ_c] : Repr (Σ' (B : GenericExpr τ_c), Canonicalize A B) := ⟨fun ⟨B, x⟩ =>
  Repr.addAppParen s!"PSigma.mk {repr B} ({repr x})"⟩

instance : Run Option (Canonicalize (τ_c := τ_c)) := ⟨canonicalize⟩
instance : Complete' Option (Canonicalize (τ_c := τ_c)) := ⟨Canonicalize.complete⟩

-- ((Π (Id Sort 0) (`Sort 0 (Π (Id ⊤) (Λ ⊤ (Id ⊤) (`(Σ (Id ⊤)) (Sort 2)))))) ⊤)
open Dsl in
#eval canonicalize (DCC ((Π (Id Sort 0) (`Sort 0 (Π (Id ⊤) (Λ ⊤ (` ⊤ (Sort 1)) (`(Σ (` ⊤ (Sort 1))) (Sort 2)))))) ⊤))

open Dsl in
inductive ViewPi : GenericExpr τ_c → Type u
  | mk : ViewPi (DCC? ((Π B C) x))

open Dsl in
def view_pi (e : GenericExpr τ_c) : Option (ViewPi e) :=
  match e with
  | DCC? ((Π _B _C) x) => .some .mk
  | _ => .none

def ViewPi.complete (h : ViewPi e) : view_pi e = .some h := by
  cases h
  simp [view_pi]

open Dsl in
inductive RedEta : (e : GenericExpr τ_c) → (e' : GenericExpr τ_c) → Type u
  | pi     : RedEta B B' → RedEta C C' → RedEta x x' → Canonicalize (DCC? ((Π B' C') x')) e' → RedEta (DCC? ((Π B C) x)) e'
  | canon₀ : (h_ar : point_arity e = 0) → (ViewPi e → False) → (hc  : Canonicalize e e') → RedEta e e'
  | canon₁ : (h_ar : point_arity e = 1) → (hc₁ : RedEta (points e)[0] p')
    → Canonicalize (set_points e ⟨#[p'], by grind⟩) e'
    → RedEta e e'
  | canon₂ : (h_ar : point_arity e = 2)
    → (hc₁ : RedEta (points e)[0] p'₁)
    → (hc₂ : RedEta (points e)[1] p'₂)
    → Canonicalize (set_points e ⟨#[p'₁, p'₂], by grind⟩) e'
    → RedEta e e'
  | canon₃ : (h_ar : point_arity e = 3)
    → (hc₁ : RedEta (points e)[0] p'₁)
    → (hc₂ : RedEta (points e)[1] p'₂)
    → (hc₃ : RedEta (points e)[2] p'₃)
    → Canonicalize (set_points e ⟨#[p'₁, p'₂, p'₃], by grind⟩) e'
    → RedEta e e'
deriving Repr

def red_eta (e : GenericExpr τ_c) : Option (Σ' (e' : GenericExpr τ_c), RedEta e e') :=
  open Dsl in if heq : point_arity e = 0 then
    if heq₂ : (view_pi e) = .none then
      match canonicalize e with
      | .some ⟨_, h⟩ => .some ⟨_, .canon₀ heq (fun h => by have heq' := h.complete; grind) h⟩
      | .none => .none
    else
    match e with
    | DCC? ((Π B C) x) =>
      match red_eta B, red_eta C with
      | .some ⟨B', h₁⟩, .some ⟨C', h₂⟩ =>
        match red_eta x with
        | .some ⟨x', h₃⟩ =>
          match canonicalize (DCC? ((Π B' C') x')) with
          | .some ⟨_, h₄⟩ =>
            .some ⟨_, .pi h₁ h₂ h₃ h₄⟩
          | .none => .none
        | .none => .none
      | _, _ => .none
    | _ => .none
  else if heq : point_arity e = 1 then
    have h_dec : sizeOf (points e)[0] < sizeOf e := by
      simp [points]
      split <;> grind
    match red_eta (points e)[0] with
    | .some ⟨p', h₁⟩ =>
      match canonicalize (set_points e ⟨#[p'], by grind⟩) with
      | .some ⟨_, h₂⟩ =>
        .some ⟨_, .canon₁ heq h₁ h₂⟩
      | .none => .none
    | .none => .none
  else if heq : point_arity e = 2 then
    have h_dec₁ : sizeOf (points e)[0] < sizeOf e := by
      simp [points]
      split <;> grind
    have h_dec₂ : sizeOf (points e)[1] < sizeOf e := by
      simp [points]
      split <;> grind
    match red_eta (points e)[0] with
    | .some ⟨p'₁, h₁⟩ =>
      match red_eta (points e)[1] with
      | .some ⟨p'₂, h₂⟩ =>
        match canonicalize (set_points e ⟨#[p'₁, p'₂], by grind⟩) with
        | .some ⟨_, h₃⟩ =>
          .some ⟨_, .canon₂ heq h₁ h₂ h₃⟩
        | .none => .none
      | .none => .none
    | .none => .none
  else if heq : point_arity e = 3 then
    have h_dec₁ : sizeOf (points e)[0] < sizeOf e := by
      simp [points]
      split <;> grind
    have h_dec₂ : sizeOf (points e)[1] < sizeOf e := by
      simp [points]
      split <;> grind
    have h_dec₃ : sizeOf (points e)[2] < sizeOf e := by
      simp [points]
      split <;> grind
    match red_eta (points e)[0] with
    | .some ⟨p'₁, h₁⟩ =>
      match red_eta (points e)[1] with
      | .some ⟨p'₂, h₂⟩ =>
        match red_eta (points e)[2] with
        | .some ⟨p'₃, h₃⟩ =>
          match canonicalize (set_points e ⟨#[p'₁, p'₂, p'₃], by grind⟩) with
          | .some ⟨_, h₄⟩ =>
            .some ⟨_, .canon₃ heq h₁ h₂ h₃ h₄⟩
          | .none => .none
        | .none => .none
      | .none => .none
    | .none => .none
  else .none
termination_by sizeOf e

def RedEta.complete (h : RedEta (τ_c := τ_c) e e') : red_eta e = .some ⟨e', h⟩ := by
  induction h with
  | pi =>
    expose_names
    unfold red_eta
    have heq := Complete'.complete a_3
    simp [point_arity, view_pi, a_ih_1, a_ih_2, a_ih]
    simp [Run.run, pure] at heq
    grind
  | canon₀ h_ar hn_pi hc =>
    expose_names
    have heq : view_pi e_1 = .none := by
      apply Option.eq_none_iff_forall_ne_some.mpr
      intro h
      exact (hn_pi h).elim
    have hc' := Complete'.complete hc
    simp [Run.run, pure] at hc'
    unfold red_eta
    simp [h_ar, heq, hc']
  | canon₁ h_ar ih₁ hc ih_heq =>
    have hc' := Complete'.complete hc
    simp [Run.run, pure] at hc'
    simp [red_eta, h_ar, hc', ih_heq]
  | canon₂ h_ar ih₁ ih₂ hc ih_heq ih_heq₂ =>
    have hc' := Complete'.complete hc
    simp [Run.run, pure] at hc'
    simp [red_eta, h_ar, hc', ih_heq, ih_heq₂]
  | canon₃ h_ar ih₁ ih₂ ih₃ hc ih_heq ih_heq₂ ih_heq₃ =>
    have hc' := Complete'.complete hc
    simp [Run.run, pure] at hc'
    simp [red_eta, h_ar, hc', ih_heq, ih_heq₂, ih_heq₃]

instance [Repr τ_c] : Repr (Σ' (B : GenericExpr τ_c), RedEta A B) := ⟨fun ⟨B, x⟩ =>
  Repr.addAppParen s!"PSigma.mk {repr B} ({repr x})"⟩

open Dsl in
#eval red_eta (DCC ((Π (Id Sort 0) (`Sort 0 (Π (Id ⊤) (Λ ⊤ (` ⊤ (Sort 1)) (`(Σ (` ⊤ (Sort 1))) (Sort 2)))))) ⊤))

instance : Run Option (RedEta (τ_c := τ_c)) := ⟨red_eta⟩
instance : Complete' Option (RedEta (τ_c := τ_c)) := ⟨RedEta.complete⟩

end GenericExpr

/-
Recursive canonicalize without size termination argument:

Index by Canonicalize f f'

| canon₁ : (h_ar : point_arity e = 1) → (hp : Canonicalize' ((points e).get 1) p')

then stope when reach point_arity = 0
-/

