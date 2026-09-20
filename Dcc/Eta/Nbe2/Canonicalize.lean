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
  | _, .inr ⟨hn₂⟩ =>
    match hrt.readback_head? h_dom e_h hlt with
    | .some ⟨_, hrb⟩ => .some ⟨_, .single (fun ⦃g₁⦄ heq => hn₂ heq) hrb⟩
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
      have heq_hrt_fst : hrt_1.reduction.fst = g.app hole_e :=
        (unique hrt' hrt_1.reduction.snd).symm
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
      cases unique hrt' (heq_1 ▸ hrt_1.reduction.snd)
      have heq_star := RedChoiceStar.complete hr
      have heq_star' : (run_norm RedHead g).fst = g₁ := by grind
      have heq_dom₁ := hdg.complete
      have heq_dom₂ := h_dom'.complete
      have heq_dom_g' : g'.domain.fst = a := by grind
      subst heq_dom_g'
      subst heq_star'
      simp [hdg.assert_complete, hlt₁, hrtg.complete, hrbg_ih, h_dom'.assert_complete, hlt₂, hrt'_1.complete, hrb'.complete]
      apply proof_eq
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

inductive RedEta : (e : GenericExpr τ_c) → (e' : GenericExpr τ_c) → Type u
  | sort   : RedEta (DCC? Sort m) (DCC? Sort m)
  | top    : RedEta (DCC? ⊤) (DCC? ⊤)
  | bot    : RedEta (DCC? ⊥) (DCC? ⊥)
  | tintro : RedEta (DCC? ∗) (DCC? ∗)
  | eq     : RedEta x x' → RedEta y y' → RedEta (DCC? x = y) (DCC? x' = y')
  | refl   : RedEta B B' → RedEta env env' → RedEta x x' → RedEta (DCC? (refl(B) env x)) (DCC? (refl(B') env' x'))
  | mkc    : RedEta B B' → RedEta x x' → RedEta y y' → RedEta (DCC? ⟦B⟧(x, y)) (DCC? ⟦B'⟧(x', y'))
  | bang   : RedEta A A' → RedEta (DCC? !(A)) (DCC? !(A'))
  | box    : RedEta x x' → RedEta (DCC? &(x)) (DCC? &(x'))
  | coup   : RedEta B B' → RedEta (DCC? Coup(B)) (DCC? Coup(B'))
  | pi     : RedEta B B'
    → RedAffNorm (DCC? (C env)) ⟨C₁, hn⟩
    → RedEta C₁ C'
    → RedEta env env'
    → Domain C τ
    → RedAffNorm (DCC? (B' env')) ⟨A, hn_A⟩
    → RedEta (DCC? (Π(B, C) env)) (DCC? (Π(Id(τ), `(τ, C')) A))
  | fn     : (h_dom : Domain f A) → (e_h : Hole A f.max_hole.succ x)
    → (hrt : f.ViewAppHole x f.max_hole.succ (by grind) e_h.max_hole)
    → (hrb : ReadbackFold f h_dom e_h (by grind) hrt f')
    → RedEta f f'

def red_eta (e : GenericExpr τ_c) : Option (Σ' (e' : GenericExpr τ_c), RedEta e e') :=
  match e with
  | DCC? ∗ | DCC? ⊥ | DCC? ⊤ | DCC? Sort _m => .some ⟨_, by constructor⟩
  | DCC? x = y =>
    match x.red_eta, y.red_eta with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => .some ⟨_, .eq h₁ h₂⟩
    | _, _ => .none
  | DCC? (refl(B) env x) =>
    match B.red_eta with
    | .some ⟨_, h₁⟩ =>
      match env.red_eta, x.red_eta with
      | .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ => .some ⟨_, .refl h₁ h₂ h₃⟩
      | _, _ => .none
    | .none => .none
  | DCC? ⟦B⟧(x, y) =>
    match B.red_eta with
    | .some ⟨_, h₁⟩ =>
      match x.red_eta, y.red_eta with
      | .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ => .some ⟨_, .mkc h₁ h₂ h₃⟩
      | _, _ => .none
    | .none => .none
  | DCC? !(A) =>
    match A.red_eta with
    | .some ⟨_, h⟩ => .some ⟨_, .bang h⟩
    | .none => .none
  | DCC? Coup(B) =>
    match B.red_eta with
    | .some ⟨_, h⟩ => .some ⟨_, .coup h⟩
    | .none => .none
  | DCC? &(x) =>
    match x.red_eta with
    | .some ⟨_, h⟩ => .some ⟨_, .box h⟩
    | .none => .none
  | DCC? (Π(B, C) x) =>
    match B.red_eta with
    | .some ⟨_, h₁⟩ =>
      match (reduce RedAff (DCC? (C x))).fst.red_eta with
      | .some ⟨_, h₂⟩ =>
        match x.red_eta with
        | .some ⟨_, h₃⟩ =>
          .some ⟨_, .pi h₁ ⟨reduce_sound rfl, reduce_norm rfl⟩ h₂ h₃ C.domain.snd ⟨reduce_sound rfl, reduce_norm rfl⟩⟩
        | .none => .none
      | .none => .none
    | .none => .none
  | f =>
    let h_dom := f.domain.snd
    let ⟨x, e_h⟩ := mk_hole f.domain.fst f.max_hole.succ
    match view_app_hole? f x f.max_hole.succ (by grind) e_h.max_hole with
    | .some h =>
      match readback_fold h_dom e_h (by grind) h with
      | .some ⟨_, hrb⟩ => .some ⟨_, .fn h_dom e_h h hrb⟩
      | .none => .none
    | .none => .none
termination_by (e.size, sizeOf e)
decreasing_by any_goals (grind)

def RedEta.complete (h : RedEta (τ_c := τ_c) e e') : red_eta e = .some ⟨e', h⟩ := by
  induction h with
  | coup | box | bang | mkc | refl | eq | top | bot | tintro | sort => simp_all [red_eta]
  | pi hr_B hr_env_C hr_C hr_env h_dom hrid =>
    have heq  := hr_env_C.complete_fst
    have heq₁ := hrid.complete_fst
    have heq₂ := h_dom.complete
    cases heq.symm
    cases heq₁.symm
    expose_names
    simp_all [red_eta, hr_env_C.eq, hrid.eq]
    cases unique C.domain.snd h_dom
    simp [proof_eq C.domain.snd h_dom]
    constructor <;> apply RedAffNorm.eq
  | fn h_dom e_h hrt hrb =>
    unfold red_eta
    split
    any_goals (
      focus
      try (
        cases hrt
        expose_names
        cases elim_norm (fun _ ⟨_, h⟩ => by cases h) hrt
        grind)
      done)
    case h_12 =>
      expose_names
      have h₁ := h_dom.complete
      have h₂ := e_h.complete
      have h₃ := hrt.complete
      have h₄ := hrb.complete
      grind

instance : Run Option (RedEta (τ_c := τ_c)) := ⟨red_eta⟩
instance : Complete' Option (RedEta (τ_c := τ_c)) := ⟨RedEta.complete⟩

end GenericExpr
