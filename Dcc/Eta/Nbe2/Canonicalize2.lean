import Dcc.Eta.Nbe2.RedSpine

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

/-
To η-reduce a function, track movement of the hole through the function.

"Optimize" the function by looking for any steps that can be removed.
These are steps where ViewAppHole is a no-op on the hole.
-/

namespace GenericExpr

inductive ViewAppHole : (f : GenericExpr τ_c)
  → (hole₁ : GenericExpr τ_c)
  → (lv    : ℕ)
  → (hlt   : f.max_hole < lv)
  → (hmem  : lv ≤ hole₁.max_hole)
  → Type u
  | quot   : RedSpineNorm (DCC? (f hole₁)) x'
    → (hn  : x'.max_hole < lv)
    → ViewAppHole f hole₁ lv hlt hmem
  -- par is not actually a case. this is the fallback that should hit if no ViewAppHole is present
  /-| par    : RedAffNorm (DCC? (f hole₁)) ⟨(DCC? (f' hole₁)), hn'⟩
    → (hlt : f.max_hole < hole₁.min_hole)
    → ViewAppHole f hole₁ hlt-/
  -- Note: this will need to recurse since we can't just blindly assume hole₁
  -- we just need to know the hole is in there somewhere could be f (g (h hole))
  -- if this does not fire, just do quot
  | comp   : (hrt : RedSpineNorm (DCC? ((f ∘ g) x)) e')
    → (hgt : e'.max_hole ≥ lv)
    → (hsp : hrt.head = ⟨DCC? (f (g x)), ⟨.comp⟩, .comp⟩)
    → ViewAppHole g x lv (by grind) (by grind)
    → ViewAppHole (DCC? (f ∘ g)) x lv hlt hmem
  | comp'  : (hrt : RedSpineNorm (DCC? ((f ∘' g) x)) e')
    → (hgt : e'.max_hole ≥ lv)
    → (hsp : hrt.head = ⟨DCC? (f (g x)), ⟨.comp'⟩, .comp'⟩)
    → ViewAppHole g x lv (by grind) (by grind)
    → ViewAppHole (DCC? (f ∘' g)) x lv hlt hmem
  | comp₂  : (hrt : RedSpineNorm (DCC? ((f ∘∘ g) x)) e')
    → (hgt : e'.max_hole ≥ lv)
    → (hsp : hrt.head = ⟨DCC? (f (g x)), ⟨.comp₂⟩, .comp₂⟩)
    → ViewAppHole g x lv (by grind) (by grind)
    → ViewAppHole (DCC? (f ∘∘ g)) x lv hlt hmem
  /-
    Since we are weak-head reducing, and since
    the root expression should already be in normal form (NOTE TODO ENFORCE THIS),
    it doesn't matterh what RedSpineNorm reduces to
    just what the last step was
  -/
  | id     : (hrt : RedSpineNorm (DCC? (Id(A) x)) x)
    → (hsp : hrt.head = ⟨x, ⟨.id⟩, .id⟩)
    → ViewAppHole (DCC? Id(A)) x lv hlt hmem
  | fst    : (hrt : RedSpineNorm (DCC? (Fst(B) ⟦_B⟧(x, y))) x)
    → (hsp : hrt.head = ⟨x, ⟨.fstc⟩, .fstc⟩)
    → ViewAppHole (DCC? Fst(B)) (DCC? ⟦_B⟧(x, y)) lv hlt hmem
  | snd    : (hrt : RedSpineNorm (DCC? (Snd(B) ⟦_B⟧(x, y))) y)
    → (hsp : hrt.head = ⟨y, ⟨.sndc⟩, .sndc⟩)
    → ViewAppHole (DCC? Snd(B)) (DCC? ⟦_B⟧(x, y)) lv hlt hmem
  -- Purpose of SpineNorm is to handle top-level weak head steps that produce further normal forms
  -- innere congruences, which are irrelevant, so we eliminate them by considering only WHNF reductions
  | eval   : (hrt : RedSpineNorm (DCC? (Eval(A, B, x) ⟦_B⟧(y, z))) e')
    → (hsp : hrt.head = ⟨DCC? (x y z), ⟨.evalc⟩, .eval⟩)
    → ViewAppHole (DCC? Eval(A, B, x)) (DCC? ⟦_B⟧(y, z)) lv hlt hmem
  | curr'  : (hrt : RedSpineNorm (DCC? (!Λ(A, B, x) &(y) &(z))) e')
    → (hsp : hrt.head = ⟨DCC? (x &(⟦B⟧(y, z))), ⟨.curr'⟩, .curr'⟩)
    → ViewAppHole x (DCC? &(⟦B⟧(y, z))) lv (by grind) (by grind)
    → ViewAppHole (DCC? (!Λ(A, B, x) &(y))) (DCC? &(z)) lv hlt hmem
  | curr   : (hrt : RedSpineNorm (DCC? (Λ(A, B, x) y z)) e')
    → (hsp : hrt.head = ⟨DCC? (x ⟦B⟧(y, z)), ⟨.curr⟩, .curr⟩)
    → ViewAppHole x (DCC? ⟦B⟧(y, z)) lv (by grind) (by grind)
    → ViewAppHole (DCC? (Λ(A, B, x) y)) z lv hlt hmem
  | eql    : (hrt : RedSpineNorm (DCC? (Eql(B) &(x) &(y))) e')
    → (hsp : hrt.head = ⟨DCC? (y = y), ⟨.eql⟩, .eql⟩)
    → ViewAppHole (DCC? (Eql(B) &(x))) (DCC? &(y)) lv hlt hmem
  /-
    Recursively canonicalize the points inside all combinators.
    This handles the inner congruences.

    BIG TODO
  -/
  | pair   : (hrt : RedSpineNorm (DCC? (⟦B⟧⟨x, y⟩ &(z))) e')
    → (hsp : hrt.head = ⟨DCC? ⟦(B z)⟧((x z), (y z (x z))), ⟨.pair⟩, .pair⟩)
    → ViewAppHole (DCC? ⟦B⟧⟨x, y⟩) (DCC? &(z)) lv hlt hmem
  | unmap  : (hrt : RedSpineNorm (DCC? (*<x> &(y))) e')
    → (hsp : hrt.head = ⟨DCC? (x y), ⟨.unmap⟩, .unmap⟩)
    → ViewAppHole (DCC? *<x>) (DCC? &(y)) lv hlt hmem
  | fmap  : (hrt : RedSpineNorm (DCC? ($<x> &(y))) e')
    → (hsp : hrt.head = ⟨DCC? &((x y)), ⟨.fmap⟩, .fmap⟩)
    → ViewAppHole (DCC? $<x>) (DCC? &(y)) lv hlt hmem
  | map   : (hrt : RedSpineNorm (DCC? (!<x> &(y))) e')
    → (hsp : hrt.head = ⟨DCC? !((x y)), ⟨.map⟩, .map⟩)
    → ViewAppHole (DCC? !<x>) (DCC? &(y)) lv hlt hmem
  -- if τ contains the hole, then this is Σ
  -- otherwise, the Coup does not depend on the hole
  -- in which case it is just `(
  | sigma    : (hrt : RedSpineNorm (DCC? (Σ(B, C) x)) e')
    → (hsp : hrt.head = ⟨DCC? Coup((C x)), ⟨.sigma⟩, .sigma⟩)
    → ViewAppHole C x lv (by grind) (by grind)
    → ViewAppHole (DCC? Σ(B, C)) x lv hlt hmem
deriving Repr

set_option maxHeartbeats 10000000000 in
def view_app_hole? (f hole₁ : GenericExpr τ_c) (lv : ℕ) (hlt : f.max_hole < lv) (hmem : lv ≤ hole₁.max_hole) : Option (ViewAppHole f hole₁ lv hlt hmem) :=
  match (DCC? (f hole₁)).red_spine!! with
  | .some ⟨e', hrt⟩ =>
    if hn' : e'.max_hole < lv then
      .some (.quot hrt hn')
    else
      -- In remaining cases, just show that no reduction is possible
      match f with
      | DCC? Id(A) =>
        if heq : e' = hole₁ then by
          subst heq
          exact .some (.id hrt (
            match heq₂ : hrt.head with
            | ⟨_, _, .id⟩ => by simp_all only [not_lt]))
        else .none
      | DCC? `(B, x) =>
        have hn'' : e'.max_hole < lv := by
          match heq₂ : hrt.head with
          | ⟨_, ⟨.quot⟩, .quot⟩ =>
            have heq_fst : hrt.head.fst = x := by simp_all
            let h := heq_fst ▸ hrt.head_rest
            have h_dec  := RedAff.max_hole_preserved (.quot (β := B) (x := x) (y := hole₁))
            have h_dec₂ := h.max_hole_preserved
            have h_dec₃ : e'.max_hole ≥ lv := by simp_all
            grind
          | ⟨_, ⟨.congrFun h⟩, hn⟩ =>
            cases hn
            grind
        (hn' hn'').elim
      | DCC? f ∘ g =>
        match g.view_app_hole? hole₁ lv (by grind) (by grind) with
        | .some h =>
          .some (.comp hrt (by grind) (
            match heq₂ : hrt.head with
            | ⟨_, _, .comp⟩ => by simp_all only [not_lt]) h)
        | .none => .none
      | DCC? f ∘' g =>
        match g.view_app_hole? hole₁ lv (by grind) (by grind) with
        | .some h =>
          .some (.comp' hrt (by grind) (
            match heq₂ : hrt.head with
            | ⟨_, _, .comp'⟩ => by simp_all only [not_lt]) h)
        | .none => .none
      | DCC? f ∘∘ g =>
        match g.view_app_hole? hole₁ lv (by grind) (by grind) with
        | .some h =>
          .some (.comp₂ hrt (by grind) (
            match heq₂ : hrt.head with
            | ⟨_, _, .comp₂⟩ => by simp_all only [not_lt]) h)
        | .none => .none
      | DCC? Fst(B) => by
        cases hole₁
        case mkc =>
          rename_i B x y
          if heq : e' = x then
            subst heq
            exact .some (.fst hrt (match heq₂ : hrt.head with
              | ⟨_, _, .fstc⟩ => by simp_all only [not_lt]))
          else exact .none
        any_goals (
          exact False.elim (by
            match heq₂ : hrt.head with
            | ⟨_, hr, hn⟩ => cases hn))
      | DCC? Snd(B) => by
        cases hole₁
        case mkc =>
          rename_i B x y
          if heq : e' = y then
            subst heq
            exact .some (.snd hrt (match heq₂ : hrt.head with
              | ⟨_, _, .sndc⟩ => by simp_all only [not_lt]))
          else exact .none
        any_goals (
          exact False.elim (by
            match heq₂ : hrt.head with
            | ⟨_, hr, hn⟩ => cases hn))
      | DCC? Eval(A, B, x) => by
        cases hole₁
        case mkc =>
          exact .some (.eval hrt (match heq₂ : hrt.head with
              | ⟨_, _, .eval⟩ => by simp_all only [not_lt]))
        any_goals (
          exact False.elim (by
            match heq₂ : hrt.head with
            | ⟨_, hr, hn⟩ => cases hn))
      | DCC? ⟦B⟧⟨x, y⟩ => by
        cases hole₁
        case box =>
          exact .some (.pair hrt (match heq₂ : hrt.head with
              | ⟨_, _, .pair⟩ => by simp_all only [not_lt]))
        any_goals (
          exact False.elim (by
            match heq₂ : hrt.head with
            | ⟨_, hr, hn⟩ => cases hn))
      | DCC? *<x> => by
        cases hole₁
        case box =>
          exact .some (.unmap hrt (match heq₂ : hrt.head with
              | ⟨_, _, .unmap⟩ => by simp_all only [not_lt]))
        any_goals (
          exact False.elim (by
            match heq₂ : hrt.head with
            | ⟨_, hr, hn⟩ => cases hn))
      | DCC? $<x> => by
        cases hole₁
        case box =>
          exact .some (.fmap hrt (match heq₂ : hrt.head with
              | ⟨_, _, .fmap⟩ => by simp_all only [not_lt]))
        any_goals (
          exact False.elim (by
            match heq₂ : hrt.head with
            | ⟨_, hr, hn⟩ => cases hn))
      | DCC? !<x> => by
        cases hole₁
        case box =>
          exact .some (.map hrt (match heq₂ : hrt.head with
              | ⟨_, _, .map⟩ => by simp_all only [not_lt]))
        any_goals (
          exact False.elim (by
            match heq₂ : hrt.head with
            | ⟨_, hr, hn⟩ => cases hn))
      | DCC? Σ(B, C) => by
        match C.view_app_hole? hole₁ lv (by grind) (by grind) with
        | .some h =>
          exact .some (.sigma hrt (match heq₂ : hrt.head with
            | ⟨_, _, .sigma⟩ => by simp_all only [not_lt]) h)
        | .none => exact .none
      | DCC? Dom(_x) | DCC? Sort _m | DCC? ∗ | DCC? ⊤ | DCC? ⊥
      | DCC? (_x = _y) | DCC? refl(_B) | DCC? ⟦_B⟧(_x, _y) | DCC? Coup(_B)
      | DCC? Π(_B, _C) | DCC? !(_A) | .const _n | .hole _n =>
        False.elim (by
          match hrt.head with
          | ⟨B, ⟨hr⟩, hn⟩ =>
            cases hr <;> cases hn)
      | DCC? (a b) => by
        cases a
        case curr =>
          rename_i A B x
          match x.view_app_hole? (DCC? ⟦B⟧(b, hole₁)) lv (by grind) (by grind) with
          | .some h =>
            exact .some (.curr hrt (match heq₂ : hrt.head with
            | ⟨_, _, .curr⟩ => by simp_all only [not_lt]) h)
          | .none => exact .none
        case curr' =>
          rename_i A B x
          cases b
          case box b =>
            cases hole₁
            case box c =>
              match x.view_app_hole? (DCC? &(⟦B⟧(b, c))) lv (by grind) (by grind) with
              | .some h =>
                exact .some (.curr' hrt (match heq₂ : hrt.head with
                  | ⟨_, _, .curr'⟩ => by simp_all only [not_lt]) h)
              | .none => exact .none
            any_goals (
            exact False.elim (by
              match heq₂ : hrt.head with
              | ⟨_, hr, hn⟩ => cases hn))
          -- These are impossible due to head reduction not existing so the hole is contained in output
          any_goals (
            exact False.elim (by
              match heq₂ : hrt.head with
              | ⟨_, hr, hn⟩ => cases hn))
        case eql =>
          cases b
          case box b =>
            cases hole₁
            case box c =>
              exact .some (.eql hrt (by
                match heq₂ : hrt.head with
                | ⟨_, hr, .eql⟩ => simp_all only [not_lt]))
            any_goals (
            exact False.elim (by
              match heq₂ : hrt.head with
              | ⟨_, hr, hn⟩ => cases hn))
          any_goals (
            exact False.elim (by
              match heq₂ : hrt.head with
              | ⟨_, hr, hn⟩ => cases hn))
        any_goals (
          exact False.elim (by
          match hrt.head with
          | ⟨B, ⟨hr⟩, hn⟩ =>
            cases hr <;> cases hn))
  | .none => .none

end GenericExpr
