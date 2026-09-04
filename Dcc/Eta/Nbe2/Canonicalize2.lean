import Dcc.Eta.Nbe2.RedSpine
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

set_option pp.deepTerms true
set_option pp.deepTerms.threshold 9999
set_option pp.proofs true
set_option pp.proofs.threshold 9999

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
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : hrt.head = ⟨DCC? (f (g x)), ⟨.comp⟩, .comp⟩)
    → ViewAppHole g x lv (by simp_all [max_hole]) (by simp_all [max_hole])
    → ViewAppHole (DCC? (f ∘ g)) x lv hlt hmem
  | comp'  : (hrt : RedSpineNorm (DCC? ((f ∘' g) x)) e')
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : hrt.head = ⟨DCC? (f (g x)), ⟨.comp'⟩, .comp'⟩)
    → ViewAppHole g x lv (by simp_all [max_hole]) (by simp_all [max_hole])
    → ViewAppHole (DCC? (f ∘' g)) x lv hlt hmem
  | comp₂  : (hrt : RedSpineNorm (DCC? ((f ∘∘ g) x)) e')
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : hrt.head = ⟨DCC? (f (g x)), ⟨.comp₂⟩, .comp₂⟩)
    → ViewAppHole g x lv (by simp_all [max_hole]) (by simp_all [max_hole])
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
    → (hgt : ¬ x.max_hole < lv)
    → (hsp : hrt.head = ⟨x, ⟨.fstc⟩, .fstc⟩)
    → ViewAppHole (DCC? Fst(B)) (DCC? ⟦_B⟧(x, y)) lv hlt hmem
  | snd    : (hrt : RedSpineNorm (DCC? (Snd(B) ⟦_B⟧(x, y))) y)
    → (hgt : ¬ y.max_hole < lv)
    → (hsp : hrt.head = ⟨y, ⟨.sndc⟩, .sndc⟩)
    → ViewAppHole (DCC? Snd(B)) (DCC? ⟦_B⟧(x, y)) lv hlt hmem
  -- Purpose of SpineNorm is to handle top-level weak head steps that produce further normal forms
  -- innere congruences, which are irrelevant, so we eliminate them by considering only WHNF reductions
  | eval   : (hrt : RedSpineNorm (DCC? (Eval(A, B, x) ⟦_B⟧(y, z))) e')
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : hrt.head = ⟨DCC? (x y z), ⟨.evalc⟩, .eval⟩)
    → ViewAppHole (DCC? Eval(A, B, x)) (DCC? ⟦_B⟧(y, z)) lv hlt hmem
  | curr'  : (hrt : RedSpineNorm (DCC? (!Λ(A, B, x) &(y) &(z))) e')
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : hrt.head = ⟨DCC? (x &(⟦B⟧(y, z))), ⟨.curr'⟩, .curr'⟩)
    → ViewAppHole x (DCC? &(⟦B⟧(y, z))) lv (by simp_all [max_hole]) (by simp_all [max_hole])
    → ViewAppHole (DCC? (!Λ(A, B, x) &(y))) (DCC? &(z)) lv hlt hmem
  | curr   : (hrt : RedSpineNorm (DCC? (Λ(A, B, x) y z)) e')
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : hrt.head = ⟨DCC? (x ⟦B⟧(y, z)), ⟨.curr⟩, .curr⟩)
    → ViewAppHole x (DCC? ⟦B⟧(y, z)) lv (by simp_all [max_hole]) (by simp_all [max_hole])
    → ViewAppHole (DCC? (Λ(A, B, x) y)) z lv hlt hmem
  | eql    : (hrt : RedSpineNorm (DCC? (Eql(B) &(x) &(y))) e')
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : hrt.head = ⟨DCC? (y = y), ⟨.eql⟩, .eql⟩)
    → ViewAppHole (DCC? (Eql(B) &(x))) (DCC? &(y)) lv hlt hmem
  /-
    Recursively canonicalize the points inside all combinators.
    This handles the inner congruences.

    BIG TODO
  -/
  | pair   : (hrt : RedSpineNorm (DCC? (⟦B⟧⟨x, y⟩ &(z))) e')
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : hrt.head = ⟨DCC? ⟦(B z)⟧((x z), (y z (x z))), ⟨.pair⟩, .pair⟩)
    → ViewAppHole (DCC? ⟦B⟧⟨x, y⟩) (DCC? &(z)) lv hlt hmem
  | unmap  : (hrt : RedSpineNorm (DCC? (*<x> &(y))) e')
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : hrt.head = ⟨DCC? (x y), ⟨.unmap⟩, .unmap⟩)
    → ViewAppHole (DCC? *<x>) (DCC? &(y)) lv hlt hmem
  | fmap  : (hrt : RedSpineNorm (DCC? ($<x> &(y))) e')
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : hrt.head = ⟨DCC? &((x y)), ⟨.fmap⟩, .fmap⟩)
    → ViewAppHole (DCC? $<x>) (DCC? &(y)) lv hlt hmem
  | map   : (hrt : RedSpineNorm (DCC? (!<x> &(y))) e')
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : hrt.head = ⟨DCC? !((x y)), ⟨.map⟩, .map⟩)
    → ViewAppHole (DCC? !<x>) (DCC? &(y)) lv hlt hmem
  -- if τ contains the hole, then this is Σ
  -- otherwise, the Coup does not depend on the hole
  -- in which case it is just `(
  | sigma    : (hrt : RedSpineNorm (DCC? (Σ(B, C) x)) e')
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : hrt.head = ⟨DCC? Coup((C x)), ⟨.sigma⟩, .sigma⟩)
    → ViewAppHole C x lv (by simp_all [max_hole]) (by simp_all [max_hole])
    → ViewAppHole (DCC? Σ(B, C)) x lv hlt hmem
deriving Repr

theorem RedSpineNorm.head_eq (h : RedSpineNorm A C) (hr : RedAff A B := by constructor) (hn : hr.IsHead := by constructor) : h.head = ⟨B, ⟨hr⟩, hn⟩ := by
  unfold head
  split
  case h_1 hr' hn' _ =>
    cases hn'.unique hn
    cases hn'.eq hn
    rfl
  case h_2 hr' hn' hrt' _ =>
    cases hn'.unique hn
    cases hn'.eq hn
    have h_dec := hr'.decreasing
    grind

def RedSpineNorm.fst_hole (hrt : RedSpineNorm (DCC? (Fst(B) hole₁)) e') : Σ' B x y, hole₁ = DCC? ⟦B⟧(x, y) :=
  match hole₁, e', hrt.head with
  | DCC? ⟦_B⟧(_x, _y), _e', ⟨_, _, .fstc⟩ => ⟨_, _, _, rfl⟩

def RedSpineNorm.snd_hole (hrt : RedSpineNorm (DCC? (Snd(B) hole₁)) e') : Σ' B x y, hole₁ = DCC? ⟦B⟧(x, y) :=
  match hole₁, e', hrt.head with
  | DCC? ⟦_B⟧(_x, _y), _e', ⟨_, _, .sndc⟩ => ⟨_, _, _, rfl⟩

def RedSpineNorm.eval_hole (hrt : RedSpineNorm (DCC? (Eval(A, B, x) hole₁)) e') : Σ' B x y, hole₁ = DCC? ⟦B⟧(x, y) :=
  match hole₁, e', hrt.head with
  | DCC? ⟦_B⟧(_x, _y), _e', ⟨_, _, .eval⟩ => ⟨_, _, _, rfl⟩

def RedSpineNorm.pair_hole (hrt : RedSpineNorm (DCC? (⟦B⟧⟨x, y⟩ hole₁)) e') : Σ' y, hole₁ = DCC? &(y) :=
  match hole₁, e', hrt.head with
  | DCC? &(_y), _e', ⟨_, _, .pair⟩ => ⟨_, rfl⟩

def RedSpineNorm.map_hole (hrt : RedSpineNorm (DCC? (!<x> hole₁)) e') : Σ' y, hole₁ = DCC? &(y) :=
  match hole₁, e', hrt.head with
  | DCC? &(_y), _e', ⟨_, _, .map⟩ => ⟨_, rfl⟩

def RedSpineNorm.unmap_hole (hrt : RedSpineNorm (DCC? (*<x> hole₁)) e') : Σ' y, hole₁ = DCC? &(y) :=
  match hole₁, e', hrt.head with
  | DCC? &(_y), _e', ⟨_, _, .unmap⟩ => ⟨_, rfl⟩

def RedSpineNorm.fmap_hole (hrt : RedSpineNorm (DCC? ($<x> hole₁)) e') : Σ' y, hole₁ = DCC? &(y) :=
  match hole₁, e', hrt.head with
  | DCC? &(_y), _e', ⟨_, _, .fmap⟩ => ⟨_, rfl⟩

def RedSpineNorm.curr'_hole (hrt : RedSpineNorm (DCC? (!Λ(A, B, x) y hole₁)) e') : Σ y' z, (PLift (y = (DCC? &(y')))) × (PLift (hole₁ = DCC? &(z))) :=
  match y, hole₁, e', hrt.head with
  | DCC? &(y), DCC? &(z), _e', ⟨_, _, .curr'⟩ => ⟨y, z, ⟨rfl⟩, ⟨rfl⟩⟩

def RedSpineNorm.eql_hole (hrt : RedSpineNorm (DCC? (Eql(B) x hole₁)) e') : Σ' x' y, (PLift (x = (DCC? &(x')))) × (PLift (hole₁ = DCC? &(y))) :=
  match x, hole₁, e', hrt.head with
  | DCC? &(y), DCC? &(z), _e', ⟨_, _, .eql⟩ => ⟨y, z, ⟨rfl⟩, ⟨rfl⟩⟩

def RedSpineNorm.parapp_elim (hrt : RedSpineNorm (DCC? (f y z)) e') : (Σ' A B x, f = (DCC? Λ(A, B, x))) ⊕ (Σ' A B x, f = (DCC? !Λ(A, B, x))) ⊕ (Σ' B, f = DCC? Eql(B)) := by
  cases f
  case curr =>
    cases hrt.head.snd
    case mk fst snd => exact .inl ⟨_, _, _, rfl⟩
  case curr' =>
    cases hrt.head.snd
    case mk fst snd =>
      exact .inr (.inl ⟨_, _, _, rfl⟩)
  case eql =>
    cases hrt.head.snd
    case mk fst snd =>
      exact .inr (.inr ⟨_, rfl⟩)
  all_goals (
    refine False.elim ?_
    match hrt.head with
    | ⟨_, ⟨hr⟩, hn⟩ => cases hn)

theorem RedSpineNorm.quot_no_mem (hrt : RedSpineNorm (DCC? (`(B, x) y)) e') (hlt : (DCC? `(B, x)).max_hole < lv) (hn : ¬ e'.max_hole < lv) (hmem : lv ≤ y.max_hole) : e'.max_hole < lv := by
  match heq₂ : hrt.head with
  | ⟨_, ⟨.quot⟩, .quot⟩ =>
    have heq_fst : hrt.head.fst = x := by simp_all
    let h := heq_fst ▸ hrt.head_rest
    have h_dec  := RedAff.max_hole_preserved (.quot (β := B) (x := x) (y := y))
    have h_dec₂ := h.max_hole_preserved
    have h_dec₃ : e'.max_hole ≥ lv := by simp_all
    grind
  | ⟨_, ⟨.congrFun h⟩, hn⟩ =>
    cases hn
    grind

theorem max_hole_points {e : GenericExpr τ} (n : ℕ) (hn : e.max_hole < lv) (hlt : n < e.point_arity := by grind) : (e.points.get ⟨n, hlt⟩).max_hole < lv := by
  induction e
  any_goals (simp [point_arity] at hlt)
  any_goals (simp_all [points, Vector.get, max_hole])
  any_goals (grind)

theorem max_hole_points_app (n : ℕ) (hn : (DCC? (f x)).max_hole < lv) (hlt : n < f.point_arity := by grind) : (f.points.get ⟨n, hlt⟩).max_hole < lv := by
  simp [max_hole] at hn
  exact max_hole_points n hn.left

def view_app_hole? (f hole₁ : GenericExpr τ_c) (lv : ℕ) (hlt : f.max_hole < lv) (hmem : lv ≤ hole₁.max_hole) : Option (ViewAppHole f hole₁ lv hlt hmem) :=
  match (DCC? (f hole₁)).red_spine!! with
  | .some ⟨e', hrt⟩ =>
    if hn' : e'.max_hole < lv then
      .some (.quot hrt hn')
    else
      -- In remaining cases, just show that no reduction is possible
      match f with
      | DCC? Id(A) => by
        if heq : e' = hole₁ then
          subst heq
          exact .some (.id hrt hrt.head_eq)
        else exact .none
      | DCC? `(B, x) =>
        have hn'' : e'.max_hole < lv := hrt.quot_no_mem hlt hn' hmem
        (hn' hn'').elim
      | DCC? f ∘ g =>
        match g.view_app_hole? hole₁ lv (max_hole_points 1 hlt) hmem with
        | .some h =>
          .some (.comp hrt hn' hrt.head_eq h)
        | .none => .none
      | DCC? f ∘' g =>
        match g.view_app_hole? hole₁ lv (max_hole_points 1 hlt) hmem with
        | .some h =>
          .some (.comp' hrt hn' hrt.head_eq h)
        | .none => .none
      | DCC? f ∘∘ g =>
        match g.view_app_hole? hole₁ lv (max_hole_points 1 hlt) hmem with
        | .some h =>
          .some (.comp₂ hrt hn' hrt.head_eq h)
        | .none => .none
      | DCC? Fst(B) =>
        match hrt.fst_hole with
        | ⟨B, x, y, heq₀⟩ => by
          if heq : e' = x then
            subst heq₀
            subst heq
            exact .some (.fst hrt hn' hrt.head_eq)
          else exact .none
      | DCC? Snd(B) =>
        match hrt.snd_hole with
        | ⟨B, x, y, heq₀⟩ => by
          if heq : e' = y then
            subst heq₀
            subst heq
            exact .some (.snd hrt hn' hrt.head_eq)
          else exact .none
      | DCC? Eval(A, B, x) =>
        match hrt.eval_hole with
        | ⟨B, x, y, heq₀⟩ => by
          subst heq₀
          exact .some (.eval hrt hn' hrt.head_eq)
      | DCC? ⟦B⟧⟨x, y⟩ =>
        match hrt.pair_hole with
        | ⟨_, heq₀⟩ => by
          subst heq₀
          exact .some (.pair hrt hn' hrt.head_eq)
      | DCC? *<x> =>
        match hrt.unmap_hole with
        | ⟨_, heq₀⟩ => by
          subst heq₀
          exact .some (.unmap hrt hn' hrt.head_eq)
      | DCC? $<x> =>
        match hrt.fmap_hole with
        | ⟨_, heq₀⟩ => by
          subst heq₀
          exact .some (.fmap hrt hn' hrt.head_eq)
      | DCC? !<x> =>
        match hrt.map_hole with
        | ⟨_, heq₀⟩ => by
          subst heq₀
          exact .some (.map hrt hn' hrt.head_eq)
      | DCC? Σ(B, C) =>
        match C.view_app_hole? hole₁ lv (max_hole_points 1 hlt) hmem with
        | .some h =>
          .some (.sigma hrt hn' hrt.head_eq h)
        | .none => .none
      | DCC? Dom(_x) | DCC? Sort _m | DCC? ∗ | DCC? ⊤ | DCC? ⊥
      | DCC? (_x = _y) | DCC? refl(_B) | DCC? ⟦_B⟧(_x, _y) | DCC? Coup(_B)
      | DCC? Π(_B, _C) | DCC? !(_A) | .const _n | .hole _n => False.elim (hrt.elim_norm_flse (fun _ hr hn => nomatch hn))
      | DCC? (a b) =>
        match hrt.parapp_elim with
        | .inl ⟨A, B, x, heq₀⟩ => by
          subst heq₀
          match x.view_app_hole? (DCC? ⟦B⟧(b, hole₁)) lv (max_hole_points_app 2 hlt) (by simp [max_hole] at hlt; simp [max_hole]; omega) with
          | .some h =>
            exact .some (.curr hrt hn' hrt.head_eq h)
          | .none => exact .none
        | .inr (.inl ⟨A, B, x, heq₀⟩) => by
          subst heq₀
          match hrt.curr'_hole with
          | ⟨b, c, ⟨heq₁⟩, ⟨heq₂⟩⟩ =>
            subst heq₁
            subst heq₂
            match x.view_app_hole? (DCC? &(⟦B⟧(b, c))) lv (max_hole_points_app 2 hlt) (by grind only [max_hole, = max_def]) with
            | .some h =>
              exact .some (.curr' hrt hn' hrt.head_eq h)
            | .none => exact .none
        | .inr (.inr ⟨B, heq₀⟩) => by
          subst heq₀
          match hrt.eql_hole with
          | ⟨b, c, ⟨heq₁⟩, ⟨heq₂⟩⟩ =>
            subst heq₁
            subst heq₂
            exact .some (.eql hrt hn' hrt.head_eq)
  | .none => .none

set_option maxHeartbeats 10000000000 in
def view_app_hole? (f hole₁ : GenericExpr τ_c) (lv : ℕ) (hlt : f.max_hole < lv) (hmem : lv ≤ hole₁.max_hole) : Option (ViewAppHole f hole₁ lv hlt hmem) :=
  match (DCC? (f hole₁)).red_spine!! with
  | .some ⟨_e', hrt⟩ => view_app_hole_red? f hole₁ hrt lv hlt hmem
  | .none => .none

theorem ViewAppHole.complete (h : ViewAppHole (τ_c := τ_c) f hole₁ lv hlt mem) : view_app_hole? f hole₁ lv hlt mem = .some h := by
  induction h
  case curr | curr' | comp | comp' | comp₂ | sigma
    | id | fst | snd | eval | eql | pair | unmap | fmap | map
    | quot =>
    unfold view_app_hole?; unfold view_app_hole_red?
    expose_names
    have heqa := RedSpineNorm.complete (by assumption)
    have h_dec := hrt.max_hole_preserved
    simp_all [max_hole]
  /-case quot =>
    unfold view_app_hole?
    expose_names
    have heqa := RedSpineNorm.complete (by assumption)
    grind-/

/-
Show that if Hole hole₁ for the domain, then (ViewAppHole f hole₁ → False) implies there is no possible head step reduction.
This will be useful for funext proof because then f = g by congrFun.

In the other cases, when we readback ViewAppHole, we condense each of the gluing steps and induct by canonicalizing all points.
e.g., Id(A) ∘' Id(A).
-/

--#check ViewAppHole.complete

/-def ViewAppHole.complete (h : ViewAppHole (τ_c := τ_c) f hole₁ lv hlt mem) : view_app_hole? f hole₁ lv hlt mem = .some h := by
  unfold view_app_hole?
  induction h
  /-case quot =>
    expose_names
    split
    case h_1 hrt heq₁ =>
      have heq₂ := a.complete.symm.trans heq₁
      cases heq₂
      simp [hn]
    case h_2 heq =>
      have h := a.complete.symm.trans heq
      simp at h-/
  case id | quot =>
    expose_names
    have heqa := RedSpineNorm.complete (by assumption)
    grind
  case comp =>
    expose_names
    have heqa := RedSpineNorm.complete (by assumption)
    grind-/
  

end GenericExpr
