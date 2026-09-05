import Dcc.Eta.Nbe2.RedSpine
import Dcc.Eta.Nbe2.Hole
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
  | quot   : (hrt : RedSpineNorm (DCC? (f hole₁)) x')
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
  | eql   : (hrt : RedSpineNorm (DCC? (Eql(B) &(x) &(y))) (DCC? y = y))
    → (hgt : ¬ (DCC? y = y).max_hole < lv)
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

@[grind unfold, dcc_force_reduce]
def RedSpineNorm.fst_hole (hrt : RedSpineNorm (DCC? (Fst(B) hole₁)) e') : Σ' B x y, hole₁ = DCC? ⟦B⟧(x, y) := by
  cases hole₁
  case mkc =>
    exact ⟨_, _, _, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun _ hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def RedSpineNorm.snd_hole (hrt : RedSpineNorm (DCC? (Snd(B) hole₁)) e') : Σ' B x y, hole₁ = DCC? ⟦B⟧(x, y) := by
  cases hole₁
  case mkc =>
    exact ⟨_, _, _, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun _ hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def RedSpineNorm.eval_hole (hrt : RedSpineNorm (DCC? (Eval(A, B, x) hole₁)) e') : Σ' B x y, hole₁ = DCC? ⟦B⟧(x, y) := by
  cases hole₁
  case mkc =>
    exact ⟨_, _, _, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun _ hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def RedSpineNorm.pair_hole (hrt : RedSpineNorm (DCC? (⟦B⟧⟨x, y⟩ hole₁)) e') : Σ' y, hole₁ = DCC? &(y) := by
  cases hole₁
  case box =>
    exact ⟨_, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun _ hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def RedSpineNorm.map_hole (hrt : RedSpineNorm (DCC? (!<x> hole₁)) e') : Σ' y, hole₁ = DCC? &(y) := by
  cases hole₁
  case box =>
    exact ⟨_, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun _ hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def RedSpineNorm.unmap_hole (hrt : RedSpineNorm (DCC? (*<x> hole₁)) e') : Σ' y, hole₁ = DCC? &(y) := by
  cases hole₁
  case box =>
    exact ⟨_, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun _ hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def RedSpineNorm.fmap_hole (hrt : RedSpineNorm (DCC? ($<x> hole₁)) e') : Σ' y, hole₁ = DCC? &(y) := by
  cases hole₁
  case box =>
    exact ⟨_, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun _ hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def RedSpineNorm.curr'_hole (hrt : RedSpineNorm (DCC? (!Λ(A, B, x) y hole₁)) e') : Σ y' z, (PLift (y = (DCC? &(y')))) × (PLift (hole₁ = DCC? &(z))) := by
  cases hole₁
  case box =>
    cases y
    case box =>
      exact ⟨_, _, ⟨rfl⟩, ⟨rfl⟩⟩
    all_goals (exact (hrt.elim_norm_flse (fun _ hr hn => nomatch hn)).elim)
  all_goals (exact (hrt.elim_norm_flse (fun _ hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def RedSpineNorm.eql_hole (hrt : RedSpineNorm (DCC? (Eql(B) x hole₁)) e') : Σ' x' y, (PLift (x = (DCC? &(x')))) × (PLift (hole₁ = DCC? &(y))) := by
  cases hole₁
  case box =>
    cases x
    case box =>
      exact ⟨_, _, ⟨rfl⟩, ⟨rfl⟩⟩
    all_goals (exact (hrt.elim_norm_flse (fun _ hr hn => nomatch hn)).elim)
  all_goals (exact (hrt.elim_norm_flse (fun _ hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def RedSpineNorm.parapp_elim (hrt : RedSpineNorm (DCC? (f y z)) e') : (Σ' A B x, f = (DCC? Λ(A, B, x))) ⊕ (Σ' A B x, f = (DCC? !Λ(A, B, x))) ⊕ (Σ' B, f = DCC? Eql(B)) := by
  cases f
  case curr =>
    exact .inl ⟨_, _, _, rfl⟩
  case curr' =>
    exact .inr (.inl ⟨_, _, _, rfl⟩)
  case eql =>
    exact .inr (.inr ⟨_, rfl⟩)
  all_goals (exact (hrt.elim_norm_flse (fun _ hr hn => nomatch hn)).elim)

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
        | ⟨B, x, y, heq₀⟩ =>
          if heq : e' = x then by
            subst heq₀
            subst heq
            exact .some (.fst hrt hn' hrt.head_eq)
          else .none
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
            let heq' := hrt.unique ⟨.single .eql .eql, fun _ _ h => nomatch h⟩
            exact .some (.eql (heq' ▸ hrt) (heq' ▸ hn') (heq' ▸ hrt).head_eq)
  | .none => .none

def ViewAppHole.complete_some (h : ViewAppHole (τ_c := τ_c) f hole₁ lv hlt mem) : (view_app_hole? f hole₁ lv hlt mem).isSome := by
  induction h
  case quot | id | comp | comp' | comp₂ =>
    unfold view_app_hole?
    expose_names
    have heqa := RedSpineNorm.complete (by assumption)
    have h_dec := RedSpineNorm.max_hole_preserved (by assumption)
    simp_all [max_hole]
    try (aesop)
  case fst | snd | eval | curr | eql | pair | unmap | fmap | map | sigma =>
    unfold view_app_hole?
    expose_names
    have heqa := RedSpineNorm.complete (by assumption)
    have h_dec := RedSpineNorm.max_hole_preserved (by assumption)
    simp [heqa, hgt]
    grind
  case curr' =>
    unfold view_app_hole?
    expose_names
    have heqa := RedSpineNorm.complete (by assumption)
    have h_dec := RedSpineNorm.max_hole_preserved (by assumption)
    simp [heqa, hgt]
    clear a
    simp_all [RedSpineNorm.parapp_elim, RedSpineNorm.curr'_hole]
    aesop

#check ViewAppHole.complete_some

def ViewAppHole.eq (h₁ h₂ : ViewAppHole f hole₁ lv hlt mem) : h₁ = h₂ := by
  induction h₁
  any_goals (
    focus
    try (
      cases h₂ <;> (
        expose_names
        cases hrt.unique hrt_1
        cases hrt.eq hrt_1
        first | (grind) | (aesop))))

def ViewAppHole.complete (h : ViewAppHole (τ_c := τ_c) f hole₁ lv hlt mem) : view_app_hole? f hole₁ lv hlt mem = .some h := by
  have h_some := h.complete_some
  have heq := h.eq ((view_app_hole? f hole₁ lv hlt mem).get h_some)
  grind

#check ViewAppHole.complete

def view_app_hole_none_complete (hn : ViewAppHole (τ_c := τ_c) f hole₁ lv hlt mem → False) : view_app_hole? f hole₁ lv hlt mem = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro h heq
  exact hn h

inductive Domain : GenericExpr τ_c → GenericExpr τ_c → Type u
  | mk : RedAffNorm (DCC? Dom(x)) ⟨τ, hn_τ⟩ → Domain x τ
deriving Repr

@[grind ., grind →]
theorem RedAff.dom_decreasing (h : RedAff (DCC? Dom(x)) τ) (hneq : ∀ ⦃y⦄, τ ≠ (DCC? Dom(y))) : τ.size < x.size := by
  cases h
  any_goals (grind)

theorem RedAff.IsHead.spine_dom_decreasing (hr : RedAff (DCC? (f x)) B) (hn : hr.IsHead) (h_dom : RedAff (DCC? Dom(f)) τ) : τ.size < f.size := by
  cases hn <;> grind

theorem RedAff.IsHead.spine_dom_decreasing' (hr : RedAff (DCC? (f x)) B) (hn : hr.IsHead) (h_dom : Domain f τ) : τ.size < f.size :=
  match h_dom with
  | ⟨⟨hr', hn'⟩⟩ =>
    match hr'.cases_head with
    | .inl h => by
      cases h
      cases hn
      any_goals (exact (hn' ⟨_, (by constructor)⟩).elim)
    | .inr ⟨_, h₁, h₂⟩ => by
      have h := hn.spine_dom_decreasing hr h₁
      have h_dec' := h₁.decreasing
      grind

theorem RedSpinePlus.dom_decreasing (hr : RedSpinePlus (DCC? (f x)) B) (h_dom : Domain f τ) : τ.size < f.size :=
  match hr with
  | .single hr hn => hn.spine_dom_decreasing' hr h_dom
  | .head hr hn _hrt => hn.spine_dom_decreasing' hr h_dom

theorem RedSpineNorm.dom_decreasing (hr : RedSpineNorm (DCC? (f x)) B) (h_dom : Domain f τ) : τ.size < f.size :=
  match hr with
  | ⟨hr, _⟩ => hr.dom_decreasing h_dom

def Domain.decreasing_neq (h : Domain x τ) (hneq : ∀ ⦃y⦄, τ ≠ (DCC? Dom(y))) : τ.size < x.size :=
  match h with
  | ⟨⟨hr, hn⟩⟩ => by
    match hr.cases_head with
    | .inl h => grind
    | .inr ⟨_, h₁, h₂⟩ => grind

def Domain.is_norm (h : Domain α τ) : IsNorm RedAff τ :=
  match h with
  | ⟨_, hn⟩ => hn

def domain (e : GenericExpr τ_c) : ((τ : GenericExpr τ_c) × Domain e τ) :=
  ⟨_, ⟨aff_sound' (DCC? Dom(e))⟩⟩

def Domain.complete (h : Domain e τ) : domain e = ⟨τ, h⟩ :=
  match h with
  | ⟨hr⟩ => by
    have h := (hr.out_eq ▸ hr).eq
    simp [domain]
    grind

def Domain.complete_fst (h : Domain e τ) : (domain e).fst = τ := by
  have h := h.complete
  grind

@[dcc_rel]
def ViewAppHole.reduction (h : ViewAppHole f x lv hlt hmem) : Σ B, RedSpineNorm (DCC? (f x)) B := by
  cases h <;> exact ⟨_, by assumption⟩

/-
If a function is well-typed, it has some spine reduction on the hole
-/

def Domain.has_spine_hole_red (h_dom : Domain (τ_c := τ_c) f α) (hneq : α ≠ (DCC? Dom(τ))) (e_h : Hole α f.max_hole.succ x) : Σ' B, RedSpineNorm (DCC? (f x)) B := by
  sorry

/-
If a function is not well-typed, it has no spine reduction.
-/
def no_dom_no_spine_red (h_dom : Domain (τ_c := τ_c) f (DCC? Dom(τ))) (e_h : Hole α f.max_hole.succ x) : NormHead (DCC? (f x)) := by sorry

/-
view_app_hole? always fires when there is a spine reduction and this is a hole for the function.
-/
def Domain.app_hole_some (h_dom : Domain (τ_c := τ_c) f α) (e_h : Hole α f.max_hole.succ x) (hr : RedSpineNorm (DCC? (f x)) B) : (f.view_app_hole? x f.max_hole.succ (by grind) e_h.max_hole).isSome := by
  
  sorry

/-
ViewAppHole cases that can be condensed to a single combinator

ReadbackHead should always have size ≤ f since Domain.size <
and x' <
-/
inductive ReadbackHead : (f : GenericExpr τ_c) → (h_dom : Domain f A) → (e_h : Hole A f.max_hole.succ x)
  → (hrt : ViewAppHole f x f.max_hole.succ (by grind) e_h.max_hole)
  → (f' : GenericExpr τ_c) → Type u
  | id  {h_dom : Domain f A} {e_h : Hole A f.max_hole.succ x}
    {hrt : ViewAppHole f x f.max_hole.succ (by grind) e_h.max_hole} :
    (heq : hrt.reduction.fst = x) → ReadbackHead f h_dom e_h hrt (DCC? Id(A))
  | fst {h_dom : Domain f (DCC? Coup(B))} {e_h : Hole (DCC? Coup(B)) f.max_hole.succ (DCC? ⟦_B⟧(x, y))}
    {hrt : ViewAppHole f (DCC? ⟦_B⟧(x, y)) f.max_hole.succ (by grind) e_h.max_hole} :
    (heq : hrt.reduction.fst = x) → ReadbackHead f h_dom e_h hrt (DCC? Fst(B))
  | snd {h_dom : Domain f (DCC? Coup(B))} {e_h : Hole (DCC? Coup(B)) f.max_hole.succ (DCC? ⟦_B⟧(x, y))}
    {hrt : ViewAppHole f (DCC? ⟦_B⟧(x, y)) f.max_hole.succ (by grind) e_h.max_hole} :
    (heq : hrt.reduction.fst = y) → ReadbackHead f h_dom e_h hrt (DCC? Snd(B))
  | quot {h_dom : Domain f A} {e_h : Hole A f.max_hole.succ x}
    {hrt : ViewAppHole f x f.max_hole.succ (by grind) e_h.max_hole} :
    (heq : hrt = .quot (x' := x') hred hlt) → ReadbackHead f h_dom e_h hrt (DCC? `(A, x'))

/-
Termination argument is straightforward in Canonicalize since we're only recursion on comp or curr
-/

theorem Domain.decreasing (h : ViewAppHole f x lv hlt hmem) (h_dom : Domain f A) : A.size < f.size := by
  cases h <;> exact RedSpineNorm.dom_decreasing (by assumption) (by assumption)

def ViewAppHole.readback_head? {f : GenericExpr τ_c} (h_dom : Domain f A) (e_h : Hole A f.max_hole.succ x) (hrt : ViewAppHole f x f.max_hole.succ (by grind) e_h.max_hole) : Option (Σ' f', ReadbackHead f h_dom e_h hrt f') :=
  match hrt with
  | .quot _ _ => .some ⟨_, .quot rfl⟩
  | hrt =>
    if heq : hrt.reduction.fst = x then
      .some ⟨_, .id heq⟩
    else
      match A with
      | DCC? Coup(_B) =>
        match x with
        | DCC? ⟦__B⟧(x, y) =>
          have _hneq : x ≠ y := e_h.coup_points_neq
          if heq : hrt.reduction.fst = x then
            .some ⟨_, .fst heq⟩
          else if heq : hrt.reduction.fst = y then
            .some ⟨_, .snd heq⟩
          else .none
        | _ => .none
      | _ => .none

def ViewAppHole.quot_nmem {e_h : Hole A (max_hole f).succ x} (hv : ViewAppHole f x f.max_hole.succ (by grind) e_h.max_hole)
  (hrt : RedSpineNorm (DCC? (f x)) e') (_heq : hv = .quot hrt hlt) : e'.max_hole < x.min_hole := by
  have h := e_h.min_hole
  grind

/-
Quot at least
-/

/-
f contains the constant x in some way
-/
def RedSpineNorm.quot_size_at_least (hrt : RedSpineNorm (DCC? (f x)) x') (h_size_hole : x.size = 0) : Σ' m, f.size = x'.size + m := by
  have h_dec := hrt.decreasing
  exact ⟨f.size - x'.size, by grind⟩


def ReadbackHead.complete {f : GenericExpr τ_c} {h_dom : Domain f A} {e_h : Hole A f.max_hole.succ x}
  {hrt : ViewAppHole f x f.max_hole.succ (by grind) e_h.max_hole}
  (h : ReadbackHead (τ_c := τ_c) f h_dom e_h hrt f') : hrt.readback_head? h_dom e_h = .some ⟨f', h⟩ := by
  induction heq₀ : h
  · unfold ViewAppHole.readback_head?
    split
    case h_1 heq =>
      simp [ViewAppHole.reduction] at heq
      grind
    · aesop
  · unfold ViewAppHole.readback_head?
    expose_names
    split
    case h_1 hrt' hn' =>
      have h := ViewAppHole.quot_nmem (ViewAppHole.quot hrt' hn') hrt' (by rfl) (A := B.coup) (e_h := e_h_1)
      have heq₁ := hrt'.complete
      simp [ViewAppHole.reduction] at heq
      cases heq
      cases heq₀
      grind
    case h_2 =>
      simp [heq]
      intro h
      cases h
  · unfold ViewAppHole.readback_head?
    expose_names
    split
    case h_1 hrt' hn' =>
      have h := ViewAppHole.quot_nmem (ViewAppHole.quot hrt' hn') hrt' (by rfl) (A := B.coup) (e_h := e_h_1)
      have heq₁ := hrt'.complete
      simp [ViewAppHole.reduction] at heq
      cases heq
      cases heq₀
      grind
    case h_2 =>
      have hneq : y ≠ _B.mkc x_1 y := fun h => nomatch h
      simp [heq, hneq]
      exact e_h_1.coup_points_neq.symm
  · unfold ViewAppHole.readback_head?
    expose_names
    subst heq
    simp

def ReadbackHead.preservation {f x f' A : GenericExpr τ_c} {h_dom : Domain f A} {e_h : Hole A f.max_hole.succ x} {hrt : ViewAppHole f x f.max_hole.succ (by grind) e_h.max_hole}
  (h : ReadbackHead f h_dom e_h hrt f') : Domain f' A := by
  have hn := h_dom.is_norm
  cases h with
  | quot | id =>
    exact ⟨⟨.single (by constructor), by assumption⟩⟩
  | fst | snd =>
    cases e_h with
    | coup => exact ⟨⟨.single (by constructor), by assumption⟩⟩

@[grind ., grind →]
theorem RedAff.domain_max_hole_preserved (h : RedAff (DCC? Dom(x)) τ) : τ.max_hole ≤ x.max_hole := by
  cases h <;> grind

theorem RedSpinePlus.domain_max_hole_preserved (h : RedSpinePlus (DCC? Dom(x)) τ) : τ.max_hole ≤ x.max_hole := by
  cases h <;> grind

theorem RedSpineNorm.domain_max_hole_preserved (h : RedSpineNorm (DCC? Dom(x)) τ) : τ.max_hole ≤ x.max_hole :=
  match h with
  | ⟨hr, _⟩ => hr.domain_max_hole_preserved

@[grind ., grind →]
theorem RedAffReflTrans.max_hole_preserved (h : RedAffReflTrans A B) : B.max_hole ≤ A.max_hole :=
  match h.cases_head with
  | .inl h => by grind
  | .inr ⟨_, h₁, h₂⟩ => by
    have h_dec := h₁.decreasing
    have h_dec₂ := h₁.max_hole_preserved
    have h_dec₃ := max_hole_preserved h₂
    grind
termination_by A.size

theorem Domain.max_hole_preserved (h : Domain x A) : A.max_hole ≤ x.max_hole :=
  match h with
  | ⟨⟨hr, _hn⟩⟩ => hr.max_hole_preserved

def ReadbackHead.max_hole_preserved {f f' A : GenericExpr τ_c} {h_dom : Domain f A} {e_h : Hole A f.max_hole.succ x}
  {hrt : f.ViewAppHole x f.max_hole.succ (by grind) e_h.max_hole}
  (h : ReadbackHead f h_dom e_h hrt f') : f'.max_hole ≤ f.max_hole := by
  have h_dec := h_dom.max_hole_preserved
  cases h <;> grind

def ReadbackHead.preservation_view {f f' A : GenericExpr τ_c} {h_dom : Domain f A} {e_h : Hole A f.max_hole.succ x}
  {hrt : f.ViewAppHole x f.max_hole.succ (by grind) e_h.max_hole}
  (h : ReadbackHead f h_dom e_h hrt f') : f'.ViewAppHole x f'.max_hole.succ
  (by grind)
  (by have ha := h.max_hole_preserved; have hb := e_h.max_hole; grind) := by
  have ha := h.max_hole_preserved
  have hb := e_h.max_hole
  have hc := e_h.min_hole
  cases h with
  | id heq =>
    have heq' : hrt.reduction = ⟨hrt.reduction.fst, hrt.reduction.snd⟩ := rfl
    apply ViewAppHole.id (hrt := ⟨.single .id .id, e_h.is_norm.to_head⟩)
    simp [RedSpineNorm.head]
  | fst heq =>
    have heq' : hrt.reduction = ⟨hrt.reduction.fst, hrt.reduction.snd⟩ := rfl
    expose_names
    apply ViewAppHole.fst (hrt := ⟨.single .fstc .fstc, e_h.is_norm.sigl.to_head⟩) (lv := B.fstc.max_hole.succ) (hgt := by grind)
    simp [RedSpineNorm.head]
  | snd heq =>
    have heq' : hrt.reduction = ⟨hrt.reduction.fst, hrt.reduction.snd⟩ := rfl
    expose_names
    apply ViewAppHole.snd (hrt := ⟨.single .sndc .sndc, e_h.is_norm.sigr.to_head⟩) (lv := B.sndc.max_hole.succ) (hgt := by grind)
    simp [RedSpineNorm.head]
  | quot heq =>
    have heq' : hrt.reduction = ⟨hrt.reduction.fst, hrt.reduction.snd⟩ := rfl
    apply ViewAppHole.quot (hrt := ⟨.single .quot .quot, by rename_i hred; exact hred.is_norm⟩)
    · grind

/-
When ViewAppHole reduces to part of the hole, we have reached a normal form.
So reduce these to the canonical projection, quotation, or Id.

Otherwise, the expression is "gluing" operations together in some way that does
meaningful work.

Always reduce all the points of the expression.

Decreasing argument goes by the length of the reduction in ViewAppHole

We do not assume f is in normal form. That is assumed in later proofs since defeq β-normalizes first.

Simply continue running Canonicalize until the size doesn't decrease.
-/
inductive Canonicalize : (f : GenericExpr τ_c) → (f' : GenericExpr τ_c) → Type u
  /-
    Make this a global refl case so there is a decreasing argument for Canonicalize
    Should be no issue with stopping halfway due to ViewAppHole
    | par    : (h_dom : Domain f A)
    → (e_h : Hole A f.max_hole.succ x)
    → (hn  : ∀ ⦃hlt⦄ ⦃hmem⦄, ViewAppHole f x f.max_hole.succ hlt hmem → False)
    → Canonicalize f f-/
  | comp   : (h_dom : Domain (DCC? f ∘ g) A)
    → (e_h  : Hole A (DCC? f ∘ g).max_hole.succ x)
    → (hrt  : ViewAppHole (DCC? f ∘ g) x (DCC? (f ∘ g)).max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? f ∘ g) h_dom e_h hrt f' → False)
    → (hc₁  : Canonicalize f f')
    → (hc₂  : Canonicalize g g')
    → Canonicalize (DCC? f ∘ g) (DCC? f' ∘ g')
  /-
    MASSIVE TODO: merge ∘ ∘' and ∘∘ in Judge because they all have the same domain
    and are all of very similar shape.
    Can merge the constructor in Judge. We are coercing them to the same for now,
    but as long as Judge is changed this is legal.
  -/
  | comp'  : (h_dom : Domain (DCC? f ∘' g) A)
    → (e_h  : Hole A (DCC? f ∘' g).max_hole.succ x)
    → (hrt  : ViewAppHole (DCC? f ∘' g) x (DCC? (f ∘ g)).max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? f ∘' g) h_dom e_h hrt f' → False)
    → (hc₁  : Canonicalize f f')
    → (hc₂  : Canonicalize g g') -- size of ∘' and ∘ is the same
    → Canonicalize (DCC? f ∘' g) (DCC? f' ∘ g')
  | comp₂  : (h_dom : Domain (DCC? f ∘∘ g) A)
    → (e_h  : Hole A (DCC? f ∘∘ g).max_hole.succ x)
    → (hrt  : ViewAppHole (DCC? f ∘∘ g) x (DCC? (f ∘∘ g)).max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? f ∘∘ g) h_dom e_h hrt f' → False)
    → (hc₁  : Canonicalize f f')
    → (hc₂  : Canonicalize g g') -- size of ∘' and ∘ is the same
    → Canonicalize (DCC? f ∘∘ g) (DCC? f' ∘ g')
  | eval   : (h_dom : Domain (DCC? Eval(A, B, x)) τ)
    → (e_h : Hole τ (DCC? Eval(A, B, x)).max_hole.succ y)
    → (hrt : ViewAppHole (DCC? Eval(A, B, x)) y (DCC? Eval(A, B, x)).max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? Eval(A, B, x)) h_dom e_h hrt f' → False)
    → (hc₁ : Canonicalize B B')
    → (hc₂ : Canonicalize x x')
    → Canonicalize (DCC? Eval(A, B, x)) (DCC? Eval(A, B', x'))
  | curr   : (h_dom : Domain (DCC? (Λ(A, B, x) y)) τ)
    → (e_h : Hole τ (DCC? (Λ(A, B, x) y)).max_hole.succ z)
    → (hrt : ViewAppHole (DCC? (Λ(A, B, x) y)) z (DCC? (Λ(A, B, x) y)).max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? (Λ(A, B, x) y)) h_dom e_h hrt f' → False)
    → (hc₁ : Canonicalize B B')
    → (hc₂ : Canonicalize x x')
    → Canonicalize (DCC? (Λ(A, B, x) y)) (DCC? (Λ(A, B', x') y))
  | curr'  : (h_dom : Domain (DCC? (!Λ(A, B, x) &(y))) τ)
    → (e_h : Hole τ (DCC? (!Λ(A, B, x) &(y))).max_hole.succ z)
    → (hrt : ViewAppHole (DCC? (!Λ(A, B, x) &(y))) z (DCC? (!Λ(A, B, x) &(y))).max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? (!Λ(A, B, x) &(y))) h_dom e_h hrt f' → False)
    → (hc₁ : Canonicalize B B')
    → (hc₂ : Canonicalize x x')
    → Canonicalize (DCC? (!Λ(A, B, x) &(y))) (DCC? (!Λ(A, B', x') &(y)))
  | eql    : (h_dom : Domain (DCC? (Eql(B) &(x))) τ)
    → (e_h : Hole τ (DCC? (Eql(B) &(x))).max_hole.succ y)
    → (hrt : ViewAppHole (DCC? (Eql(B) &(x))) y (DCC? (Eql(B) &(x))).max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? (Eql(B) &(x))) h_dom e_h hrt f' → False)
    → (hc₂ : Canonicalize B B')
    → Canonicalize (DCC? (Eql(B) &(x))) (DCC? (Eql(B') &(x)))
  | pair   : (h_dom : Domain (DCC? ⟦B⟧⟨x, y⟩) τ)
    → (e_h : Hole τ (DCC? ⟦B⟧⟨x, y⟩).max_hole.succ z)
    → (hrt : ViewAppHole (DCC? ⟦B⟧⟨x, y⟩) z (DCC? ⟦B⟧⟨x, y⟩).max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? ⟦B⟧⟨x, y⟩) h_dom e_h hrt f' → False)
    → (hc₁ : Canonicalize B B')
    → (hc₂ : Canonicalize x x')
    → (hc₃ : Canonicalize y y')
    → Canonicalize (DCC? ⟦B⟧⟨x, y⟩) (DCC? ⟦B'⟧⟨x', y'⟩)
  | unmap  : (h_dom : Domain (DCC? *<x>) τ)
    → (e_h : Hole τ (DCC? *<x>).max_hole.succ y)
    → (hrt : ViewAppHole (DCC? *<x>) y (DCC? *<x>).max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? *<x>) h_dom e_h hrt f' → False)
    → (hc₁ : Canonicalize x x')
    → Canonicalize (DCC? *<x>) (DCC? *<x'>)
  | fmap   : (h_dom : Domain (DCC? $<x>) τ)
    → (e_h : Hole τ (DCC? $<x>).max_hole.succ y)
    → (hrt : ViewAppHole (DCC? $<x>) y (DCC? $<x>).max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? $<x>) h_dom e_h hrt f' → False)
    → (hc₁ : Canonicalize x x')
    → Canonicalize (DCC? $<x>) (DCC? $<x'>)
  | map    : (h_dom : Domain (DCC? !<x>) τ)
    → (e_h : Hole τ (DCC? !<x>).max_hole.succ y)
    → (hrt : ViewAppHole (DCC? !<x>) y (DCC? !<x>).max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? !<x>) h_dom e_h hrt f' → False)
    → (hc₁ : Canonicalize x x')
    → Canonicalize (DCC? !<x>) (DCC? !<x'>)
  | sigma  : (h_dom : Domain (DCC? Σ(B, C)) τ)
    → (e_h : Hole τ (DCC? Σ(B, C)).max_hole.succ x)
    → (hrt : ViewAppHole (DCC? Σ(B, C)) x (DCC? Σ(B, C)).max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? Σ(B, C)) h_dom e_h hrt f' → False)
    → (hc₁ : Canonicalize B B')
    → (hc₂ : Canonicalize C C')
    → Canonicalize (DCC? Σ(B, C)) (DCC? Σ(B', C'))
  | single : (h_dom : Domain f A)
    → (e_h  : Hole A f.max_hole.succ x)
    → (hrt  : ViewAppHole f x f.max_hole.succ (by grind) e_h.max_hole)
    → (hrb  : ReadbackHead f h_dom e_h hrt f')
    → Canonicalize f f'

def canonicalize (f : GenericExpr τ_c) : Option ((f' : GenericExpr τ_c) × Canonicalize f f') :=
  let ⟨A, h_dom⟩ := f.domain
  let ⟨x, e_h⟩ := mk_hole A f.max_hole.succ
  match f.view_app_hole? x f.max_hole.succ (by grind) e_h.max_hole with
  | .some hrt =>
    match heq : hrt.readback_head? h_dom e_h with
    | .some ⟨f', hrb⟩ => .some ⟨_, .single h_dom e_h hrt hrb⟩
    | .none =>
      have hn_hrb : ∀ ⦃f'⦄, ReadbackHead f h_dom e_h hrt f' → False := by
        intro f' h
        simp_all [h.complete]
      match heq₂ : f with
      | (DCC? f ∘ g) =>
        match f.canonicalize, g.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .comp h_dom e_h hrt hn_hrb h₁ h₂⟩
        | _, _ => .none
      | (DCC? f ∘' g) =>
        match f.canonicalize, g.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .comp' h_dom e_h hrt hn_hrb h₁ h₂⟩
        | _, _ => .none
      | (DCC? f ∘∘ g) =>
        match f.canonicalize, g.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .comp₂ h_dom e_h hrt hn_hrb h₁ h₂⟩
        | _, _ => .none
      | DCC? Eval(A, B, f) =>
        match B.canonicalize, f.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .eval h_dom e_h hrt hn_hrb h₁ h₂⟩
        | _, _ => .none
      | DCC? (Λ(A, B, f) env) =>
        match B.canonicalize, f.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .curr h_dom e_h hrt hn_hrb h₁ h₂⟩
        | _, _ => .none
      | DCC? (!Λ(A, B, f) &(env)) =>
        match B.canonicalize, f.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .curr' h_dom e_h hrt hn_hrb h₁ h₂⟩
        | _, _ => .none
      | DCC? (Eql(B) &(env)) =>
        match B.canonicalize with
        | .some ⟨_, h₁⟩ => by
          subst heq₂
          exact .some ⟨_, .eql h_dom e_h hrt hn_hrb h₁⟩
        | .none => .none
      | DCC? ⟦B⟧⟨a, b⟩ =>
        match B.canonicalize with
        | .some ⟨_, h₁⟩ =>
          match a.canonicalize, b.canonicalize with
          | .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ => by
            subst heq₂
            exact .some ⟨_, .pair h_dom e_h hrt hn_hrb h₁ h₂ h₃⟩
          | _, _ => .none
        | .none => .none
      | DCC? *<x> =>
        match x.canonicalize with
        | .some ⟨_, h₁⟩ => by
          subst heq₂
          exact .some ⟨_, .unmap h_dom e_h hrt hn_hrb h₁⟩
        | .none => .none
      | DCC? $<x> =>
        match x.canonicalize with
        | .some ⟨_, h₁⟩ => by
          subst heq₂
          exact .some ⟨_, .fmap h_dom e_h hrt hn_hrb h₁⟩
        | .none => .none
      | DCC? !<x> =>
        match x.canonicalize with
        | .some ⟨_, h₁⟩ => by
          subst heq₂
          exact .some ⟨_, .map h_dom e_h hrt hn_hrb h₁⟩
        | .none => .none
      | DCC? Σ(B, C) =>
        match B.canonicalize, C.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .sigma h_dom e_h hrt hn_hrb h₁ h₂⟩
        | _, _ => .none
      | _ => .none
  | .none => .none

def readback_head_none_complete {f x : GenericExpr τ_c} {h_dom : Domain f A} {e_h : Hole A f.max_hole.succ x} {hrt : f.ViewAppHole x f.max_hole.succ (by grind) e_h.max_hole}
  (hn : ∀ ⦃f'⦄, ReadbackHead f h_dom e_h hrt f' → False) : ViewAppHole.readback_head? h_dom e_h hrt = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro h
  exact (hn h.snd).elim

def Canonicalize.complete (h : Canonicalize (τ_c := τ_c) f f') : f.canonicalize = .some ⟨f', h⟩ := by
  induction h <;> (
    try (have ha := readback_head_none_complete (by assumption))
    try (have haa := ReadbackHead.complete (by assumption))
    have hb := Hole.complete (by assumption)
    have hc := ViewAppHole.complete (by assumption)
    have hd := Domain.complete (by assumption)
    have he := Domain.complete_fst (by assumption)
    unfold canonicalize
    grind)

/-
TODO: comp' vs comp vs comp₂ can be condensed to the same judgment rule,
so we assume η-reduce to ∘.

Id(A) ∘ Id(A) handled by id
So ∘ is doing some work here.

For single-step cases, i.e., the normal form is reached in one-step, η-reduce to that.
-/

end GenericExpr
