import Dcc.Eta.Nbe2.RedSpine
import Dcc.Eta.Nbe2.Hole
import Dcc.Eta.Nbe2.Domain
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

/-
To η-reduce a function, track movement of the hole through the function.

"Optimize" the function by looking for any steps that can be removed.
These are steps where ViewAppHole is a no-op on the hole.

ViewAppHole characterizes a spine-reduction on a Hole to normal form.

Funext is forced by η-reducing two expressions that perform the same
"work" on a hole to the same thing.

Is (f x) = (g x), where f x -> B and g x -> B, then (f x) and (g x) either perform work or perform
no work by reflexivity or congruence.

If (f x) -> f' x and (g x) -> g' x, then f' = g' by (f x) = (g x).

If f or g perform meaningful work, then there must be a spine reduction.
An example of a spine reduction is Id(A) x = x. An actual rewriting of the
term occurrs and the hole changes places.

  Possible spine reduction single-steps are listed in RedSpine.lean.
  Spine reductions can either collapse the entire reduction to a canonical form, or perform meaningful "gluing" of work.
    - Id(A) ∘ Id(A) collapses to Id(A)
    - All collapsed reductions are listed in ReadbackHead. Funext is proved for this.
  If the spine reduction sequence contains meaningful "gluing," Canonicalize recurses on the components.
    - (Id(Sort 1) ∘ Fst(Id(Sort 1))) ∘ (Id(Coup(Id(Sort 1))) ∘ Fst(`(Sort 1, Coup(Id(Sort 1)))))
      does not automatically collapse, since the sub-expressions have meaningful composition. Canonicalize recurses. We have not proven funext for this yet.
-/

namespace GenericExpr

open CasesHead
open MaxHolePreserved
open DomDecreasing

inductive ViewAppHole : (f : GenericExpr τ_c)
  → (hole₁ : GenericExpr τ_c)
  → (lv    : ℕ)
  → (hlt   : f.max_hole < lv)
  → (hmem  : lv ≤ hole₁.max_hole)
  → Type u
  | quot   : (hrt : DSL((f hole₁) →!wh⁺ x'))
    → (hn  : x'.max_hole < lv)
    → ViewAppHole f hole₁ lv hlt hmem
  -- par is not actually a case. this is the fallback that should hit if no ViewAppHole is present
  /-| par    : RedAffNorm (DCC? (f hole₁)) ⟨(DCC? (f' hole₁)), hn'⟩
    → (hlt : f.max_hole < hole₁.min_hole)
    → ViewAppHole f hole₁ hlt-/
  -- Note: this will need to recurse since we can't just blindly assume hole₁
  -- we just need to know the hole is in there somewhere could be f (g (h hole))
  -- if this does not fire, just do quot
  | comp   : (hrt : DSL(((f ∘ g) x) →!wh⁺ e'))
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : get_head hrt.raw = ⟨DCC? (f (g x)), ⟨.comp⟩, .comp⟩)
    → ViewAppHole g x lv (by simp_all [max_hole]) (by simp_all [max_hole])
    → ViewAppHole (DCC? (f ∘ g)) x lv hlt hmem
  /-
    Since we are weak-head reducing, and since
    the root expression should already be in normal form (NOTE TODO ENFORCE THIS),
    it doesn't matterh what RedSpineNorm reduces to
    just what the last step was
  -/
  | id     : (hrt : DSL((Id(A) x) →!wh⁺ x))
    → (hsp : get_head hrt.raw = ⟨x, ⟨.id⟩, .id⟩)
    → ViewAppHole (DCC? Id(A)) x lv hlt hmem
  | fst    : (hrt : DSL((Fst(B) ⟦_B⟧(x, y)) →!wh⁺ x))
    → (hgt : ¬ x.max_hole < lv)
    → (hsp : get_head hrt.raw = ⟨x, ⟨.fstc⟩, .fstc⟩)
    → ViewAppHole (DCC? Fst(B)) (DCC? ⟦_B⟧(x, y)) lv hlt hmem
  | snd    : (hrt : DSL((Snd(B) ⟦_B⟧(x, y)) →!wh⁺ y))
    → (hgt : ¬ y.max_hole < lv)
    → (hsp : get_head hrt.raw = ⟨y, ⟨.sndc⟩, .sndc⟩)
    → ViewAppHole (DCC? Snd(B)) (DCC? ⟦_B⟧(x, y)) lv hlt hmem
  -- Purpose of SpineNorm is to handle top-level weak head steps that produce further normal forms
  -- innere congruences, which are irrelevant, so we eliminate them by considering only WHNF reductions
  | eval    : (hrt : DSL((Eval(A, B, x) ⟦_B⟧(y, z)) →!wh⁺ e'))
    → (hgt  : ¬ e'.max_hole < lv)
    → (hsp  : get_head hrt.raw = ⟨DCC? (x y z), ⟨.evalc⟩, .eval⟩)
    → ViewAppHole (DCC? Eval(A, B, x)) (DCC? ⟦_B⟧(y, z)) lv hlt hmem
  | curr'  : (hrt : DSL((!Λ(A, B, x) &(y) &(z)) →!wh⁺ e'))
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : get_head hrt.raw = ⟨DCC? (x &(⟦B⟧(y, z))), ⟨.curr'⟩, .curr'⟩)
    → ViewAppHole x (DCC? &(⟦B⟧(y, z))) lv (by simp_all [max_hole]) (by simp_all [max_hole])
    → ViewAppHole (DCC? (!Λ(A, B, x) &(y))) (DCC? &(z)) lv hlt hmem
  | curr   : (hrt : DSL((Λ(A, B, x) y z) →!wh⁺ e'))
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : get_head hrt.raw = ⟨DCC? (x ⟦B⟧(y, z)), ⟨.curr⟩, .curr⟩)
    → ViewAppHole x (DCC? ⟦B⟧(y, z)) lv (by simp_all [max_hole]) (by simp_all [max_hole])
    → ViewAppHole (DCC? (Λ(A, B, x) y)) z lv hlt hmem
  | eql   : (hrt : DSL((Eql(B) &(x) &(y)) →!wh⁺ y = y))
    → (hgt : ¬ (DCC? y = y).max_hole < lv)
    → (hsp : get_head hrt.raw = ⟨DCC? (y = y), ⟨.eql⟩, .eql⟩)
    → ViewAppHole (DCC? (Eql(B) &(x))) (DCC? &(y)) lv hlt hmem
  /-
    Recursively canonicalize the points inside all combinators.
    This handles the inner congruences.

    BIG TODO
  -/
  | pair   : (hrt : DSL((⟦B⟧⟨x, y⟩ &(z)) →!wh⁺ e'))
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : get_head hrt.raw = ⟨DCC? ⟦(B z)⟧((x z), (y z (x z))), ⟨.pair⟩, .pair⟩)
    → ViewAppHole (DCC? ⟦B⟧⟨x, y⟩) (DCC? &(z)) lv hlt hmem
  | unbox  : (hrt : DSL((*(A) &(y)) →!wh⁺ y))
    → (hgt : ¬ y.max_hole < lv)
    → (hsp : get_head hrt.raw = ⟨y, ⟨.unbox⟩, .unbox⟩)
    → ViewAppHole (DCC? *(A)) (DCC? &(y)) lv hlt hmem
  | fmap  : (hrt : DSL(($<x> &(y)) →!wh⁺ e'))
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : get_head hrt.raw = ⟨DCC? &((x y)), ⟨.fmap⟩, .fmap⟩)
    → ViewAppHole (DCC? $<x>) (DCC? &(y)) lv hlt hmem
  | map   : (hrt : DSL((!<x> &(y)) →!wh⁺ e'))
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : get_head hrt.raw = ⟨DCC? !((x y)), ⟨.map⟩, .map⟩)
    → ViewAppHole (DCC? !<x>) (DCC? &(y)) lv hlt hmem
  -- if τ contains the hole, then this is Σ
  -- otherwise, the Coup does not depend on the hole
  -- in which case it is just `(
  | sigma    : (hrt : DSL((Σ(B, C) x) →!wh⁺ e'))
    → (hgt : ¬ e'.max_hole < lv)
    → (hsp : get_head hrt.raw = ⟨DCC? Coup((C x)), ⟨.sigma⟩, .sigma⟩)
    → ViewAppHole C x lv (by simp_all [max_hole]) (by simp_all [max_hole])
    → ViewAppHole (DCC? Σ(B, C)) x lv hlt hmem

theorem AndNorm.head_eq (h : DSL(A →!wh⁺ C)) (hr : RedHead A B := by exact ⟨⟨by constructor⟩, by constructor⟩) : get_head h.raw = ⟨B, hr⟩ := by
  unfold get_head
  split
  case h_1 hr' _ _ =>
    cases unique hr hr'
    congr!
    apply proof_eq
  case h_2 hr' hn' hrt' _ =>
    cases unique hr hr'
    congr!
    apply proof_eq

@[grind unfold, dcc_force_reduce]
def AndNorm.fst_hole (hrt : DSL((Fst(B) hole₁) →!wh⁺ e')) : Σ' B x y, hole₁ = DCC? ⟦B⟧(x, y) := by
  cases hole₁
  case mkc =>
    exact ⟨_, _, _, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def AndNorm.snd_hole (hrt : DSL((Snd(B) hole₁) →!wh⁺ e')) : Σ' B x y, hole₁ = DCC? ⟦B⟧(x, y) := by
  cases hole₁
  case mkc =>
    exact ⟨_, _, _, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def AndNorm.eval_hole (hrt : DSL((Eval(A, B, x) hole₁) →!wh⁺ e')) : Σ' B x y, hole₁ = DCC? ⟦B⟧(x, y) := by
  cases hole₁
  case mkc =>
    exact ⟨_, _, _, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def AndNorm.pair_hole (hrt : DSL((⟦B⟧⟨x, y⟩ hole₁) →!wh⁺ e')) : Σ' y, hole₁ = DCC? &(y) := by
  cases hole₁
  case box =>
    exact ⟨_, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def AndNorm.map_hole (hrt : DSL((!<x> hole₁) →!wh⁺ e')) : Σ' y, hole₁ = DCC? &(y) := by
  cases hole₁
  case box =>
    exact ⟨_, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def AndNorm.unbox_hole (hrt : DSL((*(A) hole₁) →!wh⁺ e')) : Σ' y, hole₁ = DCC? &(y) := by
  cases hole₁
  case box =>
    exact ⟨_, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def AndNorm.fmap_hole (hrt : DSL(($<x> hole₁) →!wh⁺ e')) : Σ' y, hole₁ = DCC? &(y) := by
  cases hole₁
  case box =>
    exact ⟨_, rfl⟩
  all_goals (exact (hrt.elim_norm_flse (fun hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def AndNorm.curr'_hole (hrt : DSL((!Λ(A, B, x) y hole₁) →!wh⁺ e')) : Σ y' z, (PLift (y = (DCC? &(y')))) × (PLift (hole₁ = DCC? &(z))) := by
  cases hole₁
  case box =>
    cases y
    case box =>
      exact ⟨_, _, ⟨rfl⟩, ⟨rfl⟩⟩
    all_goals (exact (hrt.elim_norm_flse (fun hr hn => nomatch hn)).elim)
  all_goals (exact (hrt.elim_norm_flse (fun hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def AndNorm.eql_hole (hrt : DSL((Eql(B) x hole₁) →!wh⁺ e')) : Σ' x' y, (PLift (x = (DCC? &(x')))) × (PLift (hole₁ = DCC? &(y))) := by
  cases hole₁
  case box =>
    cases x
    case box =>
      exact ⟨_, _, ⟨rfl⟩, ⟨rfl⟩⟩
    all_goals (exact (hrt.elim_norm_flse (fun hr hn => nomatch hn)).elim)
  all_goals (exact (hrt.elim_norm_flse (fun hr hn => nomatch hn)).elim)

@[grind unfold, dcc_force_reduce]
def AndNorm.parapp_elim (hrt : DSL((f y z) →!wh⁺ e')) : (Σ' A B x, f = (DCC? Λ(A, B, x))) ⊕ (Σ' A B x, f = (DCC? !Λ(A, B, x))) ⊕ (Σ' B, f = DCC? Eql(B)) := by
  cases f
  case curr =>
    exact .inl ⟨_, _, _, rfl⟩
  case curr' =>
    exact .inr (.inl ⟨_, _, _, rfl⟩)
  case eql =>
    exact .inr (.inr ⟨_, rfl⟩)
  all_goals (exact (hrt.elim_norm_flse (fun hr hn => nomatch hn)).elim)

theorem AndNorm.quot_no_mem (hrt : DSL((`(B, x) y) →!wh⁺ e')) (hlt : (DCC? `(B, x)).max_hole < lv) (hn : ¬ e'.max_hole < lv) (_hmem : lv ≤ y.max_hole) : e'.max_hole < lv := by
  match cases_head hrt.raw with
  | .inl ⟨hrt@⟨⟨hr⟩, hn⟩, heq⟩ =>
    have h_dec := max_hole_preserved hrt
    match hn with
    | .quot => grind
  | .inr ⟨_, hrt@⟨⟨hr⟩, hn⟩, hrt', heq⟩ =>
    match hn with
    | .quot =>
      have h_dec  := max_hole_preserved hrt
      have h_dec₂ := max_hole_preserved hrt'
      grind

theorem max_hole_points {e : GenericExpr τ} (n : ℕ) (hn : e.max_hole < lv) (hlt : n < e.point_arity := by first | grind | dcc_simp) : (e.points.get ⟨n, hlt⟩).max_hole < lv := by
  induction e
  any_goals (simp [point_arity] at hlt)
  any_goals (simp_all [points, Vector.get, max_hole])
  any_goals (grind)

theorem max_hole_points_app (n : ℕ) (hn : (DCC? (f x)).max_hole < lv) (hlt : n < f.point_arity := by grind) : (f.points.get ⟨n, hlt⟩).max_hole < lv := by
  simp [max_hole] at hn
  exact max_hole_points n hn.left

def view_app_hole? (f hole₁ : GenericExpr τ_c) (lv : ℕ) (hlt : f.max_hole < lv) (hmem : lv ≤ hole₁.max_hole) : Option (ViewAppHole f hole₁ lv hlt hmem) :=
  match run_norm_plus RedHead (DCC? (f hole₁)) with
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
      | DCC? *(A) =>
        match hrt.unbox_hole with
        | ⟨y, heq₀⟩ => by
          if heq : e' = y then
            subst heq₀
            subst heq
            exact .some (.unbox hrt hn' hrt.head_eq)
          else exact .none
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
      | DCC? &(_x) | DCC? Eql(_B) | DCC? !Λ(_A, _B, _x)  | DCC? Λ(_A, _B, _x) | DCC? Uncoup(_x) | DCC? Unbang(_x) | DCC? Dom(_x) | DCC? Sort _m | DCC? ∗ | DCC? ⊤ | DCC? ⊥
      | DCC? (_x = _y) | DCC? refl(_B) | DCC? ⟦_B⟧(_x, _y) | DCC? Coup(_B)
      | DCC? Π(_B, _C) | DCC? !(_A) | .const _n | .hole _n => False.elim (hrt.elim_norm_flse (fun hr hn => nomatch hn))
      | DCC? (a b) =>
        match hrt.parapp_elim with
        | .inl ⟨A, B, x, heq₀⟩ => by
          subst heq₀
          match x.view_app_hole? (DCC? ⟦B⟧(b, hole₁)) lv (max_hole_points_app 2 hlt) (by simp_all [max_hole]) with
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
            let heq' := unique hrt (AndNorm.mk (.single ⟨⟨.eql⟩, .eql⟩) (fun _ h => nomatch h))
            exact .some (.eql (heq' ▸ hrt) (heq' ▸ hn') (heq' ▸ hrt).head_eq)
  | .none => .none

def ViewAppHole.complete_some (h : ViewAppHole (τ_c := τ_c) f hole₁ lv hlt mem) : (view_app_hole? f hole₁ lv hlt mem).isSome := by
  induction h
  case quot | id | comp =>
    unfold view_app_hole?
    expose_names
    have heqa : run_norm_plus _ _ = _ := complete (M := Option) hrt
    have h_dec := max_hole_preserved (by assumption)
    simp_all [max_hole]
    try (aesop)
  case curr =>
    unfold view_app_hole?
    expose_names
    have heqa : run_norm_plus _ _ = _ := complete (M := Option) hrt
    have h_dec := max_hole_preserved (by assumption)
    simp [heqa, hgt, AndNorm.parapp_elim]
    split
    · simp
    · grind
  case fst | snd | eval | eql | pair | unbox | fmap | map | sigma =>
    unfold view_app_hole?
    expose_names
    have heqa : run_norm_plus _ _ = _ := complete (M := Option) (by assumption)
    have h_dec := max_hole_preserved (by assumption)
    simp [heqa, hgt]
    grind
  case curr' =>
    unfold view_app_hole?
    expose_names
    have heqa  : run_norm_plus _ _ = _ := complete (M := Option) (by assumption)
    have h_dec := max_hole_preserved (by assumption)
    simp [heqa, hgt]
    clear a
    simp_all [AndNorm.parapp_elim, AndNorm.curr'_hole]
    aesop

#check ViewAppHole.complete_some

def ViewAppHole.eq (h₁ h₂ : ViewAppHole f hole₁ lv hlt mem) : h₁ = h₂ := by
  induction h₁
  any_goals (
    focus
    try (
      cases h₂ <;> (
        expose_names
        cases unique hrt hrt_1
        cases proof_eq hrt hrt_1
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

theorem view_app_hole_none_sound (h : view_app_hole? (τ_c := τ_c) f hole₁ lv hlt mem = .none) : ViewAppHole f hole₁ lv hlt mem → False := by
  intro h
  have heq := h.complete
  grind

@[dcc_rel]
def ViewAppHole.reduction (h : ViewAppHole f x lv hlt hmem) : Σ B, DSL((f x) →!wh⁺ B) := by
  cases h <;> exact ⟨_, by assumption⟩

/-
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
  sorry-/

/-
Alternative to Σ(B, C) x -> Coup(C x)

x : A
-------------------------------
⟦B⟧(x, y) : Σ()

TODO: leaving this alone for now
-/

/-
Termination argument is straightforward in Canonicalize since we're only recursion on comp or curr
-/

theorem Domain.decreasing (h : ViewAppHole f x lv hlt hmem) (h_dom : Domain f A) : A.size < f.size := by
  cases h <;> exact dom_decreasing (AndNorm.raw (by assumption)) (by assumption)

def ViewAppHole.quot_nmem {e_h : Hole A lv x} (hv : ViewAppHole f x lv hlt e_h.max_hole)
  (hrt : DSL((f x) →!wh⁺ e')) (_heq : hv = .quot hrt hgt) : e'.max_hole < x.min_hole := by
  have h := e_h.min_hole
  grind

/-
Quot at least
-/

/-
f contains the constant x in some way
-/
def AndNorm.quot_size_at_least (hrt : DSL((f x) →!wh⁺ x')) (h_size_hole : x.size = 0) : Σ' m, f.size = x'.size + m := by
  have h_dec := decreasing hrt
  exact ⟨f.size - x'.size, by grind⟩

@[grind ., grind →]
theorem RedAff.domain_max_hole_preserved (h : RedAff (DCC? Dom(x)) τ) : τ.max_hole ≤ x.max_hole := by
  cases h <;> grind

theorem AndNorm.domain_max_hole_preserved (h : DSL(Dom(x) →!wh⁺ τ)) : τ.max_hole ≤ x.max_hole :=
  match h.raw with
  | .single ⟨⟨h⟩, _⟩ => h.max_hole_preserved
  | .head ⟨⟨h⟩, _⟩ hrt => by
    have h₁ := h.max_hole_preserved
    have h₂ := max_hole_preserved hrt
    grind

/-
In general, no spine reduction can mention a hole on the left,
since this is unrestricted duplication.
-/

def RedHead.max_hole_preserved_fun
  {f x : GenericExpr τ_c}
  (hlt : f.max_hole < lv)
  (hr  : RedHead (DCC? (f x)) (DCC? (g x))) : g.max_hole < lv :=
  match hr with
  | ⟨⟨hr⟩, hn⟩ => by
    cases hr <;> grind

end GenericExpr

/-
TODO:
-/
