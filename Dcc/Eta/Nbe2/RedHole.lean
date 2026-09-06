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
  | unbox  : (hrt : RedSpineNorm (DCC? (*(A) &(y))) y)
    → (hgt : ¬ y.max_hole < lv)
    → (hsp : hrt.head = ⟨y, ⟨.unbox⟩, .unbox⟩)
    → ViewAppHole (DCC? *(A)) (DCC? &(y)) lv hlt hmem
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
def RedSpineNorm.unbox_hole (hrt : RedSpineNorm (DCC? (*(A) hole₁)) e') : Σ' y, hole₁ = DCC? &(y) := by
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

theorem max_hole_points {e : GenericExpr τ} (n : ℕ) (hn : e.max_hole < lv) (hlt : n < e.point_arity := by first | grind | dcc_simp) : (e.points.get ⟨n, hlt⟩).max_hole < lv := by
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
      | DCC? Dom(_x) | DCC? Sort _m | DCC? ∗ | DCC? ⊤ | DCC? ⊥
      | DCC? (_x = _y) | DCC? refl(_B) | DCC? ⟦_B⟧(_x, _y) | DCC? Coup(_B)
      | DCC? Π(_B, _C) | DCC? !(_A) | .const _n | .hole _n => False.elim (hrt.elim_norm_flse (fun _ hr hn => nomatch hn))
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
            let heq' := hrt.unique ⟨.single .eql .eql, fun _ _ h => nomatch h⟩
            exact .some (.eql (heq' ▸ hrt) (heq' ▸ hn') (heq' ▸ hrt).head_eq)
  | .none => .none

def ViewAppHole.complete_some (h : ViewAppHole (τ_c := τ_c) f hole₁ lv hlt mem) : (view_app_hole? f hole₁ lv hlt mem).isSome := by
  induction h
  case quot | id | comp =>
    unfold view_app_hole?
    expose_names
    have heqa := RedSpineNorm.complete (by assumption)
    have h_dec := RedSpineNorm.max_hole_preserved (by assumption)
    simp_all [max_hole]
    try (aesop)
  case curr =>
    unfold view_app_hole?
    expose_names
    have heqa := RedSpineNorm.complete (by assumption)
    have h_dec := RedSpineNorm.max_hole_preserved (by assumption)
    simp [heqa, hgt, RedSpineNorm.parapp_elim]
    split
    · simp
    · grind
  case fst | snd | eval | eql | pair | unbox | fmap | map | sigma =>
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

theorem view_app_hole_none_sound (h : view_app_hole? (τ_c := τ_c) f hole₁ lv hlt mem = .none) : ViewAppHole f hole₁ lv hlt mem → False := by
  intro h
  have heq := h.complete
  grind

@[dcc_rel]
def ViewAppHole.reduction (h : ViewAppHole f x lv hlt hmem) : Σ B, RedSpineNorm (DCC? (f x)) B := by
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
ViewAppHole cases that can be condensed to a single combinator

ReadbackHead should always have size ≤ f since Domain.size <
and x' <
-/
inductive ReadbackHead : (f : GenericExpr τ_c) → (h_dom : Domain f A)
  → (e_h : Hole A lv x)
  → (hlt : f.max_hole < lv)
  → (hrt : ViewAppHole f x lv hlt e_h.max_hole)
  → (f' : GenericExpr τ_c) → Type u
  | id  {h_dom : Domain f A} {e_h : Hole A lv x}
    {hrt : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = x) → ReadbackHead f h_dom e_h hlt hrt (DCC? Id(A))
  | fst {h_dom : Domain f (DCC? Coup(B))} {e_h : Hole (DCC? Coup(B)) lv (DCC? ⟦_B⟧(x, y))}
    {hrt : ViewAppHole f (DCC? ⟦_B⟧(x, y)) lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = x) → ReadbackHead f h_dom e_h hlt hrt (DCC? Fst(B))
  | snd {h_dom : Domain f (DCC? Coup(B))} {e_h : Hole (DCC? Coup(B)) lv (DCC? ⟦_B⟧(x, y))}
    {hrt : ViewAppHole f (DCC? ⟦_B⟧(x, y)) lv hlt e_h.max_hole} :
    (heq : hrt.reduction.fst = y) → ReadbackHead f h_dom e_h hlt hrt (DCC? Snd(B))
  | quot {h_dom : Domain f A} {e_h : Hole A lv x}
    {hrt : ViewAppHole f x lv hlt e_h.max_hole} :
    (heq : hrt = .quot (x' := x') hred hgt)
    → ReadbackHead f h_dom e_h hlt hrt (DCC? `(A, x'))
  --| map  {h_dom : Domain f (DCC? !(A))} {e_h : Hole A lv (DCC? &(x))}

/-
Termination argument is straightforward in Canonicalize since we're only recursion on comp or curr
-/

theorem Domain.decreasing (h : ViewAppHole f x lv hlt hmem) (h_dom : Domain f A) : A.size < f.size := by
  cases h <;> exact RedSpineNorm.dom_decreasing (by assumption) (by assumption)

def ViewAppHole.readback_head? {f : GenericExpr τ_c} (h_dom : Domain f A)
  (e_h : Hole A lv x) (hlt : f.max_hole < lv)
  (hrt : ViewAppHole f x lv hlt e_h.max_hole) : Option (Σ' f', ReadbackHead f h_dom e_h hlt hrt f') :=
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

def ViewAppHole.quot_nmem {e_h : Hole A lv x} (hv : ViewAppHole f x lv hlt e_h.max_hole)
  (hrt : RedSpineNorm (DCC? (f x)) e') (_heq : hv = .quot hrt hgt) : e'.max_hole < x.min_hole := by
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

@[aesop unsafe 50% forward (rule_sets := [DccForceReduce])]
def ReadbackHead.complete {f : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h : Hole A lv x}
  {hlt : f.max_hole < lv}
  {hrt : ViewAppHole f x lv hlt e_h.max_hole}
  (h : ReadbackHead (τ_c := τ_c) f h_dom e_h hlt hrt f') : hrt.readback_head? h_dom e_h = .some ⟨f', h⟩ := by
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
      have h := ViewAppHole.quot_nmem (ViewAppHole.quot hrt' hn') hrt' (by rfl) (A := B.coup) (e_h := e_h_1) (hlt := hlt_1)
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
      have h := ViewAppHole.quot_nmem (ViewAppHole.quot hrt' hn') hrt' (by rfl) (A := B.coup) (e_h := e_h_1) (hlt := hlt_1)
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

def ReadbackHead.preservation {f x f' A : GenericExpr τ_c} {h_dom : Domain f A} {e_h : Hole A lv x} {hlt : f.max_hole < lv} {hrt : ViewAppHole f x lv hlt e_h.max_hole}
  (h : ReadbackHead f h_dom e_h hlt hrt f') : Domain f' A := by
  have hn := h_dom.is_norm
  cases h with
  | quot | id =>
    exact ⟨⟨.single (by constructor), by assumption⟩⟩
  | fst | snd =>
    expose_names
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

def ReadbackHead.max_hole_preserved {f f' A : GenericExpr τ_c} {h_dom : Domain f A}
  {e_h : Hole A lv x}
  {hlt : f.max_hole < lv}
  {hrt : f.ViewAppHole x lv hlt e_h.max_hole}
  (h : ReadbackHead f h_dom e_h hlt hrt f') : f'.max_hole < lv := by
  have h_dec := h_dom.max_hole_preserved
  cases h <;> grind

def ReadbackHead.preservation_view {f f' A : GenericExpr τ_c} {h_dom : Domain f A} {e_h : Hole A lv x}
  {hlt : f.max_hole < lv}
  {hrt : f.ViewAppHole x lv hlt e_h.max_hole}
  (h : ReadbackHead f h_dom e_h hlt hrt f') : f'.ViewAppHole x lv
  h.max_hole_preserved
  e_h.max_hole := by
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
    apply ViewAppHole.fst (hrt := ⟨.single .fstc .fstc, e_h.is_norm.sigl.to_head⟩) (lv := lv) (hgt := by grind)
    simp [RedSpineNorm.head]
  | snd heq =>
    have heq' : hrt.reduction = ⟨hrt.reduction.fst, hrt.reduction.snd⟩ := rfl
    expose_names
    apply ViewAppHole.snd (hrt := ⟨.single .sndc .sndc, e_h.is_norm.sigr.to_head⟩) (lv := lv) (hgt := by grind)
    simp [RedSpineNorm.head]
  | quot heq =>
    have heq' : hrt.reduction = ⟨hrt.reduction.fst, hrt.reduction.snd⟩ := rfl
    apply ViewAppHole.quot (hrt := ⟨.single .quot .quot, by rename_i hred; exact hred.is_norm⟩)
    · grind

def ReadbackHead.ext (hr₁ : RedSpineNorm (DCC? (f x)) B)
  (hr₂    : RedSpineNorm (DCC? (g x)) B)
  (h_dom₁ : Domain f A)
  (h_dom₂ : Domain g A)
  (e_h    : Hole A lv x)
  (hlt₁   : f.max_hole < lv)
  (hlt₂   : g.max_hole < lv)
  (hrt₁   : f.ViewAppHole x lv hlt₁ e_h.max_hole)
  (hrt₂   : g.ViewAppHole x lv hlt₂ e_h.max_hole)
  (hrb₁   : ReadbackHead f h_dom₁ e_h hlt₁ hrt₁ f')
  (hrb₂   : ReadbackHead g h_dom₂ e_h hlt₂ hrt₂ g') : f' = g' := by
  cases hrb₁ with
  | snd heq₁ =>
    cases hrb₂ with
    | snd heq₂ => rfl
    | fst heq₂ =>
      let hr₃  := hrt₁.reduction.snd
      let hr₄  := hrt₂.reduction.snd
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      expose_names
      have hneq := e_h.coup_points_neq
      simp_all
    | id heq₂ =>
      let hr₃ := hrt₁.reduction.snd
      let hr₄ := hrt₂.reduction.snd
      have heqa := hr₃.unique hr₁
      have heqb := hr₄.unique hr₂
      have h := ((heq₁.symm.trans heqa).trans heqb.symm).trans heq₂
      cases h
    | quot heq₂ =>
      let hr₃ := hrt₁.reduction.snd
      let hr₄ := hrt₂.reduction.snd
      have heqa := hr₃.unique hr₁
      have heqb := hr₄.unique hr₂
      expose_names
      have heqa' : y = B := by
        simp_all [ViewAppHole.reduction]
      cases heqa'
      cases heq₂
      simp [ViewAppHole.reduction] at heqb
      cases heqb
      have ha := e_h.max_hole
      have hb := e_h.min_hole
      have hc := hr₁.max_hole_preserved
      cases hb
      simp_all
      grind
  | fst heq₁ =>
    cases hrb₂ with
    | fst heq₂ => rfl
    | snd heq₂ =>
      let hr₃  := hrt₁.reduction.snd
      let hr₄  := hrt₂.reduction.snd
      let heqa := (heq₁ ▸ hr₃).unique hr₁
      let heqb := (heq₂ ▸ hr₄).unique hr₂
      expose_names
      have hneq := e_h.coup_points_neq
      simp_all
    | id heq₂ =>
      let hr₃ := hrt₁.reduction.snd
      let hr₄ := hrt₂.reduction.snd
      have heqa := hr₃.unique hr₁
      have heqb := hr₄.unique hr₂
      have h := ((heq₁.symm.trans heqa).trans heqb.symm).trans heq₂
      cases h
    | quot heq₂ =>
      let hr₃ := hrt₁.reduction.snd
      let hr₄ := hrt₂.reduction.snd
      have heqa := hr₃.unique hr₁
      have heqb := hr₄.unique hr₂
      expose_names
      have heqa' : x = B := by
        simp_all [ViewAppHole.reduction]
      cases heqa'
      cases heq₂
      simp [ViewAppHole.reduction] at heqb
      cases heqb
      have ha := e_h.max_hole
      have hb := e_h.min_hole
      have hc := hr₁.max_hole_preserved
      cases hb
      simp_all
      grind
  | id =>
    cases hrb₂ with
    | id => rfl
    | quot heq' =>
      cases heq'
      expose_names
      have ha := hr₁.max_hole_preserved
      have hb := hr₂.max_hole_preserved
      have hc := e_h.max_hole
      have hd := e_h.min_hole
      have he := hred.max_hole_preserved
      cases hrt₁
      any_goals (
        focus
        try (
          simp [ViewAppHole.reduction] at heq
          cases heq
          expose_names
          cases hrt.unique hr₁
          cases hr₂.unique hred
          cases hd
          have h : x.max_hole = x.min_hole := by grind
          grind)
        done)
      case fst | snd | unbox =>
        simp [ViewAppHole.reduction] at heq
        cases heq
      case eql =>
        simp [ViewAppHole.reduction] at heq
    | snd heq' | fst heq' =>
      expose_names
      have ha := hr₁.max_hole_preserved
      have hb := hr₂.max_hole_preserved
      have hc := e_h.max_hole
      have hd := e_h.min_hole
      let h := heq ▸ hrt₁.reduction.snd
      cases h.unique hr₁
      let h' := heq' ▸ hrt₂.reduction.snd
      cases h'.unique hr₂
  | quot =>
    cases hrb₂ with
    | snd | fst =>
      expose_names
      have ha := hr₁.max_hole_preserved
      have hb := hr₂.max_hole_preserved
      have hc := e_h.max_hole
      have hd := e_h.min_hole
      let h := heq ▸ hrt₁.reduction.snd
      cases h.unique hr₁
      simp [ViewAppHole.reduction] at ha
      simp [ViewAppHole.reduction] at hb
      simp [ViewAppHole.reduction] at hr₁
      simp [ViewAppHole.reduction] at hr₂
      simp [ViewAppHole.reduction] at h
      cases hd
      cases heq
      cases hrt₂
      · simp [ViewAppHole.reduction] at heq_1
        cases heq_1
        grind
      any_goals (
        focus
        try (
          simp [ViewAppHole.reduction] at heq_1
          cases heq_1
          expose_names
          cases hr₂.unique hrt
          simp_all)
        done)
      case id =>
        simp [ViewAppHole.reduction] at heq_1
        cases heq_1
    | quot heq' =>
      expose_names
      let h := heq ▸ hrt₁.reduction.snd
      cases h.unique hr₁
      let h' := heq' ▸ hrt₂.reduction.snd
      cases h'.unique hr₂
      rfl
    | id heq' =>
      expose_names
      have ha := hr₁.max_hole_preserved
      have hb := hr₂.max_hole_preserved
      have hc := e_h.max_hole
      have hd := e_h.min_hole
      let h := heq ▸ hrt₁.reduction.snd
      cases h.unique hr₁
      let h' := heq' ▸ hrt₂.reduction.snd
      have he := h'.max_hole_preserved
      cases heq
      simp_all [← h'.unique hr₂]
      cases hrt₂
      · expose_names
        simp [ViewAppHole.reduction] at heq'
        cases heq'
        grind
      any_goals (
        focus
        try (
          expose_names
          simp [ViewAppHole.reduction] at heq'
          cases heq'
          simp [ViewAppHole.reduction] at hr₁
          simp [ViewAppHole.reduction] at h
          simp [ViewAppHole.reduction] at hr₂
          cases hrt.unique hr₂
          grind)
        done)
      case fst | snd | unbox =>
        simp [ViewAppHole.reduction] at heq'
        cases heq'
      case eql => simp [ViewAppHole.reduction] at heq'

def ReadbackHead.self {f : GenericExpr τ_c} {h_dom : Domain f A}
  {e_h : Hole A lv x} {hlt : f.max_hole < lv} {hrt : ViewAppHole f x lv hlt e_h.max_hole}
  (h : ReadbackHead f h_dom e_h hlt hrt f') : ReadbackHead f' h.preservation e_h h.max_hole_preserved h.preservation_view f' := by
  have heq₀ := h.complete
  have heq₁ := hrt.complete
  let h_pres := h.preservation_view
  cases heq₂ : h
  case quot =>
    cases heq₂
    exact ReadbackHead.quot rfl
  all_goals (
    constructor
    simp [preservation_view]
    cases heq₂
    simp [ViewAppHole.reduction])

end GenericExpr
