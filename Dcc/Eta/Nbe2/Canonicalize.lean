import Dcc.Eta.Nbe2.RedSpine
import Dcc.Eta.Nbe2.Hole
import Dcc.Eta.Nbe2.RedHole

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

theorem max_hole_self {e : GenericExpr τ} : GenericExpr.max_hole e < e.max_hole.succ :=
  Nat.lt_add_one e.max_hole

/-
When ViewAppHole reduces to part of the hole, we have reached a normal form.
So reduce these to the canonical projection, quotation, or Id.

Otherwise, the expression is "gluing" operations together in some way that does
meaningful work.

Always reduce all the points of the expression.

Decreasing argument goes by the length of the reduction in ViewAppHole

We do not assume f is in normal form. That is assumed in later proofs since defeq β-normalizes first.

Simply continue running Canonicalize until the size doesn't decrease.

Design fork:

- If we don't canonicalize indices, then we get slightly different types
  But preservation applies.
- Preservation is subsumed by showing Canonicalize twice is a no-op

I think it might just work. Let's try it.
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
    → (hrt  : ViewAppHole (DCC? f ∘ g) x (DCC? (f ∘ g)).max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? f ∘ g) h_dom e_h max_hole_self hrt f' → False)
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
    → (hrt  : ViewAppHole (DCC? f ∘' g) x (DCC? (f ∘' g)).max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? f ∘' g) h_dom e_h max_hole_self hrt f' → False)
    → (hc₁  : Canonicalize f f')
    → (hc₂  : Canonicalize g g') -- size of ∘' and ∘ is the same
    → Canonicalize (DCC? f ∘' g) (DCC? f' ∘ g')
  | comp₂  : (h_dom : Domain (DCC? f ∘∘ g) A)
    → (e_h  : Hole A (DCC? f ∘∘ g).max_hole.succ x)
    → (hrt  : ViewAppHole (DCC? f ∘∘ g) x (DCC? (f ∘∘ g)).max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? f ∘∘ g) h_dom e_h max_hole_self hrt f' → False)
    → (hc₁  : Canonicalize f f')
    → (hc₂  : Canonicalize g g') -- size of ∘' and ∘ is the same
    → Canonicalize (DCC? f ∘∘ g) (DCC? f' ∘ g')
  | eval   : (h_dom : Domain (DCC? Eval(A, B, x)) τ)
    → (e_h : Hole τ (DCC? Eval(A, B, x)).max_hole.succ y)
    → (hrt : ViewAppHole (DCC? Eval(A, B, x)) y (DCC? Eval(A, B, x)).max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? Eval(A, B, x)) h_dom e_h max_hole_self hrt f' → False)
    → (hc₁ : Canonicalize B B')
    → (hc₂ : Canonicalize x x')
    → Canonicalize (DCC? Eval(A, B, x)) (DCC? Eval(A, B', x'))
  | curr   : (h_dom : Domain (DCC? (Λ(A, B, x) y)) τ)
    → (e_h : Hole τ (DCC? (Λ(A, B, x) y)).max_hole.succ z)
    → (hrt : ViewAppHole (DCC? (Λ(A, B, x) y)) z (DCC? (Λ(A, B, x) y)).max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? (Λ(A, B, x) y)) h_dom e_h max_hole_self hrt f' → False)
    → (hc₁ : Canonicalize B B')
    → (hc₂ : Canonicalize x x')
    → Canonicalize (DCC? (Λ(A, B, x) y)) (DCC? (Λ(A, B', x') y))
  | curr'  : (h_dom : Domain (DCC? (!Λ(A, B, x) &(y))) τ)
    → (e_h : Hole τ (DCC? (!Λ(A, B, x) &(y))).max_hole.succ z)
    → (hrt : ViewAppHole (DCC? (!Λ(A, B, x) &(y))) z (DCC? (!Λ(A, B, x) &(y))).max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? (!Λ(A, B, x) &(y))) h_dom e_h max_hole_self hrt f' → False)
    → (hc₁ : Canonicalize B B')
    → (hc₂ : Canonicalize x x')
    → Canonicalize (DCC? (!Λ(A, B, x) &(y))) (DCC? (!Λ(A, B', x') &(y)))
  | eql    : (h_dom : Domain (DCC? (Eql(B) &(x))) τ)
    → (e_h : Hole τ (DCC? (Eql(B) &(x))).max_hole.succ y)
    → (hrt : ViewAppHole (DCC? (Eql(B) &(x))) y (DCC? (Eql(B) &(x))).max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? (Eql(B) &(x))) h_dom e_h max_hole_self hrt f' → False)
    → (hc₂ : Canonicalize B B')
    → Canonicalize (DCC? (Eql(B) &(x))) (DCC? (Eql(B') &(x)))
  | pair   : (h_dom : Domain (DCC? ⟦B⟧⟨x, y⟩) τ)
    → (e_h : Hole τ (DCC? ⟦B⟧⟨x, y⟩).max_hole.succ z)
    → (hrt : ViewAppHole (DCC? ⟦B⟧⟨x, y⟩) z (DCC? ⟦B⟧⟨x, y⟩).max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? ⟦B⟧⟨x, y⟩) h_dom e_h max_hole_self hrt f' → False)
    → (hc₁ : Canonicalize B B')
    → (hc₂ : Canonicalize x x')
    → (hc₃ : Canonicalize y y')
    → Canonicalize (DCC? ⟦B⟧⟨x, y⟩) (DCC? ⟦B'⟧⟨x', y'⟩)
  | unmap  : (h_dom : Domain (DCC? *<x>) τ)
    → (e_h : Hole τ (DCC? *<x>).max_hole.succ y)
    → (hrt : ViewAppHole (DCC? *<x>) y (DCC? *<x>).max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? *<x>) h_dom e_h max_hole_self hrt f' → False)
    → (hc₁ : Canonicalize x x')
    → Canonicalize (DCC? *<x>) (DCC? *<x'>)
  | fmap   : (h_dom : Domain (DCC? $<x>) τ)
    → (e_h : Hole τ (DCC? $<x>).max_hole.succ y)
    → (hrt : ViewAppHole (DCC? $<x>) y (DCC? $<x>).max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? $<x>) h_dom e_h max_hole_self hrt f' → False)
    → (hc₁ : Canonicalize x x')
    → Canonicalize (DCC? $<x>) (DCC? $<x'>)
  | map    : (h_dom : Domain (DCC? !<x>) τ)
    → (e_h : Hole τ (DCC? !<x>).max_hole.succ y)
    → (hrt : ViewAppHole (DCC? !<x>) y (DCC? !<x>).max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? !<x>) h_dom e_h max_hole_self hrt f' → False)
    → (hc₁ : Canonicalize x x')
    → Canonicalize (DCC? !<x>) (DCC? !<x'>)
  | sigma  : (h_dom : Domain (DCC? Σ(B, C)) τ)
    → (e_h : Hole τ (DCC? Σ(B, C)).max_hole.succ x)
    → (hrt : ViewAppHole (DCC? Σ(B, C)) x (DCC? Σ(B, C)).max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ∀ ⦃f'⦄, ReadbackHead (DCC? Σ(B, C)) h_dom e_h max_hole_self hrt f' → False)
    → (hc₁ : Canonicalize B B')
    → (hc₂ : Canonicalize C C')
    → Canonicalize (DCC? Σ(B, C)) (DCC? Σ(B', C'))
  | single : (h_dom : Domain f A)
    → (e_h  : Hole A f.max_hole.succ x)
    → (hrt  : ViewAppHole f x f.max_hole.succ max_hole_self e_h.max_hole)
    → (hrb  : ReadbackHead f h_dom e_h max_hole_self hrt f')
    → Canonicalize f f'

theorem readback_head_none_complete
  {f x : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h : Hole A lv x}
  {hlt : f.max_hole < lv}
  {hrt : f.ViewAppHole x lv hlt e_h.max_hole}
  (hn : ∀ ⦃f'⦄, ReadbackHead f h_dom e_h hlt hrt f' → False) : ViewAppHole.readback_head? h_dom e_h hlt hrt = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro h
  exact (hn h.snd).elim

theorem readback_head_none_sound
  {f x : GenericExpr τ_c}
  {h_dom : Domain f A}
  {e_h : Hole A lv x}
  {hlt : f.max_hole < lv}
  {hrt : f.ViewAppHole x lv hlt e_h.max_hole}
  (heq : hrt.readback_head? h_dom e_h hlt = .none) : ∀ ⦃f'⦄, ReadbackHead f h_dom e_h hlt hrt f' → False := by
  intro f' h
  cases h.complete.symm.trans heq

def canonicalize (f : GenericExpr τ_c) : Option ((f' : GenericExpr τ_c) × Canonicalize f f') :=
  let ⟨A, h_dom⟩ := f.domain
  let ⟨x, e_h⟩ := mk_hole A f.max_hole.succ
  match f.view_app_hole? x f.max_hole.succ (by grind) e_h.max_hole with
  | .some hrt =>
    match heq : hrt.readback_head? h_dom e_h with
    | .some ⟨f', hrb⟩ => .some ⟨_, .single h_dom e_h hrt hrb⟩
    | .none =>
      have hn_hrb := readback_head_none_sound heq
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

/-def canonicalize (f : GenericExpr τ_c) : Option ((f' : GenericExpr τ_c) × Canonicalize f f') :=
  let A     := f.domain.fst
  let h_dom := f.domain.snd
  let x     := (mk_hole A f.max_hole.succ).fst
  let e_h   := (mk_hole A f.max_hole.succ).snd
  match f.view_app_hole? x f.max_hole.succ max_hole_self e_h.max_hole with
  | .some hrt =>
    if heq : (hrt.readback_head? h_dom e_h max_hole_self).isSome then
      .some ⟨_, .single h_dom e_h hrt ((hrt.readback_head? h_dom e_h max_hole_self).get heq).snd⟩
    else
      have hnrb := readback_head_none_sound (hrt := hrt) (h_dom := h_dom) (e_h := e_h) (f := f) (Option.not_isSome_iff_eq_none.mp heq)
      match heq₂ : f with
      | (DCC? f ∘ g) =>
        match f.canonicalize, g.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .comp h_dom e_h hrt hnrb h₁ h₂⟩
        | _, _ => .none
      | (DCC? f ∘' g) =>
        match f.canonicalize, g.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .comp' h_dom e_h hrt hnrb h₁ h₂⟩
        | _, _ => .none
      | (DCC? f ∘∘ g) =>
        match f.canonicalize, g.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .comp₂ h_dom e_h hrt hnrb h₁ h₂⟩
        | _, _ => .none
      | DCC? Eval(A, B, f) =>
        match B.canonicalize, f.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .eval h_dom e_h hrt hnrb h₁ h₂⟩
        | _, _ => .none
      | DCC? (Λ(A, B, f) env) =>
        match B.canonicalize, f.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .curr h_dom e_h hrt hnrb h₁ h₂⟩
        | _, _ => .none
      | DCC? (!Λ(A, B, f) &(env)) =>
        match B.canonicalize, f.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .curr' h_dom e_h hrt hnrb h₁ h₂⟩
        | _, _ => .none
      | DCC? (Eql(B) &(env)) =>
        match B.canonicalize with
        | .some ⟨_, h₁⟩ => by
          subst heq₂
          exact .some ⟨_, .eql h_dom e_h hrt hnrb h₁⟩
        | .none => .none
      | DCC? ⟦B⟧⟨a, b⟩ =>
        match B.canonicalize with
        | .some ⟨_, h₁⟩ =>
          match a.canonicalize, b.canonicalize with
          | .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ => by
            subst heq₂
            exact .some ⟨_, .pair h_dom e_h hrt hnrb h₁ h₂ h₃⟩
          | _, _ => .none
        | .none => .none
      | DCC? *<x> =>
        match x.canonicalize with
        | .some ⟨_, h₁⟩ => by
          subst heq₂
          exact .some ⟨_, .unmap h_dom e_h hrt hnrb h₁⟩
        | .none => .none
      | DCC? $<x> =>
        match x.canonicalize with
        | .some ⟨_, h₁⟩ => by
          subst heq₂
          exact .some ⟨_, .fmap h_dom e_h hrt hnrb h₁⟩
        | .none => .none
      | DCC? !<x> =>
        match x.canonicalize with
        | .some ⟨_, h₁⟩ => by
          subst heq₂
          exact .some ⟨_, .map h_dom e_h hrt hnrb h₁⟩
        | .none => .none
      | DCC? Σ(B, C) =>
        match B.canonicalize, C.canonicalize with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => by
          subst heq₂
          exact .some ⟨_, .sigma h_dom e_h hrt hnrb h₁ h₂⟩
        | _, _ => .none
      | _ => .none
  | _ => .none-/

/-
1. If two functions reduce a hole to the same B, then they Canonicalize to the same thing
  - This can be reduced to showing that there is a shortest length reduction we reduce to
    Because: if the reduction lengths are the same then we can do a simple proof of funext on RedAff since they don't have different sizes
    - This can be reduced to showing that re-canonicalization is a noop (if this is true, which it probably isn't)
    - Can also show that if two functions reduce a hole the same, their canonicalizations have the same length
2. If there is no Canonicalization of a function, then there is no top-level spine reduction
  - Hence, this is a parapp, in which case congrFun forces funext
  - Also, if there is no spine reduction on the hole, then there is no canonicalization
3. Boilerplate to lift this out given 1 and 2
-/

set_option maxHeartbeats 10000000000 in
def Canonicalize.complete (h : Canonicalize (τ_c := τ_c) f f') : f.canonicalize = .some ⟨f', h⟩ := by
  induction h
  case comp | comp' | comp₂ | eval | curr | curr' | eql | pair | unmap | fmap | map | sigma =>
    unfold canonicalize
    try (have ha := readback_head_none_complete (by assumption))
    try (have haa := ReadbackHead.complete (by assumption))
    have hb := Hole.complete (by assumption)
    have hc := ViewAppHole.complete (by assumption)
    have hd := Domain.complete (by assumption)
    have he := Domain.complete_fst (by assumption)
    cases he
    cases hd
    have hb' := Sigma.ext_iff.mp hb
    cases hb'.left; cases hb'.right
    simp [hc]
    dcc_aesop' [force_reduce]
  case single f₀ A x f₀' h_dom e_h hrt hrb =>
    unfold canonicalize
    try (have ha := readback_head_none_complete (by assumption))
    try (have haa := ReadbackHead.complete (by assumption))
    have hb := Hole.complete (by assumption)
    have hc := ViewAppHole.complete (by assumption)
    have hd := Domain.complete (by assumption)
    have he := Domain.complete_fst (by assumption)
    cases he
    cases hd
    have hb' := Sigma.ext_iff.mp hb
    cases hb'.left; cases hb'.right
    simp [hc]
    dcc_aesop' [force_reduce]

inductive OptFn : (f : GenericExpr τ_c) → (f' : GenericExpr τ_c) → Type u
  | single : (hc : Canonicalize f f') → (hn : ¬ f'.size < f.size) → OptFn f f'
  | head   : (hc : Canonicalize f f') → (hn : f'.size < f.size)   → (ih : OptFn f' f'') → OptFn f f''

def opt_fn (f : GenericExpr τ_c) : Option ((f' : GenericExpr τ_c) × OptFn f f') :=
  match f.canonicalize with
  | .some ⟨f', hc⟩ =>
    if heq : f'.size < f.size then
      match f'.opt_fn with
      | .some ⟨f'', ih⟩ => .some ⟨_, .head hc heq ih⟩
      | .none => .none
    else .some ⟨_, .single hc heq⟩
  | .none => .none
termination_by f.size

def OptFn.complete (h : OptFn (τ_c := τ_c) f f') : f.opt_fn = .some ⟨f', h⟩ := by
  induction h with
  | single hc hn => simp [hc.complete, hn, opt_fn]
  | head hc hn _ ih => simp [opt_fn, hc.complete, hn, ih]

/-
TODO: comp' vs comp vs comp₂ can be condensed to the same judgment rule,
so we assume η-reduce to ∘.

Id(A) ∘ Id(A) handled by id
So ∘ is doing some work here.

For single-step cases, i.e., the normal form is reached in one-step, η-reduce to that.
-/

end GenericExpr
