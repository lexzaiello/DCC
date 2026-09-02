import Dcc.Aff.Red
import Dcc.Eta.Nbe2.Hole
import Dcc.Attrs

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

/-
Possible unary head-level reductions. Otherwise,
no head-level step is made.
-/
inductive RedAff.IsHead : (hr : RedAff A B) → Type u
  | fstc  {B _B a b}     : IsHead (.fstc (_α := B) (β := _B) (a := a) (b := b))
  | sndc  {B _B a b}     : IsHead (.sndc (_α := B) (β := _B) (a := a) (b := b))
  | eval  {A B _B x y z} : IsHead (.evalc (_α := A) (_β := B) (x := x) (__β := _B) (y := y) (z := z))
  | eql   {B env x}        : IsHead (.eql (f_α := B) (env := env) (x := x))
  | map   {x y}          : IsHead (.map (f := x) (x := y))
  | fmap  {x y}          : IsHead (.fmap (f := x) (x := y))
  | unmap {x y}          : IsHead (.unmap (f := x) (x := y))
  | pair  {B x y z}      : IsHead (.pair (β := B) (M := x) (N := y) (x := z))
  | curr' {A B x y z}    : IsHead (.curr' (α := A) (β := B) (x := x) (y := y) (z := z))
  | id    {A x}          : IsHead (.id (α := A) (x := x))
  | quot  {B x y}        : IsHead (.quot (β := B) (x := x) (y := y))
  | curr  {A B x y z}    : IsHead (.curr (α := A) (β := B) (x := x) (y := y) (z := z))
  | sigma {B C x}        : IsHead (.sigma (f_α := B) (f_β := C) (env := x))
  | comp  {x y z}        : IsHead (.comp (x := x) (y := y) (z := z))

def RedAff.IsHead.unique {hr₁ : RedAff A B} {hr₂ : RedAff A C} (hrt₁ : hr₁.IsHead) (hrt₂ : hr₂.IsHead) : B = C := by
  cases hrt₁ <;> (cases hrt₂; rfl)

def RedAff.IsHead.eq {hr₁ : RedAff A B} {hr₂ : RedAff A B} (hrt₁ : hr₁.IsHead) (hrt₂ : hr₂.IsHead) : hrt₁ = hrt₂ := by
  cases hrt₁ <;> (cases hrt₂; rfl)

@[grind]
def NormHead (A : GenericExpr τ_c) := ∀ ⦃B⦄ ⦃hr : RedAff A B⦄ (_hrt : hr.IsHead), False

@[grind]
def red_spine? (A : GenericExpr τ_c) : Option ((B : GenericExpr τ_c) × (hr : PLift (RedAff A B)) × hr.down.IsHead) :=
  match A with
  | DCC? (Σ(_B, _C) _x)
  | DCC? (Eql(_B) &(_y) &(_z))
  | DCC? (!Λ(_A, _B, _x) &(_y) &(_z))
  | DCC? (Λ(_A, _B, _x) _y _z)
  | DCC? (`(_B, _x) _y)
  | DCC? (⟦_B⟧⟨_x, _y⟩ &(_z))
  | DCC? ((_x ∘ _y) _z)
  | DCC? (*<_x> &(_y))
  | DCC? ($<_x> &(_y))
  | DCC? (!<_x> &(_y))
  | DCC? (Eval(_A, _B, _x) ⟦_C⟧(_y, _z))
  | DCC? (Id(_A) _x)
  | DCC? (Fst(_B) ⟦__B⟧(_x, _y))
  | DCC? (Snd(_B) ⟦__B⟧(_x, _y)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | _ => .none

@[grind =_, grind ., grind =>, grind! ., grind! =>]
theorem RedAff.IsHead.complete {hr : RedAff A B} (hrt : hr.IsHead) : red_spine? A = .some ⟨B, ⟨hr⟩, hrt⟩ := by
  induction hrt <;> grind

def RedAff.IsHead.decreasing {hr : RedAff A B} (_hrt : hr.IsHead) : B.size < A.size := hr.decreasing

inductive RedSpinePlus : GenericExpr τ_c → GenericExpr τ_c → Type u
  | single : (hr : RedAff A B) → (hrt : hr.IsHead) → RedSpinePlus A B
  | head   : (hr : RedAff A B) → (hrt : hr.IsHead) → (hrt₂ : RedSpinePlus B C) → RedSpinePlus A C

def RedSpinePlus.trans (hr₁ : RedSpinePlus A B) (hr₂ : RedSpinePlus B C) : RedSpinePlus A C :=
  match hr₁ with
  | .single h _ => .head h (by assumption) (by assumption)
  | .head a b c => .head a (by assumption) (trans (by assumption) (by assumption))

def RedSpinePlus.push_head (hr : RedAff A B) (hn : hr.IsHead) (hrt : RedSpinePlus B C) : RedSpinePlus A C :=
  .trans (.single hr hn) hrt

def RedSpinePlus.decreasing (hrt : RedSpinePlus A B) : size B < size A :=
  match hrt with
  | .single _ _ => by grind
  | .head hr _ hrt => by
    have h_dec₁ := hr.decreasing
    have h_dec₂ := hrt.decreasing
    grind

def RedSpinePlus.no_refl (hr : RedSpinePlus A A) : False := by
  cases hr
  · grind
  case head =>
    expose_names
    have ha := hrt₂.decreasing
    have hb := hr.decreasing
    grind

def RedSpinePlus.elim_norm (hrt : RedSpinePlus A B) (hn : NormHead A) : A = B :=
  match hrt with
  | .single hr hn' => (hn hn').elim
  | .head hrt₁ hr₂ hrt₂ => (hn (by assumption)).elim

@[grind]
def red_spine! (A : GenericExpr τ_c) : Option ((B : GenericExpr τ_c) × RedSpinePlus A B) :=
  match A.red_spine? with
  | .some ⟨B, ⟨hr⟩, hrt⟩ =>
    have h_dec := hrt.decreasing
    match B.red_spine! with
    | .some ⟨C, hr⟩ => .some ⟨_, .head (by assumption) (by assumption) hr⟩
    | .none => .some ⟨_, .single (by assumption) (by assumption)⟩
  | .none => .none
termination_by A.size

def RedSpinePlus.unique (hr₁ : RedSpinePlus A B) (hr₂ : RedSpinePlus A C) (hn₁ : NormHead B) (hn₂ : NormHead C) : B = C := by
  cases hr₁ with
  | single ha hb =>
    cases hr₂ with
    | single hc hd => exact hb.unique hd
    | head hc hd he =>
      have h_dec := hc.decreasing
      cases hb.unique hd
      exact he.elim_norm (by assumption)
  | head ha hb hc =>
    cases hr₂ with
    | single hc hd =>
      cases hb.unique hd
      exact (hc.elim_norm (by assumption)).symm
    | head hd he hf =>
      cases hb.unique he
      have h_dec := hd.decreasing
      exact hc.unique hf (by assumption) (by assumption)
termination_by A.size

def red_spine!_norm (heq : red_spine! A = .some ⟨B, h⟩) : NormHead B := fun h => by
  intro hr hrt
  have h := hrt.complete
  unfold red_spine! at heq
  expose_names
  have h_dec₁ := h_1.decreasing
  have h_dec₂ := hr.decreasing
  cases h_1 with
  | single ha hb =>
    simp [hb.complete] at heq
    unfold red_spine! at heq
    simp [h] at heq
    split at heq
    case h_1 =>
      simp at heq
      cases heq.left; cases heq.right
    case h_2 x heq' =>
      split at heq' <;> grind
  | head ha hb hc =>
    simp [hb.complete] at heq
    have h_dec₁ := hr.decreasing
    have h_dec₂ := ha.decreasing
    have h_dec₃ := hc.decreasing
    split at heq
    case h_1 =>
      expose_names
      have h := red_spine!_norm heq_1
      simp at heq
      cases heq.left; cases heq.right
      exact (h (by assumption)).elim
    · grind
termination_by A.size

def red_spine!_none_norm (heq : red_spine! A = .none) : NormHead A := fun h => by
  intro hr hrt
  have h := hrt.complete
  unfold red_spine! at heq
  simp [h] at heq
  split at heq <;> grind

def RedSpinePlus.eq (h₁ : RedSpinePlus A B) (h₂ : RedSpinePlus A B) : h₁ = h₂ := by
  cases h₁
  · cases h₂
    · expose_names
      simp [hrt.eq hrt_1]
    · expose_names
      have ha := hrt.unique hrt_1
      cases ha
      cases hrt₂.no_refl
  · cases h₂
    · expose_names
      have ha := hrt.unique hrt_1
      cases ha
      cases hrt₂.no_refl
    · expose_names
      have ha := hrt.unique hrt_1
      cases ha
      simp [hrt.eq hrt_1]
      exact hrt₂.eq hrt₂_1

def RedSpinePlus.complete (h : RedSpinePlus A B) (hn : B.NormHead) : red_spine! A = .some ⟨B, h⟩ := by
  unfold red_spine!
  split
  case h_1 =>
    split
    case h_1 =>
      expose_names
      cases h with
      | single ha hb =>
        have heq₁ := hb.complete
        have heq₂ := hrt.complete
        have heq₃ := heq₁.symm.trans heq₂
        simp at heq₃
        cases heq₃.left; cases heq₃.right
        cases hr_1.elim_norm (by assumption)
        cases hr_1.no_refl
      | head ha hb hc =>
        have heq₂ := hrt.complete
        have h_dec₁ := hr.decreasing
        have h_dec₂ := hb.decreasing
        have hn₁ := red_spine!_norm heq_1
        have h₁ := (RedSpinePlus.head ha hb hc)
        have h₂ := (RedSpinePlus.head hr hrt hr_1)
        have heq' := h₁.unique h₂ (by assumption) (by assumption)
        have heq'' := hrt.unique hb
        cases heq'; cases heq''
        have heq''' := hrt.eq hb
        cases heq'''
        simp_all
        exact hr_1.eq (by assumption)
    case h_2 =>
      expose_names
      have h := hrt.complete
      have h := red_spine!_none_norm heq_1
      expose_names
      let hrt'' := RedSpinePlus.single hr (by assumption)
      let heq' := (RedSpinePlus.single hr (by assumption)).unique h_1 h hn
      cases heq'
      have heq''' := hrt''.eq h_1
      grind
  case h_2 =>
    cases h <;> (
      expose_names
      have h := hrt.complete
      grind)

/-
TODO: to also get this to work, we need to merge comp, comp' and comp₂.
The difference is really ugly anyway and it can be fixed by just merging the type constructors.
-/

/-
If Par fires, then there is no head reduction,
which means (f x = g x) means by congrFun f = g
-/

@[grind ., grind! .]
theorem min_hole_le_max_hole : min_hole e ≤ max_hole e := by
  induction e <;> grind

@[grind ., grind →]
theorem RedAff.max_hole_preserved (h : RedAff A B) : max_hole B ≤ max_hole A := by
  induction h <;> grind

def RedAffNorm.max_hole_preserved (h : RedAffNorm A ⟨B, hn_B⟩) : max_hole B ≤ max_hole A := by
  match h with
  | ⟨hr, hn⟩ =>
    match hr.cases_head with
    | .inl h =>
      cases h
      grind
    | .inr ⟨_, h₁, h₂⟩ =>
      have h_dec := h₁.decreasing
      have ha := h₁.max_hole_preserved
      have hb := max_hole_preserved ⟨h₂, hn⟩
      grind
termination_by A.size

open GenericExpr

inductive Domain : GenericExpr τ_c → GenericExpr τ_c → Type u
  | mk : RedAffNorm (DCC? Dom(x)) ⟨τ, hn_τ⟩ → Domain x τ

def Domain.is_norm (h : Domain α τ) : IsNorm RedAff τ :=
  match h with
  | ⟨_, hn⟩ => hn

@[grind]
def domain (e : GenericExpr τ_c) : ((τ : GenericExpr τ_c) × Domain e τ) :=
  ⟨_, ⟨aff_sound' (DCC? Dom(e))⟩⟩

def Domain.complete (h : Domain e τ) : domain e = ⟨τ, h⟩ :=
  match h with
  | ⟨hr⟩ => by
    have h := (hr.out_eq ▸ hr).eq
    grind

inductive RedSpineStar : GenericExpr τ_c → GenericExpr τ_c → Type u
  | mk₁  : RedSpinePlus A B → RedSpineStar A B
  | refl : RedSpineStar A A

@[grind]
def RedSpinePlus.tail {A C : GenericExpr τ_c} (h : RedSpinePlus A C) : ((B : GenericExpr τ_c) × (_hrt : RedSpineStar A B) × (hr : PLift (RedAff B C)) × hr.down.IsHead) :=
  match h with
  | .single hr hn =>
    ⟨_, .refl, ⟨hr⟩, hn⟩
  | head ha hb hc =>
    have ⟨_, hrt', hr, hn⟩ := hc.tail
    match hrt' with
    | .mk₁ hrt' =>
      ⟨_, .mk₁ (.head ha hb hrt'), hr, hn⟩
    | .refl =>
      ⟨_, .mk₁ (.single ha hb), hr, hn⟩

def RedSpinePlus.max_hole_preserved (h : RedSpinePlus A B) : max_hole B ≤ max_hole A :=
  match h with
  | .single ha hb => by grind
  | .head ha hb hc => by
    have h_dec₁ := ha.max_hole_preserved
    have h_dec₂ := ha.decreasing
    have h_dec₃ := hc.max_hole_preserved
    grind
termination_by A.size

inductive RedSpineNorm : GenericExpr τ_c → GenericExpr τ_c → Type u
  | mk : (hr : RedSpinePlus A B) → (hn : B.NormHead) → RedSpineNorm A B

@[grind]
def red_spine!! (A : GenericExpr τ_c) : Option ((B : GenericExpr τ_c) × RedSpineNorm A B) :=
  match heq : A.red_spine! with
  | .some ⟨B, h⟩ => .some ⟨B, ⟨h, red_spine!_norm heq⟩⟩
  | .none => .none

@[grind =_, grind ., grind! .]
theorem RedSpineNorm.complete (h : RedSpineNorm A B) : red_spine!! A = .some ⟨B, h⟩ := by
  cases h with
  | mk hr hn =>
    have h := hr.complete hn
    grind

@[dcc_rel, aesop safe destruct (rule_sets := [DccRel])]
def RedSpineNorm.unique (h₁ : RedSpineNorm A B) (h₂ : RedSpineNorm A C) : B = C := by
  have ha := h₁.complete
  have hb := h₂.complete
  grind

@[dcc_rel, aesop safe destruct (rule_sets := [DccRel])]
def RedSpineNorm.eq (h₁ : RedSpineNorm A B) (h₂ : RedSpineNorm A B) : h₁ = h₂ := by
  cases h₁
  cases h₂
  expose_names
  simp [hr.eq hr_1]

@[grind]
def RedSpineNorm.tail {A C : GenericExpr τ_c} (h : RedSpineNorm A C) : ((B : GenericExpr τ_c) × (hr : PLift (RedAff B C)) × hr.down.IsHead) :=
  match h with
  | ⟨hr, _hn⟩ =>
    have ⟨B, _hrt, ⟨hr⟩, hn⟩ := hr.tail
    ⟨B, ⟨hr⟩, hn⟩

def RedSpineNorm.max_hole_preserved (h : RedSpineNorm A B) : max_hole B ≤ max_hole A :=
  match h with
  | ⟨hrt, _⟩ => hrt.max_hole_preserved

/-
This essentially reverses a reduction to find a suitable combinator.
It takes a multi-step reduction and finds a matching unary combiantor.

This is not total, as in view_app_hole should return .none when there is no matching
top-level reduction that can be found.
In this case, par is ussed, and since par means there is no possible RedAff.IsHead
if (f x = g x), then congruence applies, hence f = g.

RedAffNorm is very sus here. But only for a few cases.
What if we recurse on pair?

Try out the IsHead proof first. Could change it to ReflTransGen instead for some.
I think this bottoms out at par but we need an intermediate RedAffNorm.

TODO: might have to figure out how to make the indices ergonomic for this in
Canonicalize
-/
inductive ViewAppHole : (f : GenericExpr τ_c)
  → (hole₁ : GenericExpr τ_c)
  → (hlt : f.max_hole < hole₁.min_hole) → Type u
  | quot   : RedSpineNorm (DCC? (f hole₁)) x'
    → (hlt : f.max_hole < hole₁.min_hole)
    → (hn  : x'.max_hole < hole₁.min_hole := by grind)
    → ViewAppHole f hole₁ hlt
  -- par is not actually a case. this is the fallback that should hit if no ViewAppHole is present
  /-| par    : RedAffNorm (DCC? (f hole₁)) ⟨(DCC? (f' hole₁)), hn'⟩
    → (hlt : f.max_hole < hole₁.min_hole)
    → ViewAppHole f hole₁ hlt-/
  -- Note: this will need to recurse since we can't just blindly assume hole₁
  -- we just need to know the hole is in there somewhere could be f (g (h hole))
  -- if this does not fire, just do quot
  | comp   : (hrt : RedSpineNorm (DCC? (f x)) (DCC? (f' (g' x))))
    → (hlt : f.max_hole < hole₁.min_hole)
    → (hgt : (DCC? (f' (g' x))).max_hole ≥ hole₁.min_hole)
    → (hsp : hrt.tail = ⟨_, ⟨.comp⟩, .comp⟩)
    → ViewAppHole f hole₁ hlt
  /-
    Since we are weak-head reducing, and since
    the root expression should already be in normal form (NOTE TODO ENFORCE THIS),
    it doesn't matterh what RedSpineNorm reduces to
    just what the last step was
  -/
  | id     : (hrt : RedSpineNorm (DCC? (f hole₁)) hole₁)
    → (hlt : f.max_hole < hole₁.min_hole)
    → (hsp : hrt.tail = ⟨(DCC? (Id(A) hole₁)), ⟨.id⟩, .id⟩)
    → ViewAppHole f hole₁ hlt
  | fst    : (hrt : RedSpineNorm (DCC? (f ⟦_B⟧(x, y))) x)
    → (hlt : f.max_hole < (DCC? ⟦_B⟧(x, y)).min_hole)
    → (hsp : hrt.tail = ⟨DCC? (Fst(B) ⟦_B⟧(x, y)), ⟨.fstc⟩, .fstc⟩)
    → ViewAppHole f (DCC? ⟦_B⟧(x, y)) hlt
  | snd    : (hrt : RedSpineNorm (DCC? (f ⟦_B⟧(x, y))) y)
    → (hlt : f.max_hole < (DCC? ⟦_B⟧(x, y)).min_hole)
    → (hsp : hrt.tail = ⟨DCC? (Snd(B) ⟦_B⟧(x, y)), ⟨.sndc⟩, .sndc⟩)
    → ViewAppHole f (DCC? ⟦_B⟧(x, y)) hlt
  -- TODO: g x y might not be the normal form. this is technically a stuck term I think
  -- this one is probably fine
  | eval   : (hrt : RedSpineNorm (DCC? (f ⟦_B⟧(x, y))) (DCC? (g x y)))
    → (hlt : f.max_hole < (DCC? ⟦_B⟧(x, y)).min_hole)
    → (hsp : hrt.tail = ⟨DCC? (Eval(A, B, g) ⟦_B⟧(x, y)), ⟨.evalc⟩, .eval⟩)
    → ViewAppHole f (DCC? ⟦_B⟧(x, y)) hlt
  -- this one is sus though
  | curr'  : (hrt : RedSpineNorm (DCC? (f &(y))) (DCC? (g &(⟦B⟧(x, y)))))
    → (hlt : f.max_hole < (DCC? &(y)).min_hole)
    → (hsp : hrt.tail = ⟨DCC? (!Λ(A, B, g) &(x) &(y)), ⟨.curr'⟩, .curr'⟩)
    → ViewAppHole f (DCC? &(y)) hlt
  | curr   : (hrt : RedSpineNorm (DCC? (f y)) (DCC? (g ⟦B⟧(x, y))))
    → (hlt : f.max_hole < (DCC? &(y)).min_hole)
    → (hsp : hrt.tail = ⟨DCC? (Λ(A, B, g) x y), ⟨.curr⟩, .curr⟩)
    → ViewAppHole f (DCC? y) hlt
  | eql    : (hrt : RedSpineNorm (DCC? (f &(x))) (DCC? (x = x)))
    → (hlt : f.max_hole < (DCC? &(y)).min_hole)
    → (hsp : hrt.tail = ⟨DCC? (Eql(B) &(env) &(x)), ⟨.eql⟩, .eql⟩)
    → ViewAppHole f (DCC? &(y)) hlt
  -- Even though pair reduces to ⟦B⟧((M x), (N x (M x))), this is not a concern since we
  -- are only interested in WHNF
  | pair   : (hrt : RedSpineNorm (DCC? (f &(z))) (DCC? ⟦(B z)⟧((x z), (y z (x z)))))
    → (hlt : f.max_hole < (DCC? &(z)).min_hole)
    → (hsp : hrt.tail = ⟨DCC? (⟦B⟧⟨x, y⟩ &(z)), ⟨.pair⟩, .pair⟩)
    → ViewAppHole f (DCC? &(z)) htl
  | unmap  : (hrt : RedSpineNorm (DCC? (f &(x))) (DCC? (g x)))
    → (hlt : f.max_hole < (DCC? &(x)).min_hole)
    → (hsp : hrt.tail = ⟨_, ⟨.unmap⟩, .unmap⟩)
    → ViewAppHole f (DCC? &(x)) htl
  | fmap  : (hrt : RedSpineNorm (DCC? (f &(x))) (DCC? &((g x))))
    → (hlt : f.max_hole < (DCC? &(x)).min_hole)
    → (hsp : hrt.tail = ⟨_, ⟨.fmap⟩, .fmap⟩)
    → ViewAppHole f (DCC? &(x)) htl
  | map   : (hrt : RedSpineNorm (DCC? (f &(x))) (DCC? !((g x))))
    → (hlt : f.max_hole < (DCC? &(x)).min_hole)
    → (hsp : hrt.tail = ⟨_, ⟨.map⟩, .map⟩)
    → ViewAppHole f (DCC? &(x)) htl
  -- if τ contains the hole, then this is Σ
  -- otherwise, the Coup does not depend on the hole
  -- in which case it is just `(
  | sigma    : (hrt : RedSpineNorm (DCC? (f x)) (DCC? Coup((C x))))
    → (hlt   : f.max_hole < x.min_hole)
    → (hsp : hrt.tail = ⟨DCC? (Σ(B, C) x), ⟨.sigma⟩, .sigma⟩)
    → ViewAppHole f x htl

def view_app_hole? (f hole₁ : GenericExpr τ_c) (hlt : f.max_hole < hole₁.min_hole) : Option (ViewAppHole f hole₁ hlt) :=
  match heq : (DCC? (f hole₁)).red_spine!! with
  | .some ⟨e', hrt⟩ =>
    if hn' : e'.max_hole < hole₁.min_hole then
      .some (.quot hrt hlt (by grind))
    else
      match e', heq₂ : hrt.tail with
      | e', ⟨_, _, .id (A := A)⟩ =>
        if heq₃ : e' = hole₁ then
          .some (.id (A := A) (heq₃ ▸ hrt) (by grind) (by dcc_aesop' [rel]))
        else .none
      | DCC? (f' (g' e')), ⟨_, _, .comp⟩ =>
        if heq₃ : e' = hole₁ then
          .some (.comp (heq₃ ▸ hrt) (by grind) (by grind) (by dcc_aesop' [rel]))
        else .none
      | e', ⟨_, _, .fstc (b := b) (B := B) (_B := _B)⟩ =>
        match hole₁ with
        | DCC? ⟦__B⟧(x, y) =>
          if heq₃ : e' = x then
            if heq₄ : __B = _B then
              if heq₅ : b = y then by
                cases heq₄
                cases heq₃
                cases heq₅
                exact .some (.fst (B := B) (_B := _B) hrt (by grind) (by dcc_aesop' [rel]))
              else .none
            else .none
          else .none
        | _ => .none
      | e', ⟨_, _, .sndc (a := a) (B := B) (_B := _B)⟩ =>
        match hole₁ with
        | DCC? ⟦__B⟧(x, y) =>
          if heq₃ : e' = y then
            if heq₄ : __B = _B then
              if heq₅ : a = x then by
                cases heq₄
                cases heq₃
                cases heq₅
                exact .some (.snd (B := B) (_B := _B) hrt (by grind) (by dcc_aesop' [rel]))
              else .none
            else .none
          else .none
        | _ => .none
      | (DCC? (g x y)), ⟨_, _, .eval (A := A) (B := B) (_B := _B)⟩ =>
        match hole₁ with
        | DCC? ⟦__B⟧(a, b) =>
          if heq : x = a ∧ y = b ∧ __B = _B then
            .some (.eval (A := A) (B := B) (heq.left ▸ heq.right.left ▸ hrt) (by grind) (by dcc_aesop' [rel]))
          else .none
        | _ => .none
      | (DCC? (g ⟦B⟧(x, y))), ⟨_, _, .curr (A := A)⟩ =>
        if heq : y = hole₁ then
          .some (.curr (A := A) (B := B) (g := g) (heq ▸ hrt) (by grind) (by dcc_aesop' [rel]))
        else .none
      | (DCC? (g &(⟦B⟧(x, y)))), ⟨_, _, .curr' (A := A)⟩ =>
        match hole₁ with
        | DCC? &(hole₁) =>
          if heq : y = hole₁ then
            .some (.curr' (A := A) (B := B) (g := g) (heq ▸ hrt) (by grind) (by dcc_aesop' [rel]))
          else .none
        | _ => .none
      | _, ⟨_, _, .eql (B := B) (env := env) (x := x)⟩ =>
        match hole₁ with
        | DCC? &(hole₁) =>
          if heq : hole₁ = x then
            .some (.eql (B := B) (env := env) (heq ▸ hrt) (by grind) (by dcc_aesop' [rel]))
          else .none
        | _ => .none
      | _, ⟨_, _, .pair (B := B) (x := x) (y := y) (z := z)⟩ =>
        match hole₁ with
        | DCC? &(hole₁) =>
          if heq : z = hole₁ then by
            cases heq
            exact .some (.pair (B := B) (x := x) (y := y) (z := z) hrt (by grind) (by dcc_aesop' [rel]))
          else .none
        | _ => .none
      | _, ⟨_, _, .unmap (x := x) (y := y)⟩ =>
        match hole₁ with
        | DCC? &(hole₁) =>
          if heq : hole₁ = y then by
            cases heq
            exact .some (.unmap (g := x) (x := y) hrt (by grind) (by dcc_aesop' [rel]))
          else .none
        | _ => .none
      | _, ⟨_, _, .map (x := x) (y := y)⟩ =>
        match hole₁ with
        | DCC? &(hole₁) =>
          if heq : hole₁ = y then by
            cases heq
            exact .some (.map (g := x) (x := y) hrt (by grind) (by dcc_aesop' [rel]))
          else .none
        | _ => .none
      | _, ⟨_, _, .fmap (x := x) (y := y)⟩ =>
        match hole₁ with
        | DCC? &(hole₁) =>
          if heq : hole₁ = y then by
            cases heq
            exact .some (.fmap (g := x) (x := y) hrt (by grind) (by dcc_aesop' [rel]))
          else .none
        | _ => .none
      | _, ⟨_, _, .sigma (B := B) (C := C) (x := x)⟩ =>
        if heq : x = hole₁ then
          .some (.sigma (B := B) (C := C) (heq ▸ hrt) (by grind) (by dcc_aesop' [rel]))
        else .none
      | _ => sorry
  | .none => .none

def view_app_hole? (f hole₁ : GenericExpr τ_c) (hlt : f.max_hole < hole₁.min_hole) : Option (ViewAppHole f hole₁ hlt) :=
  if heq : (reduce RedAff (DCC? (f hole₁))).fst = hole₁ then
    .some (.id ⟨reduce_sound_fst heq, reduce_norm_fst heq⟩ hlt)
  else if hn' : (reduce RedAff (DCC? (f hole₁))).fst.max_hole < hole₁.min_hole then
    .some (.quot ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ (by grind))
  else match reduce_with_norm RedAff (DCC? (f hole₁)) with
  | ⟨DCC? (g ⟦B⟧(x, y)), ⟨h⟩⟩ =>
    if heq : y = hole₁ then
      .some (.curr ⟨heq ▸ h.left, heq ▸ h.right⟩ hlt)
    else .none
  | _ =>
    match hole₁ with
    | DCC? ⟦B⟧(x, y) =>
      sorry
    | DCC? &(y) =>
      match reduce_with_norm RedAff (DCC? (f &(y))) with
      | ⟨DCC? (g &(⟦B⟧(x, y))), ⟨h⟩⟩ =>
        sorry
      | ⟨DCC? (x = y), ⟨h⟩⟩ =>
        
        sorry
      | ⟨DCC? ⟦B⟧((M x), (N x₁ (M₂ x₂))), ⟨h⟩⟩ =>
        if heq : (DCC? ⟦B⟧((M x), (N x₁ (M₂ x₂)))) = (DCC? ⟦B⟧((M y), (N y (M y)))) then
          .some (.pair ⟨heq ▸ h.left, heq ▸ h.right⟩ hlt)
        else .none
      | ⟨DCC? (f' x), ⟨h⟩⟩ =>
        if heq : x = y then
          .some (.unmap ⟨heq ▸ h.left, heq ▸ h.right⟩ hlt)
        else .none
      | ⟨DCC? &((f' x)), ⟨h⟩⟩ =>
        if heq : x = y then
          .some (.fmap ⟨heq ▸ h.left, heq ▸ h.right⟩ hlt)
        else .none
      | ⟨DCC? !((f' x)), ⟨h⟩⟩ =>
        if heq : x = y then
          .some (.map ⟨heq ▸ h.left, heq ▸ h.right⟩ hlt)
        else .none
      | _ => sorry
    | hole₁ =>
      match reduce_with_norm RedAff (DCC? (f hole₁)) with
      | ⟨DCC? (_f' (_g' hole₁')), ⟨h⟩⟩ =>
        if heq₂ : hole₁' = hole₁ then
          .some (.comp ⟨heq₂ ▸ h.left, heq₂ ▸ h.right⟩ hlt (by
            have ha : (reduce RedAff (f.app hole₁)).fst.max_hole ≥ hole₁.min_hole := by grind
            rw [reduce_complete_fst h.left h.right] at ha
            grind))
        else .none
      | ⟨DCC? Coup(B), ⟨h⟩⟩ =>
        .some (.sigma ⟨h.left, h.right⟩ hlt (by
          have ha : (reduce RedAff (f.app hole₁)).fst.max_hole ≥ hole₁.min_hole := by grind
          rw [reduce_complete_fst h.left h.right] at ha
          grind))
      | _ => .none

inductive ViewPar : (f : GenericExpr τ_c) → (hole₁ : GenericExpr τ_c)
  → (hlt : f.max_hole < hole₁.min_hole) → Type u
  | quot  : RedAffNorm (DCC? (f hole₁)) ⟨x', hn_x⟩
    → (hlt : f.max_hole < hole₁.min_hole)
    → (hn  : x'.max_hole < hole₁.min_hole := by grind)
    → ViewPar f hole₁ hlt
  | par   : RedAffNorm (DCC? (f hole₁)) ⟨(DCC? (f' hole₁)), hn'⟩
    → (hlt : f.max_hole < hole₁.min_hole)
    → ViewPar f hole₁ hlt
  | comp  : RedAffNorm (DCC? (f hole₁)) ⟨(DCC? (f' (g hole₁))), hn'⟩
    → (hlt : f.max_hole < hole₁.min_hole)
    → ViewPar f hole₁ hlt
  | id    : RedAffNorm (DCC? (f hole₁)) ⟨hole₁, hn'⟩
    → (hlt : f.max_hole < hole₁.min_hole)
    → ViewPar f hole₁ hlt

/-
Since we have ViewPar we can make a fallback case to par
then in later proofs, see what that ends up being
-/

@[grind]
def view_par (f hole₁ : GenericExpr τ_c) (hlt : f.max_hole < hole₁.min_hole) : Option (ViewPar f hole₁ hlt) :=
  if heq : (reduce RedAff (DCC? (f hole₁))).fst = hole₁ then
    .some (.id ⟨reduce_sound_fst heq, reduce_norm_fst heq⟩ hlt)
  else if hn' : (reduce RedAff (DCC? (f hole₁))).fst.max_hole < hole₁.min_hole then
    .some (.quot ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ (by grind))
  else match reduce_with_norm RedAff (DCC? (f hole₁)) with
  | ⟨DCC? (_f' hole₁'), ⟨h⟩⟩ =>
    if heq : hole₁' = hole₁ then
      .some (.par ⟨(heq ▸ h.left), (heq ▸ h.right)⟩ hlt)
    else
      match hole₁' with
      | DCC? (_g hole₁') =>
        if heq₂ : hole₁' = hole₁ then
          .some (.comp ⟨heq₂ ▸ h.left, heq₂ ▸ h.right⟩ hlt)
        else .none
      | _ => .none
  | _ => .none

def ViewPar.complete {f hole₁ : GenericExpr τ_c} {hn : f.max_hole < hole₁.min_hole}
  (h : ViewPar (τ_c := τ_c) f hole₁ hn) : view_par f hole₁ hn = .some h := by
  cases h with
  | par h hnb =>
    match h with
    | ⟨hr, hn⟩ =>
      have h := reduce_with_norm_complete hr hn
      have hb := reduce_complete_fst hr hn
      simp [view_par, h, hb]
      expose_names
      have h_mem : ¬ (f'.app hole₁).max_hole < hole₁.min_hole := by
        grind
      simp [h_mem]
      intro h
      cases h
  | comp h hnb =>
    match h with
    | ⟨hr, hn⟩ =>
      have h := reduce_with_norm_complete hr hn
      have hb := reduce_complete_fst hr hn
      simp [view_par, h, hb]
      expose_names
      have hneq : f'.app (g.app hole₁) ≠ hole₁ := fun h => by cases h
      simp [hneq]
      have h_mem₀ := h_1.max_hole_preserved
      have h_mem : ¬ (f'.app (g.app hole₁)).max_hole < hole₁.min_hole := by
        intro h
        have hlt' := min_hole_le_max_hole (e := hole₁)
        simp [max_hole] at h
        grind
      simp [h_mem]
      intro h
      cases h
  | id h hnb =>
    match h with
    | ⟨hr, hn⟩ =>
      have hb := reduce_complete_fst hr hn
      simp [view_par, hb]
  | quot h hnb=>
    match h with
    | ⟨hr, hn⟩ =>
      have h := reduce_with_norm_complete hr hn
      have hb := reduce_complete_fst hr hn
      simp [view_par, h, hb]
      expose_names
      have hneq : x' ≠ hole₁ := fun h => by
        have h_max_eq : max_hole x' = max_hole hole₁ := by grind
        have h_min_eq : min_hole x' = min_hole hole₁ := by grind
        grind
      simp [hneq, hn_2, hb]
      grind

def view_par_none_sound (h : view_par (τ_c := τ_c) f hole₁ hlt = .none) : ViewPar f hole₁ hlt → False := by
  intro h
  simp_all [h.complete]

def view_par_none_complete (h : ViewPar f hole₁ hlt → False) : view_par (τ_c := τ_c) f hole₁ hlt = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro hn heq
  exact h hn

/-
If ViewPar → False, then we must have a reduction of one of the remaining moves:
*<Fst(B)>
*<Snd(B)>
Fst(B)
Snd(B)
Eval(A, B, x)


we may be missing something however. for example pair.
we have not accounted for pair even though !(A) is destructable

technically Eql also destructs.

!Λ also destructs

fst' and snd' should be replaced by induction on unmap
-/

inductive ViewBranch : (f : GenericExpr τ_c) → (hole₁ : GenericExpr τ_c)
  → (hlt : f.max_hole < hole₁.min_hole) → Type u
  | fst   : RedAffNorm (DCC? (f ⟦B⟧(x, y))) ⟨x, hn_x⟩
    → (hlt : f.max_hole < (DCC? ⟦B⟧(x, y)).min_hole)
    → ViewBranch f (DCC? ⟦B⟧(x, y)) hlt
  | snd   : RedAffNorm (DCC? (f ⟦B⟧(x, y))) ⟨y, hn_x⟩
    → (hlt : f.max_hole < (DCC? ⟦B⟧(x, y)).min_hole)
    → ViewBranch f (DCC? ⟦B⟧(x, y)) hlt
  -- TODO: g x y might not be the normal form. this is technically a stuck term I think
  | eval  : RedAffNorm (DCC? (f ⟦B⟧(x, y))) ⟨DCC? (g x y), hn_x⟩
    → (hlt : f.max_hole < (DCC? ⟦B⟧(x, y)).min_hole)
    → ViewBranch f (DCC? ⟦B⟧(x, y)) hlt
  | curr' : RedAffNorm (DCC? (f &(y))) ⟨DCC? (g ⟦B⟧(x, y)), hn_x⟩
    → (hlt : f.max_hole < (DCC? &(y)).min_hole)
    → ViewBranch f (DCC? &(y)) hlt
  | eql   : RedAffNorm (DCC? (f &(y))) ⟨DCC? (x = y), hn_x⟩
    → (hlt : f.max_hole < (DCC? &(y)).min_hole)
    → ViewBranch f (DCC? &(y)) hlt
  | pair  : RedAffNorm (DCC? (f &(x))) ⟨DCC? ⟦B⟧⟨(M x), (N x (M x))⟩, hn_x⟩
    → (hlt : f.max_hole < (DCC? &(x)).min_hole)
    → ViewBranch f (DCC? &(x)) htl
  | unmap : RedAffNorm (DCC? (f &(x))) ⟨DCC? (f' x), hn_x⟩
    → (hlt : f.max_hole < (DCC? &(x)).min_hole)
    → ViewBranch f (DCC? &(x)) htl
  | fmap  : RedAffNorm (DCC? (f &(x))) ⟨DCC? &((f' x)), hn_x⟩
    → (hlt : f.max_hole < (DCC? &(x)).min_hole)
    → ViewBranch f (DCC? &(x)) htl
  | map  : RedAffNorm (DCC? (f &(x))) ⟨DCC? !((f' x)), hn_x⟩
    → (hlt : f.max_hole < (DCC? &(x)).min_hole)
    → ViewBranch f (DCC? &(x)) htl

/-
Types of reductions given a hole.

Always available:
- inject a constant value instead of the hole
- identity
-/

/-
Since hole lvs are initialized with the maximum hole, the preimage does not contain the hole
Use this to initialize hole in Canonicalize.
-/

/-
These are all the unique operations that can "pattern match" on a hole.
-/
inductive Canonicalize : (f : GenericExpr τ_c) → (f' : GenericExpr τ_c) → Type u
  | id      : (h_dom : Domain f A)
    → (e_h  : Hole A n hole₁)
    → (hn   : n > f.max_hole := by grind)
    → RedAffNorm (DCC? (f hole₁)) ⟨hole₁, e_h.is_norm⟩
    → Canonicalize f (DCC? Id(A))
  | fstc    : (h_dom : Domain f (DCC? Coup(B)))
    → (e_h  : Hole (DCC? Coup(B)) n (DCC? ⟦B⟧(a, b)))
    → (hn   : n > f.max_hole := by grind)
    → RedAffNorm (DCC? (f ⟦B⟧(a, b))) ⟨a, e_h.is_norm.sigl⟩
    → Canonicalize f (DCC? Fst(B))
  | sndc    : (h_dom : Domain f (DCC? Coup(B)))
    → (e_h  : Hole (DCC? Coup(B)) n (DCC? ⟦B⟧(a, b)))
    → (hn   : n > f.max_hole := by grind)
    → RedAffNorm (DCC? (f ⟦B⟧(a, b))) ⟨b, e_h.is_norm.sigr⟩
    → Canonicalize f (DCC? Snd(B))
  | fstc'   : (h_dom : Domain f (DCC? !(Coup(B))))
    → (e_h  : Hole (DCC? !(Coup(B))) n (DCC? &(⟦B⟧(a, b))))
    → (hn   : n > f.max_hole := by grind)
    → RedAffNorm (DCC? (f &(⟦B⟧(a, b)))) ⟨a, e_h.is_norm.box₀.sigl⟩
    → Canonicalize f (DCC? *<Fst(B)>)
  | sndc'   : (h_dom : Domain f (DCC? !(Coup(B))))
    → (e_h  : Hole (DCC? !(Coup(B))) n (DCC? &(⟦B⟧(a, b))))
    → (hn   : n > f.max_hole := by grind)
    → RedAffNorm (DCC? (f &(⟦B⟧(a, b)))) ⟨b, e_h.is_norm.box₀.sigr⟩
    → Canonicalize f (DCC? *<Snd(B)>)
  | par     : (h_dom : Domain f A)
    → (e_h  : Hole A n hole₁)
    → (hn   : n > f.max_hole := by grind)
    → RedAffNorm (DCC? (f hole₁)) ⟨(DCC? (f' hole₁)), hn₂⟩
    → Canonicalize f f'
  | comp    : (h_dom : Domain f A)
    → (e_h  : Hole A n hole₁)
    → (hn   : n > f.max_hole := by grind)
    → RedAffNorm (DCC? (f hole₁)) ⟨(DCC? (f' (g hole₁))), hn₂⟩
    → Canonicalize f (DCC? (f' ∘' g))
  | eval    : (h_dom : Domain f (DCC? Coup(B)))
    → (h_dom₂ : Domain B A)
    → (e_h  : Hole (DCC? Coup(B)) n (DCC? ⟦B⟧(a, b)))
    → (hn   : n > f.max_hole := by grind)
    → RedAffNorm (DCC? (f ⟦B⟧(a, b))) ⟨DCC? (f' a b), hn'⟩
    → Canonicalize f (DCC? Eval(A, B, f'))
  | quot    : (h_dom : Domain f B)
    → (e_h  : Hole B n hole₁)
    → (hn   : n > f.max_hole := by grind)
    → (hr_τ : RedAffNorm (DCC? (f hole₁)) ⟨x, hn_x⟩)
    → (hn   : x.max_hole < f.max_hole.succ)
    → Canonicalize e_f (DCC? `(B, x))

def canonicalize (f : GenericExpr τ_c) : Option ((f' : GenericExpr τ_c) × Canonicalize f f') :=
  let ⟨A, h_dom⟩  := f.domain
  let ⟨htm, h_hole⟩ := A.mk_hole f.max_hole.succ
  have h := h_hole.min_hole
  if heq_some : (view_par f htm (by grind)).isSome then
    match (view_par f htm (by grind)).get heq_some with
    | .par hr _ => .some ⟨_, .par h_dom h_hole (by grind) hr⟩
    | .comp hr _ => .some ⟨_, .comp h_dom h_hole (by grind) hr⟩
    | .id hr _ => .some ⟨_, .id h_dom h_hole (by grind) hr⟩
    | .quot hr _ _ => .some ⟨_, .quot h_dom h_hole (by grind) hr (by grind)⟩
  else
    
    sorry

inductive RedEta : (e : GenericExpr τ_c) → (e' : GenericExpr τ_c) → Type u
  | fn_type : (h_dom₁ : Domain C A)
    → (hr₁  : RedEta B B')
    → (hrt₂ : RedAffNorm (DCC? (C env)) ⟨Cenv, hn₂⟩)
    → (hr₂  : RedEta Cenv C')
    → (hr₃  : RedEta env env')
    → RedEta (DCC? (Π(B, C) env)) (DCC? (Π(B', `(A, C')) env'))
  | pi_comp : (hr₁ : RedEta (DCC? (B ∘' g)) B')
    → (hr₁ : RedEta (DCC? (C ∘' g)) C')
    → RedEta (DCC? (Π(B, C) ∘' g)) (DCC? (Π(B', C')))
  | pi      : RedEta B B' → RedEta C C' → RedEta (DCC? Π(B, C)) (DCC? Π(B', C'))
  | coup    : RedEta B B' → RedEta (DCC? Coup(B)) (DCC? Coup(B'))
  | bang    : RedEta A A' → RedEta (DCC? !(A)) (DCC? !(A'))
  | eq      : RedEta x x' → RedEta y y' → RedEta (DCC? x = y) (DCC? x' = y')
  | tm      : (hn : ViewEta x → False) → x.Canonicalize x' → RedEta x x'

def red_eta (e : GenericExpr τ_c) : ((e' : GenericExpr τ_c) × RedEta e e') :=
  match heq : e.view_eta? with
  | .some (.pi_type (f_α := B) (f_β := C) (env := env)) =>
    ⟨_, .fn_type
      ⟨reduce_sound rfl, reduce_norm rfl⟩
      B.red_eta.snd
      ⟨reduce_sound rfl, reduce_norm rfl⟩
      (reduce RedAff (DCC? (C env))).fst.red_eta.snd
      env.red_eta.snd⟩
  | .some (.pi_comp (f_α := B) (f_β := C) (g := g)) => ⟨_, .pi_comp (DCC? (B ∘' g)).red_eta.snd  (DCC? (C ∘' g)).red_eta.snd ⟩
  | .some (.pi (f_α := B) (f_β := C)) => ⟨_, .pi B.red_eta.snd C.red_eta.snd⟩
  | .some (.coup (β := β)) => ⟨_, .coup β.red_eta.snd⟩
  | .some (.bang (β := β)) => ⟨_, .bang β.red_eta.snd⟩
  | .some (.eq (x := x) (y := y)) => ⟨_, .eq x.red_eta.snd y.red_eta.snd⟩
  | .none => ⟨_, .tm (view_eta?_none_sound (by grind)) e.canonicalize.snd⟩
termination_by size e
decreasing_by
  any_goals (grind)

/-
Suppose we have proven that a user's DCC proof that ∀ x : A, f x = g x as a DCC theorem
can be transported into the meta-level by noting that:
- the only possible destructing / branching on terms is via couple projection or affine destruction (e.g., *<f>)
Hence, it suffcies 

Mad alternative proof strategy:
- If extensional elim is possible, that is:

theorem elim_eq (h : Judge x (DCC? (x = y))) : x = y := by sorry

Then if the user proves ∀ x : A, f x = g x as a DCC theorem,
then


Funext:

Theorem: If (h : (f x ≡ g x)), then f ≡ g

The proof strategy:
1. Assume the user has proven ∀ x : A, f x = g x as a DCC theorem
  - Note that a hole of shape A is the only inhabitant we need to check, since the only possible branching is destructing boxes &(x) or projecting couples, since we do not have inductives types
2. 


theorem funext (h_t_α : Judge α (DCC? Sort m)) (

Recall our definition of definitional equality

x →_β x₁   x₁ →_η B   y →_β y₁   y₁ →_η B
-----------------------------------------
                  x ≡ y

1. Suppose f : Π (x : A), B x and g : Π (x : A), B x
2. Suppose (f x) ≡ (g x)
  - Then, there exists x' such that (f x) →_β x'
  - and there exists y' such that (g x) →_β y'
  *note: but x' is not necessarily = y'
  - and there exists e' such that x' →_η e' and y' →_η e'
-/

/-def Canonicalize.ext
  (h_dom₁ : Domain f A)
  (h_dom₂ : Domain g A)
  (e_h    : Hole A n hole₁)
  (hn₁    : n > f.max_hole)
  (hn₂    : n > g.max_hole)
  (hrt₁   : RedAffNorm (DCC? (f hole₁)) ⟨x, hn_x⟩)
  (hrt₂   : RedAffNorm (DCC? (g hole₁)) ⟨x, hn_x⟩) : ∃ (h : GenericExpr τ_c), Canonicalize f h ∧ Canonicalize g h := by
  match hrt₁, hrt₂ with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ =>
    match hr₁.cases_head with
    | .inl h₁ =>
      match hr₂.cases_head with
      | .inl h₂ =>
        have h := h₁.trans h₂.symm
        cases h
        constructor
        · constructor <;> (
          apply Canonicalize.par
          any_goals (assumption)
          · exact ⟨.refl, h₂.symm ▸ hn₁⟩)
      | .inr ⟨_, hr₁, hr₂⟩ =>
        cases h₁
        constructor
        · constructor <;> (apply Canonicalize.par <;> assumption)
    | .inr ⟨_, ha, hb⟩ =>
      match hr₂.cases_head with
      | .inl h₂ =>
        cases h₂
        · constructor
          · constructor <;> (apply Canonicalize.par <;> assumption)
      | .inr ⟨_, hc, hd⟩ =>
        sorry-/
        /-cases ha with
        | eql =>
          cases hc with
          | eql =>
            · constructor
              · constructor
                · apply Canonicalize.par
                  any_goals (assumption)
                  exact ⟨.single (by constructor), by sorry⟩-/

end GenericExpr

/-
Invert hole. Instead of the hole being opaque, inject what the η-normal form is IN it inside the hole

hole(η-normal-form)

Dom(Fst(B)) = Coup(B)

Fst(B) ⟦B⟧(Fst(B), Snd(B))  
--------------------------------

η-reduction:

Dom(x) = A
hole(A) = y

(x y) -!> x'

But what about !(A)?

e.g., eta-reducing

Dom(f) = !(Coup(B))

Dom(B) = A
Hole(f) = &(⟦B⟧(Hole(A)

Hole(*<Fst(Id(Sort 1))>) = &(⟦Id(Sort 1)⟧(Fst(Id(Sort 1)), Snd(Id(Sort 1))))

*<Fst(Id(Sort 1))> &(⟦Id(Sort 1)⟧(Fst(Id(Sort 1)), Snd(Id(Sort 1)))) =

need to build up the trace going in

*<Fst(Id(Sort 1))> &(⟦Id(Sort 1)⟧(*<Fst(Id(Sort 1))>, *<Snd(Id(Sort 1))>))

the shape and the combinator inside must cancel out

&( *< cancel out

Kinda... this doens't explain

!<Fst(Id(Sort 1))>

I don't want to also need codomain

Coup example worked really well. that one is obvious.

scalding hot take:

pair and !Λ should be the only way to interact with boxes

that way we have a binary choice here

For one thing, unmap can be derived from pair.
Not particularly conveniently, but it can.

*<f> = ⟦?⟧⟨f, Λ(?, ?,

What about !<x>

maybe pure atomic should just be f? idk

less like just apply it the hole and more like apply it to the hole?

hole(Dom(f)) f = f'

so, clearly we can identify behavior of projections on couples.

Can we identify composition though?

Fst(B) ∘ Snd(C)

Fst(B) ⟦B⟧(Fst(B), Snd(B)) = Fst(B)

only shapes we really care about:

- fstc
- sndc
- fstc'
- sndc'
- eval (how will we handle this)
- par (how will we handle this)

oh wait interesting I think the nesting anyway gives

such that nested Coup hole is

⟦?⟧(

we need to slap on a comp for every layer it traverses

(f x) = (g x)

just plug the hole in

then we get η by default

this would be fucking sick. if only it worked

we don't actually want to refer to f. then f and g will just get f and g back out

wait thought

example:

Id(A) ∘' Id(A)

I like the probing, but it doesn't work with constant values.
That is fine, though.

I mean this is somewhat better than the current approach.

maybe we can make it work.

everything must have a canonical form.

everything.

why can't we do this by induction?

just go case by case and find an encoding.

Coup(B)

we can:
- discard (quot)
- project: fst / snd

Note: funext only really matters for unary apps. pretty sure.

because for combinators of arity 2, then (f x) = (g x) has no top-level step

so, narrow the search space to arity 1.

With Coup(B) we can:
- Fst / Snd
  - Need to handle composition as well,
    but only composition that isn't quote. quote overrides all
     -  pretty sure we just defer to the global comp for this
- Eval

With !(A) we can:
- Eql(B) &(env)
- !<x>
- $<x>
- *<x>
- ⟦B⟧⟨M, N⟩
  although this does not produce another function, so it falls under par I think
  keep it just to be safe ig
- !Λ(A, B, x) &(y)

Global moves:
- Id
- `(B, x)
- Λ(A, B, x) y
- Σ(B, C) where resulting Coup(τ) τ contains the hole
- x ∘ y, but this is inductive on y

Identity for each type of hole, distinct moves that produce distinct results
because this means (f x = g x) will force f = g

Par is just fallback ig
just make par more flexible but mutually exclusive

So what's the flow?

we need to cover each of these in canonicalize

Composition is basically the only recursive one. We just need every function to η-reduce.

This is easy just make par a fallback.

AppHole should not include Par

Par should be a fallback when no match triggers.

So AppHole only registers the valid moves, and if no valid move is found,
then Par. Boom. well. this is kinda just refl. a little.

Show that is Par triggers, then there is no head step on the next argument?
Then use that to show that congruence fires to show that f = g?
Yes.

So IsHead is good.

IsHead is basically just every possible top-level reduction

the issue with par is (par hole₁)

I don't think we even want (par hole₁).

This should be just be handled by a Refl,
or rather having no valid app recognizer.

AppHole I think is equivalent to just

| mk :

I also think we want just RedAff not RedAffNorm?
Because application with a Hole should always be able to make a step and shouldn't require mulitple steps anyway.
We should trans this instead with .comp methinks.
Or just recurse on ocmp.
-/
