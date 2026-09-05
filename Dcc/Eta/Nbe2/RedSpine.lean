import Dcc.Aff.Red
import Dcc.Attrs

universe u
variable {τ_c : Type u}

namespace GenericExpr

/-
Possible unary head-level reductions. Otherwise,
no head-level step is made.
-/
@[grind, aesop safe (rule_sets := [DccRel]) [constructors], aesop safe (rule_sets := [DccRel]) [cases]]
inductive RedAff.IsHead : (hr : RedAff A B) → Type u
  | fstc  {B _B a b}     : IsHead (.fstc (_α := B) (β := _B) (a := a) (b := b))
  | sndc  {B _B a b}     : IsHead (.sndc (_α := B) (β := _B) (a := a) (b := b))
  | eval  {A B _B x y z} : IsHead (.evalc (_α := A) (_β := B) (x := x) (__β := _B) (y := y) (z := z))
  | eql   {B env x}      : IsHead (.eql (f_α := B) (env := env) (x := x))
  | map   {x y}          : IsHead (.map (f := x) (x := y))
  | fmap  {x y}          : IsHead (.fmap (f := x) (x := y))
  | unmap {x y}          : IsHead (.unmap (f := x) (x := y))
  | pair  {B x y z}      : IsHead (.pair (β := B) (M := x) (N := y) (x := z))
  | curr' {A B x y z}    : IsHead (.curr' (α := A) (β := B) (x := x) (y := y) (z := z))
  | id    {A x}          : IsHead (.id (α := A) (x := x))
  | quot  {B x y}        : IsHead (.quot (β := B) (x := x) (y := y))
  | curr  {A B x y z}    : IsHead (.curr (α := A) (β := B) (x := x) (y := y) (z := z))
  | sigma {B C x}        : IsHead (.sigma (f_α := B) (f_β := C) (env := x))
  /-
    Cases like Id(A) ∘ Fst(Id(A)) ⟦Id(A)⟧(x, y) = Id(A) (Fst(Id(A)) ⟦Id(A)⟧(x, y)) will get stuck
    due to lacking congruence, since we are specifically interested in head-reductions.

    Maybe?: have two variants of each comp where one checks (y z).IsNorm and one checks that there is a h : y z -> z' such that h.IsHead?
  -/
  | comp  {x y z}        : IsHead (.comp (x := x) (y := y) (z := z))
  | comp' {x y z}        : IsHead (.comp' (x := x) (y := y) (z := z))
  | comp₂ {x y z}        : IsHead (.comp₂ (x := x) (y := y) (z := z))
deriving Repr

@[aesop norm (rule_sets := [DccRel])]
def RedAff.IsHead.head {hr : RedAff A B} (hn : hr.IsHead) : Σ' f x, (hr' : PLift (RedAff (DCC? (f x)) B)) × (hn' : hr'.down.IsHead) × (PLift (hr ≍ hr'.down)) × (PLift (hn ≍ hn')) := by
  cases heq : hn <;> exact ⟨_, _, ⟨by constructor⟩, hn, ⟨by grind⟩, ⟨by grind⟩⟩

@[aesop safe destruct (rule_sets := [DccRel])]
def RedAff.IsHead.unique {hr₁ : RedAff A B} {hr₂ : RedAff A C} (hrt₁ : hr₁.IsHead) (hrt₂ : hr₂.IsHead) : B = C := by
  cases hrt₁ <;> (cases hrt₂; rfl)

@[aesop safe destruct (rule_sets := [DccRel])]
def RedAff.IsHead.eq {hr₁ : RedAff A B} {hr₂ : RedAff A B} (hrt₁ : hr₁.IsHead) (hrt₂ : hr₂.IsHead) : hrt₁ = hrt₂ := by
  cases hrt₁ <;> (cases hrt₂; rfl)

@[grind]
def NormHead (A : GenericExpr τ_c) := ∀ ⦃B⦄ ⦃hr : RedAff A B⦄ (_hrt : hr.IsHead), False

def NormHead.unique (h : NormHead A) (hr : RedAff A B) (hn : hr.IsHead) : A = B := by
  cases hn <;> exact (h (by constructor)).elim

def IsNorm.to_head (h : IsNorm RedAff x) : NormHead x := fun _ b _ => h ⟨_, b⟩

@[aesop norm (rule_sets := [DccRel])]
def red_spine? (A : GenericExpr τ_c) : Option ((B : GenericExpr τ_c) × (hr : PLift (RedAff A B)) × hr.down.IsHead) :=
  match A with
  | DCC? (Σ(_B, _C) _x) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (Eql(_B) &(_y) &(_z)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (!Λ(_A, _B, _x) &(_y) &(_z)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (Λ(_A, _B, _x) _y _z) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (`(_B, _x) _y) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (⟦_B⟧⟨_x, _y⟩ &(_z)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? ((_x ∘ _y) _z) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? ((_x ∘' _y) _z) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? ((_x ∘∘ _y) _z) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (*<_x> &(_y)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? ($<_x> &(_y)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (!<_x> &(_y)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (Eval(_A, _B, _x) ⟦_C⟧(_y, _z)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (Id(_A) _x) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (Fst(_B) ⟦__B⟧(_x, _y)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | DCC? (Snd(_B) ⟦__B⟧(_x, _y)) => .some ⟨_, ⟨by constructor⟩, by constructor⟩
  | _ => .none

@[grind ., grind =>, aesop safe forward (rule_sets := [DccRel])]
theorem RedAff.IsHead.complete {hr : RedAff A B} (hrt : hr.IsHead) : red_spine? A = .some ⟨B, ⟨hr⟩, hrt⟩ := by
  induction hr
  any_goals (
    focus
    try (simp [red_spine?])
    cases hrt
    try (rfl)
    done)
  case congrArg hr ih =>
    cases hrt <;> simp [red_spine?]

def RedAff.IsHead.decreasing {hr : RedAff A B} (_hrt : hr.IsHead) : B.size < A.size := hr.decreasing

inductive RedSpinePlus : GenericExpr τ_c → GenericExpr τ_c → Type u
  | single : (hr : RedAff A B) → (hrt : hr.IsHead) → RedSpinePlus A B
  | head   : (hr : RedAff A B) → (hrt : hr.IsHead) → (hrt₂ : RedSpinePlus B C) → RedSpinePlus A C
deriving Repr

@[grind]
def RedSpinePlus.length (h : RedSpinePlus A B) : ℕ :=
  match h with
  | .single _ _ => 1
  | .head _ _ xs => xs.length.succ

@[grind .]
theorem RedSpinePlus.ar_pos (h : RedSpinePlus A B) : 0 < h.length := by
  cases h <;> grind

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

def RedSpinePlus.elim_norm' (hrt : RedSpinePlus A B) (hn : IsNorm RedAff A) : A = B := hrt.elim_norm hn.to_head

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

@[aesop safe forward (rule_sets := [DccRel])]
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

@[aesop safe forward (rule_sets := [DccSize])]
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

inductive RedSpineStar : GenericExpr τ_c → GenericExpr τ_c → Type u
  | mk₁  : RedSpinePlus A B → RedSpineStar A B
  | refl : RedSpineStar A A
deriving Repr

@[grind]
def RedSpineStar.length (h : RedSpineStar A B) : ℕ :=
  match h with
  | .refl => 0
  | .mk₁ h => h.length

def RedSpineStar.elim_norm (h : RedSpineStar A B) (hn : NormHead A) : A = B :=
  match h with
  | .refl => rfl
  | .mk₁ (.head ha _hb hc) => (hn.unique ha (by assumption) ▸ hc).elim_norm hn
  | .mk₁ (.single ha hb) => hn.unique ha (by assumption)

def RedSpineStar.elim_norm' (h : RedSpineStar A B) (hn : IsNorm RedAff A) : A = B := h.elim_norm hn.to_head

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

@[inline, aesop safe norm (rule_sets := [DccRel])]
def RedSpinePlus.pop_head {A C : GenericExpr τ_c} (h : RedSpinePlus A C) : ((B : GenericExpr τ_c) × (_hrt : RedSpineStar B C) × (hr : PLift (RedAff A B)) × hr.down.IsHead) :=
  match h with
  | .single hr hn =>
    ⟨_, .refl, ⟨hr⟩, hn⟩
  | head ha hb hc => ⟨_, .mk₁ hc, ⟨ha⟩, hb⟩

@[dcc_size]
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
deriving Repr

def RedSpineNorm.decreasing (h : RedSpineNorm A B) : B.size < A.size :=
  match h with
  | ⟨hr, _hn⟩ => hr.decreasing

@[grind]
def red_spine!! (A : GenericExpr τ_c) : Option ((B : GenericExpr τ_c) × RedSpineNorm A B) :=
  match heq : A.red_spine! with
  | .some ⟨B, h⟩ => .some ⟨B, ⟨h, red_spine!_norm heq⟩⟩
  | .none => .none

@[aesop safe forward (rule_sets := [DccRel])]
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

@[inline]
def RedSpineNorm.tail {A C : GenericExpr τ_c} (h : RedSpineNorm A C) : ((B : GenericExpr τ_c) × (hr : PLift (RedAff B C)) × hr.down.IsHead) :=
  match h with
  | ⟨hr, _hn⟩ =>
    have ⟨B, _hrt, ⟨hr⟩, hn⟩ := hr.tail
    ⟨B, ⟨hr⟩, hn⟩

@[inline, aesop safe norm (rule_sets := [DccRel])]
def RedSpineNorm.head {A C : GenericExpr τ_c} (h : RedSpineNorm A C) : ((B : GenericExpr τ_c) × (hr : PLift (RedAff A B)) × hr.down.IsHead) :=
  match h with
  | ⟨.single ha hb, _hn⟩ =>
    ⟨_, ⟨ha⟩, hb⟩
  | ⟨.head ha hb _hc, _hn⟩ =>
    ⟨_, ⟨ha⟩, hb⟩

@[inline]
def RedSpineNorm.head_rest {A C : GenericExpr τ_c} (h : RedSpineNorm A C) : RedSpineStar h.head.fst C :=
  match h with
  | ⟨.single ha hb, _hn⟩ => .refl
  | ⟨.head ha hb _hc, _hn⟩ => by
    simp [head]
    constructor; assumption

@[dcc_size]
def RedSpineNorm.max_hole_preserved (h : RedSpineNorm A B) : max_hole B ≤ max_hole A :=
  match h with
  | ⟨hrt, _⟩ => hrt.max_hole_preserved

def RedSpineStar.max_hole_preserved (h : RedSpineStar A B) : max_hole B ≤ max_hole A :=
  match h with
  | .refl => by grind
  | .mk₁ h => h.max_hole_preserved

def RedSpineNorm.push_head (h : RedSpineNorm A C) (hr : RedAff A B) (hn : hr.IsHead) : RedSpineStar B C × (PLift (C.NormHead)) :=
  match h with
  | ⟨.single ha hb, hn'⟩ => by
    cases hn.unique hb
    exact ⟨.refl, ⟨hn'⟩⟩
  | ⟨.head ha hb hc, hn'⟩ => by
    cases hn.unique hb
    exact ⟨.mk₁ hc, ⟨hn'⟩⟩

def RedSpineNorm.elim_norm_flse (h : RedSpineNorm A B) (hn : NormHead A) : False :=
  match h with
  | ⟨hr, _hn⟩ => by
    have h_dec := h.decreasing
    have h := hr.elim_norm hn
    grind

@[grind]
def RedSpineNorm.length (h : RedSpineNorm A B) : ℕ :=
  match h with
  | ⟨hr, _⟩ => hr.length

@[grind .]
theorem RedSpineNorm.ar_pos (h : RedSpinePlus A B) : 0 < h.length := by
  cases h <;> grind

end GenericExpr
