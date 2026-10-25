import Dcc.Red.Rel
import Dcc.Red.Conf

namespace Expr

set_option maxHeartbeats 2000000 in
theorem semi_complete {A B : Expr} (hr : A.Red B) : ∃ B', ∃ (h : A.Red B'), (step? A) = .some ⟨B', ⟨h⟩⟩ := by
  unfold step?
  split
  case h_1 heq =>
    unfold step_head? at heq
    split at heq
    any_goals (grind)
  case h_2 heq_none =>
    split
    case h_1 =>
      split
      case h_1 =>
        cases hr
        any_goals (
          focus
          try (simp [step_head?] at heq_none)
          done)
        case point => grind
        case congrFun hr =>
          have ⟨B', hr', heq'⟩ := semi_complete hr
          exact ⟨_, .congrFun hr', by simp [heq']⟩
        case congrArg hr =>
          split
          case h_1 hr' heq' => exact ⟨_, .congrFun hr', rfl⟩
          case h_2 hr' heq' hn =>
            exact ⟨_, .congrArg hr', by simp⟩
          case h_3 =>
            have ⟨B', hr', heq'⟩ := semi_complete hr
            grind
      case h_2 =>
        cases hr
        any_goals (grind)
    case h_2 =>
      cases hr
      any_goals (grind)
      case point hn hr =>
        expose_names
        rw [heq] at hn
        match n with
        | 0 =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          exact ⟨_, .point 0 (by assumption) hr', by simp [heq']⟩
    case h_3 =>
      cases hr
      any_goals (grind)
      case point hn hr =>
        expose_names
        rw [heq] at hn
        match n with
        | 0 =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          exact ⟨_, .point 0 (by assumption) hr', by simp [heq']⟩
        | 1 =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          split
          case h_1 =>
            exact ⟨_, .point 0 (by grind) (by assumption), by simp_all⟩
          case h_2 =>
            exact ⟨_, .point 1 (by grind) (by assumption), by simp_all⟩
          · aesop
    case h_4 =>
      cases hr
      any_goals (grind)
      case point hn hr =>
        expose_names
        rw [heq] at hn
        match n with
        | 0 =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          exact ⟨_, .point 0 (by assumption) hr', by simp [heq']⟩
        | 1 =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          split
          case h_1 =>
            exact ⟨_, .point 0 (by grind) (by assumption), by simp_all⟩
          case h_2 =>
            exact ⟨_, .point 1 (by grind) (by assumption), by simp_all⟩
          case h_3 hn₁ hn₂ =>
            simp_all
            grind
        | 2 =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          split
          case h_1 => exact ⟨_, .point 0 (by grind) (by assumption), by simp_all⟩
          case h_2 => exact ⟨_, .point 1 (by grind) (by assumption), by simp_all⟩
          case h_3 => exact ⟨_, .point 2 (by grind) (by assumption), by simp_all⟩
    case h_5 =>
      cases hr
      case point hn hr =>
        expose_names
        rw [heq] at hn
        match n with
        | 0 =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          exact ⟨_, .point 0 (by assumption) hr', by simp [heq']⟩
        | 1 =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          split
          case h_1 =>
            exact ⟨_, .point 0 (by grind) (by assumption), by simp_all⟩
          case h_2 =>
            exact ⟨_, .point 1 (by grind) (by assumption), by simp_all⟩
          case h_3 hn₁ hn₂ =>
            simp_all
            grind
        | 2 =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          split
          case h_1 => exact ⟨_, .point 0 (by grind) (by assumption), by simp_all⟩
          case h_2 => exact ⟨_, .point 1 (by grind) (by assumption), by simp_all⟩
          case h_3 => exact ⟨_, .point 2 (by grind) (by assumption), by simp_all⟩
        | 3 =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          split
          case h_1 =>
            exact ⟨_, .point 0 (by grind) (by assumption), by simp_all⟩
          case h_2 =>
            exact ⟨_, .point 1 (by grind) (by assumption), by simp_all⟩
          case h_3 =>
            split
            case h_1 => exact ⟨_, .point 2 (by grind) (by assumption), by simp_all⟩
            case h_2 => exact ⟨_, .point 3 (by grind) (by assumption), by simp_all⟩
            case h_3 => simp_all; grind
      any_goals (
        focus
        try (
          dsimp [step_head?] at heq_none
          cases heq_none)
        done)
      any_goals (
        focus
        try (
          expose_names
          simp [point_arity] at heq))
termination_by (A.size, sizeOf A)
decreasing_by
  any_goals (grind)

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance Red.instSemicomplete : SemiComplete (Red) := ⟨semi_complete⟩

theorem aff_complete (h : Relation.ReflTransGen (Red) A B)
  (hn : IsNorm Red B) : reduce Red A = ⟨B, ⟨h⟩⟩ :=
  Red.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance instComplete : Complete (Relation.ReflTransGen (Red)) (P := IsNorm Red) := Red.instRedRel.instComplete

-- RedRel.reduce Size Red.instRedRel : (e : Expr) → (e' : Expr) × PULift (Relation.ReflTransGen Red e e')
#check reduce Red

/-
Complete.complete
  Id : ∀ (h : Relation.ReflTransGen Red ?m.8 ?m.9), IsNorm Red ?m.9 → Rel.run Id ?m.8 = pure ⟨?m.9, { down := h }⟩
-/
#check instComplete.complete

@[grind ., grind →]
theorem Red.decreasing' {A B : Expr} (h : Red A B) : size B < size A := Red.instRedRel.decreasing h

@[grind ., grind →]
theorem red_aff_decreasing? {A B : Expr} (h : Relation.ReflTransGen (Red) A B) : (size B) ≤ (size A) := by
  if hs : (size A) = (size B) then
    simp_all
  else
    rw [← Relation.reflGen_transGen] at h
    match h with
    | .refl => grind
    | .single h =>
      have hn' : B.size < A.size := Red.instRedRel.to_trans.decreasing h
      grind

@[grind ., grind →]
theorem red_aff_trans_decreasing {A B : Expr} : Relation.TransGen (Red) A B → (size B) < (size A) :=
  Red.instRedRel.to_trans.decreasing

@[dcc_force_reduce, dcc_force_aff]
abbrev Red.reduce := Expr.reduce (Red)

attribute [dcc_force_reduce, dcc_force_aff] Red.reduce.eq_def

instance Red.instDecidableNorm {A : Expr}  : Decidable (IsNorm Red A) :=
  match heq₀ : Expr.reduce Red A with
  | ⟨A', ⟨h⟩⟩ =>
    if heq : A' = A then
      have h_norm := reduce_norm (h := heq ▸ h) (A := A) (B := A) (hR := Red.instRedRel) (heq ▸ heq₀)
      .isTrue (fun ⟨a, b⟩ => by
        exact h_norm ⟨_, b⟩)
    else
      .isFalse (fun h => by
        have h := Red.instRedRel.reduce_norm_fst h
        simp_all)

@[dcc_judge]
def RedReflTrans := Relation.ReflTransGen (Red)

theorem RedReflTrans.reflGen_transGen : Relation.ReflGen (Relation.TransGen Red) = RedReflTrans :=
  Relation.reflGen_transGen

@[dcc_judge]
def RedTrans := Relation.TransGen (Red)

namespace RedTrans

def single (r : Red A B) : RedTrans A B := Relation.TransGen.single r

def trans (r₁ : RedTrans A B) (r₂ : RedTrans B C) : RedTrans A C := Relation.TransGen.trans r₁ r₂

def to_reflTrans {a b : Expr} (r : RedTrans a b) : RedReflTrans a b :=
  Relation.TransGen.to_reflTransGen (a := a) (b := b) r

end RedTrans

namespace RedReflTrans

def cases_head {a b : Expr} (r : RedReflTrans a b) :=
  Relation.ReflTransGen.cases_head (a := a) (b := b) r

def single {A B : Expr}
  (r : Red A B) : (RedReflTrans) A B := Relation.ReflTransGen.single r

def trans {A B C : Expr} (r₁ : RedReflTrans A B)
  (r₂ : RedReflTrans B C) : RedReflTrans A C := Relation.ReflTransGen.trans r₁ r₂

def conf {A B C : Expr} (h₁ : RedReflTrans A B) (h₂ : RedReflTrans A C) : ∃ D, RedReflTrans B D ∧ RedReflTrans C D := Red.instRedRel.globally_confluent.conf h₁ h₂

def elim_head_norm {A B : Expr} (h : RedReflTrans A B) (hn : IsNorm Red A) : A = B :=
  hn.unique_refl h

@[grind ., grind →]
theorem red_aff_decreasing? {A B : Expr} (h : (RedReflTrans) A B) : (size B) ≤ (size A) := by
  if hs : (size A) = (size B) then
    simp_all
  else
    rw [← reflGen_transGen] at h
    match h with
    | .refl => grind
    | .single h =>
      have hn' : B.size < A.size := Red.instRedRel.to_trans.decreasing h
      grind

def elim_norm (hr : RedReflTrans A B) (hn : IsNorm Red A) : A = B := by
  change Relation.ReflTransGen _ _ _ at hr
  exact hn.unique_refl hr

@[grind ., grind <=]
theorem elim_norm' (hr : RedReflTrans A B) (hn : IsNorm Red A) : A = B := by
  change Relation.ReflTransGen _ _ _ at hr
  exact hn.unique_refl hr

def push_head (hr₁ : RedReflTrans A C) (hn : IsNorm Red C) (hr₂ : Red A B) : RedReflTrans B C :=
  have ⟨_, h₁, h₂⟩ := Red.instRedRel.globally_confluent.conf hr₁ (.single hr₂)
  hn.unique_refl h₁ ▸ h₂

end RedReflTrans

namespace RedTrans

@[grind ., grind →]
theorem red_aff_trans_decreasing {A B : Expr} : (RedTrans) A B → (size B) < (size A) := by
  change Relation.TransGen _ _ _ → _
  exact (Red.instRedRel).to_trans.decreasing

end RedTrans

namespace Red

abbrev decreasing (x y : Expr) := (Red.instRedRel).decreasing (x := x) (y := y)

end Red

namespace RedReflTrans

def push_head' (hr₁ : RedReflTrans A C) (hn : IsNorm Red C) (hr₂ : RedReflTrans A B) : RedReflTrans B C := by
  have ⟨_, h₁, h₂⟩ := hr₁.conf hr₂
  have heq := hn.unique_refl h₁
  exact heq ▸ h₂

@[grind ., grind →]
theorem decreasing? {A B : Expr} (h : (RedReflTrans) A B) : (size B) ≤ (size A) := red_aff_decreasing? h

end RedReflTrans

inductive RedNorm : Expr → Expr → Type u
  | mk : (hr : RedReflTrans A B) → (hn : IsNorm Red B) → RedNorm A B
deriving DecidableEq, Repr

@[dcc_step]
def RedNorm.decreasing? (h : RedNorm A B) : B.size ≤ A.size :=
  match h with
  | ⟨hr, _hn⟩ => Expr.decreasing? _ hr

@[grind]
def RedNorm.raw (r : RedNorm A B) : NormExpr Red := ⟨B, r.2⟩

@[dcc_step]
def RedNorm.is_norm (r : RedNorm A B) : IsNorm Red B :=
  match r with
  | ⟨_ha, hb⟩ => hb

@[grind]
def aff_sound {A B : Expr} {h : Relation.ReflTransGen Red A B} (heq : reduce Red A = ⟨B, ⟨h⟩⟩) : RedNorm A B := ⟨reduce_sound heq, reduce_norm heq⟩

@[grind, dcc_force_reduce, aesop unsafe norm (rule_sets := [DccForceReduce])]
def aff_sound' (A : Expr) : RedNorm A (reduce Red A).fst := ⟨reduce_sound rfl, reduce_norm rfl⟩

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedNorm.complete {A B : Expr} (h : RedNorm A B) : (reduce Red A).fst = B :=
  match h with
  | ⟨hr, hn⟩ => by
    have ha := reduce_complete_fst hr hn
    simp [ha]

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedNorm.complete_fst {A : Expr} (h : RedNorm A B) : (reduce Red A).fst = B :=
  match h with
  | ⟨hr, hn⟩ => by
    have ha := reduce_complete_fst hr hn
    simp [ha]

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedNorm.complete_snd {A : Expr} (h : RedNorm A B) : (reduce Red A).snd = ⟨reduce_sound rfl⟩ :=
  match h with
  | ⟨hr, hn⟩ => by simp

@[dcc_reduce]
def RedNorm.eq {e : Expr} (hr : RedNorm e (reduce Red e).fst) : hr = aff_sound rfl :=
  match hr with
  | ⟨hr, hn⟩ => by
    have heq := reduce_complete hr hn
    grind

abbrev RedNorm.red (h : RedNorm A B) : RedReflTrans A B :=
  match h with
  | ⟨hr, _⟩ => hr

def RedNorm.aff_complete {A B : Expr} (h : RedNorm A B) : reduce Red A = ⟨B, ⟨h.red⟩⟩ :=
  match h with
  | ⟨hr₁, hn₁⟩ => reduce_complete hr₁ hn₁

def RedNorm.out_eq {A B : Expr} (h : RedNorm A B) : B = (reduce Red A).fst :=
  match h with
  | .mk hr hn => by
    have heq := reduce_complete hr hn
    aesop

@[ext]
def RedNorm.ext (h₁ h₂ : RedNorm A B) : h₁ = h₂ := by
  match h₁ with
  | ⟨hr₁, hn₁⟩ =>
    match h₂ with
    | ⟨hr₂, hn₂⟩ =>
      dcc_simp_all

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def RedNorm.unique {A : Expr} (h₁ : RedNorm A B) (h₂ : RedNorm A C) : B = C :=
  match h₁, h₂ with
  | ⟨ha, hb⟩, ⟨hc, hd⟩ => norm_unique ha hb hc hd

def RedNorm.heq (h₁ : RedNorm A B) (h₂ : RedNorm A C) : h₁ ≍ h₂ := by
  have heq := h₁.unique h₂
  cases h₁
  cases h₂
  congr!

@[macro_inline, dcc_size, aesop safe apply (rule_sets := [DccSize]) ]
def RedNorm.absurd {P : Sort v} {A : Expr} (h₁ : RedNorm A B) (h₂ : RedNorm A C) (hneq : B ≠ C := by intro h; cases h) : P :=
  _root_.absurd (h₁.unique h₂) (by simp_all)

def RedNorm.elim_norm (hr : RedNorm A B) (hn : IsNorm Red A) : B = A :=
  match hr with
  | ⟨hr, _hn⟩ => by
    have h := hn.unique_refl hr
    cases h
    grind

def RedNorm.push_head {A : Expr} (hrt : RedNorm A C) (hr : Red A B) : RedNorm B C :=
  match hrt with
  | ⟨hrt, hn⟩ => ⟨hrt.push_head hn hr, hn⟩

open Congruent in
def RedNorm.congrFun (hrt : RedNorm (DCC? (f x)) C) (hrt_f : RedNorm f f') : RedNorm (DCC? (f' x)) C :=
  match hrt, hrt_f with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, _hn₂⟩ =>
    ⟨
      have ⟨_, h₁, h₂⟩ := hr₁.conf (Congruent.congrFun' (hR := Red.instCongruent.reflTrans) hr₂)
      hn₁.unique_refl h₁ ▸ h₂, hn₁⟩

open Congruent in
def RedNorm.congrArg (hrt : RedNorm (DCC? (f x)) C) (hrt_x : RedNorm x x') : RedNorm (DCC? (f x')) C :=
  match hrt, hrt_x with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, _hn₂⟩ =>
    ⟨
      have ⟨_, h₁, h₂⟩ := hr₁.conf (Congruent.congrArg' (hR := Red.instCongruent.reflTrans) hr₂)
      hn₁.unique_refl h₁ ▸ h₂, hn₁⟩

namespace IsNorm

def map (h : IsNorm (Red) (.map f)) : IsNorm Red f :=
  fun ⟨_, hr⟩ => h ⟨_, .point 0 (by grind) hr⟩

def unbox (h : IsNorm (Red) (.unbox f)) : IsNorm Red f :=
  fun ⟨_, hr⟩ => h ⟨_, .point 0 (by grind) hr⟩

def box₀ (h : IsNorm Red (DCC? (& x))) : IsNorm Red x :=
  fun ⟨_, hr⟩ => h ⟨_, .point 0 (by grind) hr⟩

end IsNorm

def Red.elim_norm (hr : Red A B) (hn : IsNorm Red A) : False := by
  have h := hn.unique hr
  have h_dec := hr.decreasing
  grind

def Red.size_absurd (hr : Red A B) (h_size_eq : size A ≤ size B := by grind) : False := by
  have h_dec := hr.decreasing
  grind

end Expr
