import Dcc.Aff.Rel
import Dcc.Aff.Conf

universe u
variable {τ : Type u} [DecidableEq τ]

namespace GenericExpr

set_option maxHeartbeats 2000000 in
theorem semi_complete {A B : GenericExpr τ} (hr : A.RedAff B) : ∃ B', ∃ (h : A.RedAff B'), (step? A) = .some ⟨B', ⟨h⟩⟩ := by
  unfold step?
  split
  case h_1 heq =>
    unfold step_head? at heq
    split at heq
    any_goals (grind)
    case h_9 =>
      expose_names
      split at heq
      case isTrue heq_A =>
        cases heq_A
        grind
      case isFalse =>
        split at heq <;> grind
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
      case h_2 heq_arr hn =>
        cases hr
        any_goals (grind)
        any_goals (
          focus
          try (simp [step_head?] at heq_none)
          done)
        case dom₀ hr =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          exact ⟨_, .dom₀ hr', by simp [heq']⟩
      case h_3 heq_ar =>
        cases hr
        any_goals (grind)
        any_goals (
          focus
          try (simp [step_head?] at heq_none)
          done)
        case dom₂₀ hr =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          exact ⟨_, .dom₂₀ hr', by simp [heq']⟩
      case h_4 heq_ar =>
        cases hr
        any_goals (grind)
        any_goals (
          focus
          try (simp [step_head?] at heq_none)
          done)
        case uncoup₀ hr =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          exact ⟨_, .uncoup₀ hr', by simp [heq']⟩
      case h_5 heq_ar =>
        cases hr
        any_goals (grind)
        any_goals (
          focus
          try (simp [step_head?] at heq_none)
          done)
        case unbang₀ hr =>
          have ⟨x', hr', heq'⟩ := semi_complete hr
          exact ⟨_, .unbang₀ hr', by simp [heq']⟩
      case h_6 =>
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
          simp [point_arity] at heq)
        done)
      case unif_refl =>
        unfold step_head? at heq_none
        simp at heq_none
termination_by (A.size, sizeOf A)
decreasing_by
  any_goals (grind)

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance RedAff.instSemicomplete : SemiComplete (RedAff (τ := τ)) := ⟨semi_complete⟩

theorem aff_complete (h : Relation.ReflTransGen (RedAff (τ := τ)) A B)
  (hn : IsNorm RedAff B) : reduce RedAff A = ⟨B, ⟨h⟩⟩ :=
  RedAff.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance instComplete : Complete (Relation.ReflTransGen (RedAff (τ := τ))) (P := IsNorm RedAff) := RedAff.instRedRel.instComplete

-- RedRel.reduce Size RedAff.instRedRel : (e : Expr) → (e' : Expr) × PULift (Relation.ReflTransGen RedAff e e')
#check reduce RedAff

/-
Complete.complete
  Id : ∀ (h : Relation.ReflTransGen RedAff ?m.8 ?m.9), IsNorm RedAff ?m.9 → Rel.run Id ?m.8 = pure ⟨?m.9, { down := h }⟩
-/
#check instComplete.complete

@[grind ., grind →]
theorem RedAff.decreasing' {A B : GenericExpr τ} (h : RedAff A B) : size B < size A := RedAff.instRedRel.decreasing h

@[grind ., grind →]
theorem red_aff_decreasing? {A B : GenericExpr τ} (h : Relation.ReflTransGen (RedAff (τ := τ)) A B) : (size B) ≤ (size A) := by
  if hs : (size A) = (size B) then
    simp_all
  else
    rw [← Relation.reflGen_transGen] at h
    match h with
    | .refl => grind
    | .single h =>
      have hn' : B.size < A.size := RedAff.instRedRel.to_trans.decreasing h
      grind

@[grind ., grind →]
theorem red_aff_trans_decreasing {A B : GenericExpr τ} : Relation.TransGen (RedAff (τ := τ)) A B → (size B) < (size A) :=
  RedAff.instRedRel.to_trans.decreasing

@[dcc_force_reduce, dcc_force_aff]
abbrev RedAff.reduce := GenericExpr.reduce (RedAff (τ := τ))

attribute [dcc_force_reduce, dcc_force_aff] RedAff.reduce.eq_def

instance RedAff.instDecidableNorm [DecidableEq α]
{A : GenericExpr α}  : Decidable (IsNorm (RedAff (τ := α)) A) :=
  match heq₀ : GenericExpr.reduce RedAff A with
  | ⟨A', ⟨h⟩⟩ =>
    if heq : A' = A then
      have h_norm := reduce_norm (h := heq ▸ h) (A := A) (B := A) (hR := RedAff.instRedRel) (heq ▸ heq₀)
      .isTrue (fun ⟨a, b⟩ => by
        exact h_norm ⟨_, b⟩)
    else
      .isFalse (fun h => by
        have h := RedAff.instRedRel.reduce_norm_fst h
        simp_all)

@[dcc_judge]
def RedAffReflTrans := Relation.ReflTransGen (RedAff (τ := τ))

theorem RedAffReflTrans.reflGen_transGen : Relation.ReflGen (Relation.TransGen (RedAff (τ := τ_c))) = RedAffReflTrans (τ := τ_c) :=
  Relation.reflGen_transGen

@[dcc_judge]
def RedAffTrans := Relation.TransGen (RedAff (τ := τ))

namespace RedAffTrans

def single (r : RedAff A B) : RedAffTrans A B := Relation.TransGen.single r

def trans (r₁ : RedAffTrans A B) (r₂ : RedAffTrans B C) : RedAffTrans A C := Relation.TransGen.trans r₁ r₂

def to_reflTrans {a b : Expr} (r : RedAffTrans a b) : RedAffReflTrans a b :=
  Relation.TransGen.to_reflTransGen (a := a) (b := b) r

end RedAffTrans

namespace RedAffReflTrans

def cases_head {a b : GenericExpr τ} (r : RedAffReflTrans a b) :=
  Relation.ReflTransGen.cases_head (a := a) (b := b) r

def single {A B : GenericExpr τ}
  (r : RedAff A B) : (RedAffReflTrans (τ := τ)) A B := Relation.ReflTransGen.single r

def trans {A B C : GenericExpr τ} (r₁ : RedAffReflTrans A B)
  (r₂ : RedAffReflTrans B C) : RedAffReflTrans A C := Relation.ReflTransGen.trans r₁ r₂

def conf {A B C : GenericExpr τ} (h₁ : RedAffReflTrans A B) (h₂ : RedAffReflTrans A C) : ∃ D, RedAffReflTrans B D ∧ RedAffReflTrans C D := RedAff.instRedRel.globally_confluent.conf h₁ h₂

def elim_head_norm {A B : GenericExpr τ} (h : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B :=
  hn.unique_refl h

@[grind ., grind →]
theorem red_aff_decreasing? {A B : GenericExpr τ} (h : (RedAffReflTrans (τ := τ)) A B) : (size B) ≤ (size A) := by
  if hs : (size A) = (size B) then
    simp_all
  else
    rw [← reflGen_transGen] at h
    match h with
    | .refl => grind
    | .single h =>
      have hn' : B.size < A.size := RedAff.instRedRel.to_trans.decreasing h
      grind

def elim_norm (hr : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B := by
  change Relation.ReflTransGen _ _ _ at hr
  exact hn.unique_refl hr

@[grind ., grind <=]
theorem elim_norm' (hr : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B := by
  change Relation.ReflTransGen _ _ _ at hr
  exact hn.unique_refl hr

def push_head (hr₁ : RedAffReflTrans (τ := τ) A C) (hn : IsNorm RedAff C) (hr₂ : RedAff A B) : RedAffReflTrans B C :=
  have ⟨_, h₁, h₂⟩ := RedAff.instRedRel.globally_confluent.conf hr₁ (.single hr₂)
  hn.unique_refl h₁ ▸ h₂

end RedAffReflTrans

namespace RedAffTrans

@[grind ., grind →]
theorem red_aff_trans_decreasing {A B : GenericExpr τ} : (RedAffTrans (τ := τ)) A B → (size B) < (size A) := by
  change Relation.TransGen _ _ _ → _
  exact (RedAff.instRedRel (τ := τ)).to_trans.decreasing

end RedAffTrans

namespace RedAff

abbrev decreasing (x y : GenericExpr τ) := (RedAff.instRedRel (τ := τ)).decreasing (x := x) (y := y)

end RedAff

namespace RedAffReflTrans

def push_head' (hr₁ : RedAffReflTrans (τ := τ) A C) (hn : IsNorm RedAff C) (hr₂ : RedAffReflTrans A B) : RedAffReflTrans B C := by
  have ⟨_, h₁, h₂⟩ := hr₁.conf hr₂
  have heq := hn.unique_refl h₁
  exact heq ▸ h₂

@[grind ., grind →]
theorem decreasing? {A B : GenericExpr τ} (h : (RedAffReflTrans (τ := τ)) A B) : (size B) ≤ (size A) := red_aff_decreasing? h

end RedAffReflTrans

inductive RedAffNorm : GenericExpr τ → NormExpr (RedAff (τ := τ)) → Type u
  | mk : (hr : RedAffReflTrans A B) → (hn : IsNorm RedAff B) → RedAffNorm A ⟨B, hn⟩
deriving DecidableEq, Repr

@[dcc_step]
def RedAffNorm.decreasing? (h : RedAffNorm (τ := τ) A B) : B.size ≤ A.size :=
  match h with
  | ⟨hr, _hn⟩ => GenericExpr.decreasing? _ hr

@[grind]
def RedAffNorm.raw (_r : RedAffNorm (τ := τ) A B) : NormExpr (RedAff (τ := τ)) := B

@[dcc_step]
def RedAffNorm.is_norm (r : RedAffNorm (τ := τ) A B) : IsNorm RedAff B.raw :=
  match r with
  | ⟨_ha, hb⟩ => hb

@[grind]
def aff_sound {A B : GenericExpr τ} {h : Relation.ReflTransGen RedAff A B} (heq : reduce RedAff A = ⟨B, ⟨h⟩⟩) : RedAffNorm A ⟨B, reduce_norm heq⟩ := ⟨reduce_sound heq, reduce_norm heq⟩

@[grind, dcc_force_reduce, aesop unsafe norm (rule_sets := [DccForceReduce])]
def aff_sound' (A : GenericExpr τ) : RedAffNorm A ⟨(reduce RedAff A).fst, reduce_norm rfl⟩ := ⟨reduce_sound rfl, reduce_norm rfl⟩

@[grind, inline, dcc_reduce]
def red_aff (A : GenericExpr τ) : NormExpr (RedAff (τ := τ)) := ⟨(reduce RedAff A).fst, reduce_norm (A := A) rfl⟩

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedAffNorm.complete {A : GenericExpr τ} {B : NormExpr RedAff (τ := τ)} (h : RedAffNorm A B) : red_aff A = B :=
  match h with
  | ⟨hr, hn⟩ => by
    have ha := reduce_complete_fst hr hn
    simp [red_aff, ha]

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedAffNorm.complete_fst {A : GenericExpr τ} (h : RedAffNorm A ⟨B, hn_B⟩) : (reduce RedAff A).fst = B :=
  match h with
  | ⟨hr, hn⟩ => by
    have ha := reduce_complete_fst hr hn
    simp [ha]

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedAffNorm.complete_snd {A : GenericExpr τ} (h : RedAffNorm A ⟨B, hn_B⟩) : (reduce RedAff A).snd = ⟨reduce_sound rfl⟩ :=
  match h with
  | ⟨hr, hn⟩ => by simp

@[dcc_reduce]
def RedAffNorm.eq {e : GenericExpr τ} (hr : RedAffNorm e (red_aff e)) : hr = aff_sound rfl :=
  match hr with
  | ⟨hr, hn⟩ => by
    have heq := reduce_complete hr hn
    grind

abbrev RedAffNorm.red (h : RedAffNorm A ⟨B, hn⟩) : RedAffReflTrans A B :=
  match h with
  | ⟨hr, _⟩ => hr

def RedAffNorm.aff_complete {A B : GenericExpr τ} {hn : IsNorm RedAff B} (h : RedAffNorm A ⟨B, hn⟩) : reduce RedAff A = ⟨B, ⟨h.red⟩⟩ :=
  match h with
  | ⟨hr₁, hn₁⟩ => reduce_complete hr₁ hn₁

def RedAffNorm.out_eq {A : GenericExpr τ} (h : RedAffNorm A B) : B = (red_aff A) :=
  match h with
  | .mk hr hn => by
    have heq := reduce_complete hr hn
    rw [red_aff]
    aesop

@[ext]
def RedAffNorm.ext (h₁ h₂ : RedAffNorm A B) : h₁ = h₂ := by
  match h₁ with
  | ⟨hr₁, hn₁⟩ =>
    match h₂ with
    | ⟨hr₂, hn₂⟩ =>
      dcc_simp_all

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def RedAffNorm.unique {A : GenericExpr τ} (h₁ : RedAffNorm A B) (h₂ : RedAffNorm A C) : B = C :=
  match h₁, h₂ with
  | ⟨ha, hb⟩, ⟨hc, hd⟩ => NormExpr.ext (norm_unique ha hb hc hd)

@[macro_inline, dcc_size, aesop safe apply (rule_sets := [DccSize]) ]
def RedAffNorm.absurd {P : Sort v} {A : GenericExpr τ} (h₁ : RedAffNorm A B) (h₂ : RedAffNorm A C) (hneq : B ≠ C := by intro h; cases h) : P :=
  _root_.absurd (h₁.unique h₂) (by simp_all)

def RedAffNorm.elim_norm (hr : RedAffNorm A B) (hn : IsNorm RedAff A) : B = ⟨A, hn⟩ :=
  match hr with
  | ⟨hr, _hn⟩ => by
    have h := hn.unique_refl hr
    cases h
    grind

def RedAffNorm.push_head {A : GenericExpr τ} (hrt : RedAffNorm A C) (hr : RedAff A B) : RedAffNorm B C :=
  match hrt with
  | ⟨hrt, hn⟩ => ⟨hrt.push_head hn hr, hn⟩

open Congruent in
def RedAffNorm.congrFun (hrt : RedAffNorm (τ := τ) (DCC? (f x)) C) (hrt_f : RedAffNorm f ⟨f', hn_f⟩) : RedAffNorm (DCC? (f' x)) C :=
  match hrt, hrt_f with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, _hn₂⟩ =>
    ⟨
      have ⟨_, h₁, h₂⟩ := hr₁.conf (Congruent.congrFun' (hR := RedAff.instCongruent.reflTrans) hr₂)
      hn₁.unique_refl h₁ ▸ h₂, hn₁⟩

open Congruent in
def RedAffNorm.congrArg (hrt : RedAffNorm (τ := τ) (DCC? (f x)) C) (hrt_x : RedAffNorm x ⟨x', hn_f⟩) : RedAffNorm (DCC? (f x')) C :=
  match hrt, hrt_x with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, _hn₂⟩ =>
    ⟨
      have ⟨_, h₁, h₂⟩ := hr₁.conf (Congruent.congrArg' (hR := RedAff.instCongruent.reflTrans) hr₂)
      hn₁.unique_refl h₁ ▸ h₂, hn₁⟩

namespace IsNorm

def map (h : IsNorm (RedAff (τ := τ)) (.map f)) : IsNorm RedAff f :=
  fun ⟨_, hr⟩ => h ⟨_, .point 0 (by grind) hr⟩

def unbox (h : IsNorm (RedAff (τ := τ)) (.unbox f)) : IsNorm RedAff f :=
  fun ⟨_, hr⟩ => h ⟨_, .point 0 (by grind) hr⟩

def box₀ (h : IsNorm RedAff (DCC? (& x))) : IsNorm RedAff x :=
  fun ⟨_, hr⟩ => h ⟨_, .point 0 (by grind) hr⟩

end IsNorm

def RedAff.elim_norm (hr : RedAff (τ := τ) A B) (hn : IsNorm RedAff A) : False := by
  have h := hn.unique hr
  have h_dec := hr.decreasing
  grind

def RedAff.size_absurd (hr : RedAff (τ := τ) A B) (h_size_eq : size A ≤ size B := by grind) : False := by
  have h_dec := hr.decreasing
  grind

end GenericExpr
