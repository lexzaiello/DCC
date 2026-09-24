import Dcc.Aff.Rel
import Dcc.Aff.Conf

universe u
variable {τ : Type u} [DecidableEq τ]

namespace GenericExpr

set_option maxHeartbeats 10000000000 in
def semi_complete.{u} {τ : Type u} {A B : GenericExpr τ} (hr : A.RedAff B) : ∃ B', ∃ (h : A.RedAff B'), (step? A) = .some ⟨B', ⟨h⟩⟩ := by
  change ∃ _, ∃ _, (step? _) = .some _
  unfold step?
  split
  any_goals (
    focus
    try (
      split
      case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨0, by grind⟩), rfl⟩
      case h_2 hr' heq _ => exact ⟨_, hr'.mk_point (n := ⟨1, by grind⟩), rfl⟩
      case h_3 hn₁ hn₂ =>
        cases hr <;> (
          rename_i hr
          have ⟨_, hr'', heq⟩ := semi_complete hr
          grind))
    done)
  any_goals (exact ⟨_, by constructor, rfl⟩)
  any_goals (
    focus
    try (
      split
      case h_1 hr' heq =>
        exact ⟨_, hr'.mk_point (n := ⟨0, by grind⟩), rfl⟩
      case h_2 hn₁ hn₂ =>
        cases hr <;> (
          rename_i hr
          have ⟨_, hr'', heq⟩ := semi_complete hr
          grind))
    done)
  any_goals (
    focus
    try (
      split
      case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨1, by grind⟩), rfl⟩
      · split
        case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨0, by grind⟩), rfl⟩
        case h_2 hr' heq _ => exact ⟨_, hr'.mk_point (n := ⟨2, by grind⟩), rfl⟩
        case h_3 hn₁ hn₂ =>
          cases hr <;> (
            rename_i hr
            have ⟨_, hr'', heq⟩ := semi_complete hr
            grind))
    done)
  any_goals (
    focus
    try (
      split
      case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨0, by grind⟩), rfl⟩
      · split
        case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨1, by grind⟩), rfl⟩
        case h_2 hr' heq _ => exact ⟨_, hr'.mk_point (n := ⟨2, by grind⟩), rfl⟩
        case h_3 hn₁ hn₂ =>
          cases hr <;> (
            rename_i hr
            have ⟨_, hr'', heq⟩ := semi_complete hr
            grind))
    done)
  case h_38 =>
    cases hr
    <;> simp_all
    any_goals (grind)
    case congrFun hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      simp [heq]
      exact hr'.congrFun
    case congrArg hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      simp [heq]
      split
      · exact ⟨_, .congrFun (by assumption), rfl⟩
      · exact ⟨_, .congrArg (by assumption), rfl⟩
      · grind
  case h_60 =>
    simp_all
    cases hr
    any_goals (grind)
    case dom₀ hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      exact ⟨_, hr'.dom₀, by simp [heq]⟩
  case h_63 =>
    simp_all
    cases hr
    any_goals (grind)
    case uncoup₀ hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      exact ⟨_, hr'.uncoup₀, by simp [heq]⟩
  case h_64 =>
    simp_all
    cases hr
    any_goals (grind)
    case unbang₀ hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      exact ⟨_, hr'.unbang₀, by simp [heq]⟩
  case h_69 =>
    simp_all
    cases hr
    any_goals (grind)
    case dom₂₀ hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      exact ⟨_, hr'.dom₂₀, by simp [heq]⟩
  case h_70 =>
    simp_all
    cases hr
    any_goals (grind)

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance RedAff.instSemicomplete.{u} {τ : Type u} : SemiComplete (RedAff (τ := τ)) := ⟨semi_complete⟩

theorem aff_complete (h : Relation.ReflTransGen RedAff A B)
  (hn : IsNorm RedAff B) : reduce RedAff A = ⟨B, ⟨h⟩⟩ :=
  RedAff.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance instComplete.{u} {τ : Type u} : Complete (Relation.ReflTransGen (RedAff (τ := τ))) (P := IsNorm RedAff) := RedAff.instRedRel.instComplete

-- RedRel.reduce Size RedAff.instRedRel : (e : Expr) → (e' : Expr) × PULift (Relation.ReflTransGen RedAff e e')
#check reduce RedAff

/-
Complete.complete
  Id : ∀ (h : Relation.ReflTransGen RedAff ?m.8 ?m.9), IsNorm RedAff ?m.9 → Rel.run Id ?m.8 = pure ⟨?m.9, { down := h }⟩
-/
#check instComplete.complete

@[grind ., grind →]
theorem RedAff.decreasing' (h : RedAff A B) : size B < size A := by
  induction h <;> grind

@[grind ., grind →]
theorem red_aff_decreasing?.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] (h : Relation.ReflTransGen (RedAff (τ := τ)) A B) : (size B) ≤ (size A) := by
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
theorem red_aff_trans_decreasing.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] : Relation.TransGen (RedAff (τ := τ)) A B → (size B) < (size A) :=
  RedAff.instRedRel.to_trans.decreasing

@[dcc_force_reduce, dcc_force_aff]
abbrev RedAff.reduce.{u} {τ : Type u} := GenericExpr.reduce (RedAff (τ := τ))

attribute [dcc_force_reduce, dcc_force_aff] RedAff.reduce.eq_def

instance RedAff.instDecidableNorm.{u} {α : Type u} [DecidableEq α]
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
def RedAffReflTrans.{u} {τ : Type u} := Relation.ReflTransGen (RedAff (τ := τ))

theorem RedAffReflTrans.reflGen_transGen.{u} {τ : Type u} : Relation.ReflGen (Relation.TransGen RedAff) = RedAffReflTrans (τ := τ) :=
  Relation.reflGen_transGen

@[dcc_judge]
def RedAffTrans.{u} {τ : Type u} := Relation.TransGen (RedAff (τ := τ))

namespace RedAffTrans

def single (r : RedAff A B) : RedAffTrans A B := Relation.TransGen.single r

def trans (r₁ : RedAffTrans A B) (r₂ : RedAffTrans B C) : RedAffTrans A C := Relation.TransGen.trans r₁ r₂

def to_reflTrans {a b : Expr} (r : RedAffTrans a b) : RedAffReflTrans a b :=
  Relation.TransGen.to_reflTransGen (a := a) (b := b) r

end RedAffTrans

namespace RedAffReflTrans

def cases_head.{u} {τ : Type u} {a b : GenericExpr τ} (r : RedAffReflTrans a b) :=
  Relation.ReflTransGen.cases_head (a := a) (b := b) r

def single.{u} {τ : Type u} {A B : GenericExpr τ}
  (r : RedAff A B) : (RedAffReflTrans (τ := τ)) A B := Relation.ReflTransGen.single r

def trans.{u} {τ : Type u} {A B C : GenericExpr τ} (r₁ : RedAffReflTrans A B)
  (r₂ : RedAffReflTrans B C) : RedAffReflTrans A C := Relation.ReflTransGen.trans r₁ r₂

def conf.{u} {τ : Type u} {A B C : GenericExpr τ} (h₁ : RedAffReflTrans A B) (h₂ : RedAffReflTrans A C) : ∃ D, RedAffReflTrans B D ∧ RedAffReflTrans C D := RedAff.instRedRel.globally_confluent.conf h₁ h₂

def elim_head_norm.{u} {τ : Type u} {A B : GenericExpr τ} (h : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B :=
  hn.unique_refl h

@[grind ., grind →]
theorem red_aff_decreasing?.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] (h : (RedAffReflTrans (τ := τ)) A B) : (size B) ≤ (size A) := by
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

def push_head (hr₁ : RedAffReflTrans A C) (hn : IsNorm RedAff C) (hr₂ : RedAff A B) : RedAffReflTrans B C :=
  have ⟨_, h₁, h₂⟩ := RedAff.instRedRel.globally_confluent.conf hr₁ (.single hr₂)
  hn.unique_refl h₁ ▸ h₂

end RedAffReflTrans

namespace RedAffTrans

@[grind ., grind →]
theorem red_aff_trans_decreasing.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] : (RedAffTrans (τ := τ)) A B → (size B) < (size A) := by
  change Relation.TransGen _ _ _ → _
  exact (RedAff.instRedRel (τ := τ)).to_trans.decreasing

end RedAffTrans

namespace RedAff

abbrev decreasing.{u} {τ : Type u} (x y : GenericExpr τ) := (RedAff.instRedRel (τ := τ)).decreasing (x := x) (y := y)

end RedAff

namespace RedAffReflTrans

def push_head' (hr₁ : RedAffReflTrans A C) (hn : IsNorm RedAff C) (hr₂ : RedAffReflTrans A B) : RedAffReflTrans B C := by
  have ⟨_, h₁, h₂⟩ := hr₁.conf hr₂
  have heq := hn.unique_refl h₁
  exact heq ▸ h₂

@[grind ., grind →]
theorem decreasing?.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] (h : (RedAffReflTrans (τ := τ)) A B) : (size B) ≤ (size A) := red_aff_decreasing? h

end RedAffReflTrans

inductive RedAffNorm : GenericExpr τ → NormExpr (RedAff (τ := τ)) → Type u
  | mk : (hr : RedAffReflTrans A B) → (hn : IsNorm RedAff B) → RedAffNorm A ⟨B, hn⟩
deriving DecidableEq, Repr

@[dcc_step]
def RedAffNorm.decreasing? (h : RedAffNorm A B) : B.size ≤ A.size :=
  match h with
  | ⟨hr, _hn⟩ => GenericExpr.decreasing? _ hr

@[grind]
def RedAffNorm.raw (_r : RedAffNorm (τ := τ) A B) : NormExpr (RedAff (τ := τ)) := B

@[dcc_step]
def RedAffNorm.is_norm (r : RedAffNorm (τ := τ) A B) : IsNorm RedAff B.raw :=
  match r with
  | ⟨_ha, hb⟩ => hb

@[grind]
def aff_sound (heq : reduce RedAff A = ⟨B, ⟨h⟩⟩) : RedAffNorm A ⟨B, reduce_norm heq⟩ := ⟨reduce_sound heq, reduce_norm heq⟩

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
def RedAffNorm.eq (hr : RedAffNorm e (red_aff e)) : hr = aff_sound rfl :=
  match hr with
  | ⟨hr, hn⟩ => by
    have heq := reduce_complete hr hn
    grind

abbrev RedAffNorm.red (h : RedAffNorm A ⟨B, hn⟩) : RedAffReflTrans A B :=
  match h with
  | ⟨hr, _⟩ => hr

def RedAffNorm.aff_complete (h : RedAffNorm A ⟨B, hn⟩) : reduce RedAff A = ⟨B, ⟨h.red⟩⟩ :=
  match h with
  | ⟨hr₁, hn₁⟩ => reduce_complete hr₁ hn₁

def RedAffNorm.out_eq (h : RedAffNorm A B) : B = (red_aff A) :=
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
def RedAffNorm.unique (h₁ : RedAffNorm A B) (h₂ : RedAffNorm A C) : B = C :=
  match h₁, h₂ with
  | ⟨ha, hb⟩, ⟨hc, hd⟩ => NormExpr.ext (norm_unique ha hb hc hd)

@[macro_inline, dcc_size, aesop safe apply (rule_sets := [DccSize]) ]
def RedAffNorm.absurd {P : Sort v} (h₁ : RedAffNorm A B) (h₂ : RedAffNorm A C) (hneq : B ≠ C := by intro h; cases h) : P :=
  _root_.absurd (h₁.unique h₂) (by simp_all)

def RedAffNorm.elim_norm (hr : RedAffNorm A B) (hn : IsNorm RedAff A) : B = ⟨A, hn⟩ :=
  match hr with
  | ⟨hr, _hn⟩ => by
    have h := hn.unique_refl hr
    cases h
    grind

def RedAffNorm.push_head (hrt : RedAffNorm A C) (hr : RedAff A B) : RedAffNorm B C :=
  match hrt with
  | ⟨hrt, hn⟩ => ⟨hrt.push_head hn hr, hn⟩

open Congruent in
def RedAffNorm.congrFun (hrt : RedAffNorm (DCC? (f x)) C) (hrt_f : RedAffNorm f ⟨f', hn_f⟩) : RedAffNorm (DCC? (f' x)) C :=
  match hrt, hrt_f with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, _hn₂⟩ =>
    ⟨
      have ⟨_, h₁, h₂⟩ := hr₁.conf (Congruent.congrFun' (hR := RedAff.instCongruent.reflTrans) hr₂)
      hn₁.unique_refl h₁ ▸ h₂, hn₁⟩

open Congruent in
def RedAffNorm.congrArg (hrt : RedAffNorm (DCC? (f x)) C) (hrt_x : RedAffNorm x ⟨x', hn_f⟩) : RedAffNorm (DCC? (f x')) C :=
  match hrt, hrt_x with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, _hn₂⟩ =>
    ⟨
      have ⟨_, h₁, h₂⟩ := hr₁.conf (Congruent.congrArg' (hR := RedAff.instCongruent.reflTrans) hr₂)
      hn₁.unique_refl h₁ ▸ h₂, hn₁⟩

namespace IsNorm

def map (h : IsNorm RedAff (.map f)) : IsNorm RedAff f :=
  fun ⟨_, hr⟩ => h ⟨_, .map₀ hr⟩

def unbox (h : IsNorm RedAff (.unbox f)) : IsNorm RedAff f :=
  fun ⟨_, hr⟩ => h ⟨_, .unbox₀ hr⟩

def box₀ (h : IsNorm RedAff (DCC? (& x))) : IsNorm RedAff x :=
  fun ⟨_, hr⟩ => h ⟨_, .box₀ hr⟩

end IsNorm

def RedAff.elim_norm (hr : RedAff A B) (hn : IsNorm RedAff A) : False := by
  have h := hn.unique hr
  have h_dec := hr.decreasing
  grind

def RedAff.size_absurd (hr : RedAff A B) (h_size_eq : size A ≤ size B := by grind) : False := by
  have h_dec := hr.decreasing
  grind

end GenericExpr
