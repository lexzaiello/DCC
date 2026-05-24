import Dcc.Attrs
import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Size

namespace Expr

inductive RedAff : Expr → Expr → Prop
  | quot     : RedAff (DCC (`(β, x) y)) x
  | id       : RedAff (DCC (Id(α) x)) x
  | fstc     : RedAff (DCC (Fstc(_α) ⟦β⟧(a, b))) a
  | sndc     : RedAff (DCC (Sndc(_α) ⟦β⟧(a, b))) b
  | comp'    : RedAff (DCC ((x ∘' y) z)) (DCC (x (y z)))
  | comp     : RedAff (DCC ((x ∘ y) z)) (DCC (x (y z)))
  | curr     : RedAff (DCC (Λ(α, β, x) y z)) (DCC (x ⟦β⟧(y, z)))
  | sigl     : RedAff x x' → RedAff (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x', y))
  | sigr     : RedAff y y' → RedAff (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x, y'))
  | sigma    : RedAff (DCC (Σ(f_α, f_β) env)) (DCC (Coup((f_β env))))
  | coup     : RedAff β β' → RedAff (DCC (Coup(β))) (DCC (Coup(β')))
  | congrFun : RedAff f f' → RedAff (DCC (f x)) (DCC (f' x))
  | congrArg : RedAff x x' → RedAff (DCC (f x)) (DCC (f x'))

@[dcc_force_reduce, dcc_force_aff]
def step? (e : Expr) : Option ((e' : Expr) × (PULift.{1, 0} (RedAff e e'))) :=
  match e with
  | (DCC (`(_β, _x) _y))                             => .some ⟨_, ⟨.quot⟩⟩
  | (DCC (Id(_α) _x))                                => .some ⟨_, ⟨.id⟩⟩
  | (DCC (Fstc(_α) ⟦_γ⟧(_a, _b)))                    => .some ⟨_, ⟨.fstc⟩⟩
  | (DCC (Sndc(_α) ⟦_γ⟧(_a, _b)))                    => .some ⟨_, ⟨.sndc⟩⟩
  | (DCC ((x ∘' y) z))                               => .some ⟨(DCC (x (y z))), ⟨.comp'⟩⟩
  | (DCC ((x ∘ y) z))                                => .some ⟨(DCC (x (y z))), ⟨.comp⟩⟩
  | (DCC (Λ(_α, β, x) y z))                          => .some ⟨(DCC (x ⟦β⟧(y, z))), ⟨.curr⟩⟩
  | (DCC (Σ(_f_α, _f_β) _env))                       => .some ⟨_, ⟨.sigma⟩⟩
  | DCC ⟦β⟧(x, y) =>
    match x.step?, y.step? with
    | .some ⟨x', ⟨h₁⟩⟩, _ => .some ⟨(DCC ⟦β⟧(x', y)), ⟨.sigl h₁⟩⟩
    | _, .some ⟨y', ⟨h₁⟩⟩ => .some ⟨(DCC ⟦β⟧(x, y')), ⟨.sigr h₁⟩⟩
    | _, _ => .none
  | (DCC (Coup(β))) =>
    match β.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.coup h⟩⟩
    | _ => .none
  | DCC (f x) =>
    match f.step?, x.step? with
    | .some ⟨f', ⟨h₁⟩⟩, _ => .some ⟨(DCC (f' x)), ⟨.congrFun h₁⟩⟩
    | _, .some ⟨x', ⟨h₁⟩⟩ => .some ⟨(DCC (f x')), ⟨.congrArg h₁⟩⟩
    | _, _ => .none
  | _ => .none

@[dcc_force_reduce, dcc_force_aff]
instance RedAff.instRedRel : RedRel RedAff size where
  run := step?

theorem red_aff_sn : ∀ (e : Expr), Acc (fun b a => RedAff a b) e := RedAff.instRedRel.sn

theorem red_aff_trans_sn : ∀ (e : Expr), Acc (fun b a => Relation.TransGen RedAff a b) e := RedAff.instRedRel.to_trans.sn

instance RedAff.instCongruent : Congruent RedAff where

open Congruent in @[dcc_reduce, aesop safe apply (rule_sets := [DccReduce])] theorem RedAff.conf (h₁ : RedAff A B) (h₂ : RedAff A C) : ∃ D, RedAff.instRedRel.ReflTrans B D ∧ RedAff.instRedRel.ReflTrans C D := by
  induction h₁ generalizing C with
  | sigma =>
    cases h₂ with
    | sigma => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single (.coup (.congrArg h)), .single .sigma⟩
  | coup hr₁ ih =>
    cases h₂ with
    | coup hr₂ =>
      have ⟨_, ha, hb⟩ := ih hr₂
      exact ⟨_, coup' ha, coup' hb⟩
  | quot =>
    cases h₂ with
    | quot => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .refl, .single .quot⟩
  | id =>
    cases h₂ with
    | id => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single h, .single .id⟩
  | sigl h ih =>
    cases h₂ with
    | sigl h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, sigl' h₁, sigl' h₂⟩
    | sigr h =>
      exact ⟨_, .single (.sigr h), .single (.sigl (by assumption))⟩
  | sigr h ih =>
    cases h₂ with
    | sigl h =>
      exact ⟨_, .single (.sigl h), .single (.sigr (by assumption))⟩
    | sigr h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, sigr' h₁, sigr' h₂⟩
  | fstc =>
    cases h₂ with
    | fstc => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => cases h with
      | sigl h => exact ⟨_, .single h, .single .fstc⟩
      | sigr h => exact ⟨_, .refl, .single .fstc⟩
  | sndc =>
    cases h₂ with
    | sndc => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => cases h with
      | sigl h => exact ⟨_, .refl, .single .sndc⟩
      | sigr h => exact ⟨_, .single h, .single .sndc⟩
  | comp =>
    cases h₂ with
    | comp => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single (.congrArg (.congrArg (by assumption))), .single .comp⟩
  | comp' =>
    cases h₂ with
    | comp' => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single (.congrArg (.congrArg (by assumption))), .single .comp'⟩
  | curr =>
    cases h₂ with
    | curr => exact ⟨_, .refl, .refl⟩
    | congrFun h =>
      cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single (.congrArg (.sigl h)), .single .curr⟩
    | congrArg h => exact ⟨_, .single (.congrArg (.sigr (by assumption))), .single .curr⟩
  | congrFun h_r ih =>
    cases h₂
    case sigma => cases h_r
    case fstc =>
      cases h_r
    case sndc =>
      cases h_r
    case comp' | quot | id | comp => cases h_r
    case curr =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .curr, .single (.congrArg (.sigl (by assumption)))⟩
    case congrFun f f' x f'' h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, congrFun' h₁, congrFun' h₂⟩
    case congrArg f f' x x'' h_x =>
      exact ⟨_, congrArg' (.single h_x), congrFun' (.single h_r)⟩
  | congrArg h_r ih =>
    cases h₂ with
    | fstc => cases h_r with
      | sigl h => exact ⟨_, .single .fstc, .single h⟩
      | sigr h => exact ⟨_, .single .fstc, .refl⟩
    | sndc => cases h_r with
      | sigl h => exact ⟨_, .single .sndc, .refl⟩
      | sigr h => exact ⟨_, .single .sndc, .single h⟩
    | quot => exact ⟨_, .single .quot, .refl⟩
    | id => exact ⟨_, .single .id, .single h_r⟩
    | comp  => exact ⟨_, .single .comp, congrArg' (congrArg' (.single (by assumption)))⟩
    | comp' => exact ⟨_, .single .comp', congrArg' (congrArg' (.single (by assumption)))⟩
    | curr  => exact ⟨_, .single .curr, congrArg' (sigr' (.single (by assumption)))⟩
    | sigma => exact ⟨_, .single .sigma, coup' (.single (.congrArg (by assumption)))⟩
    | congrFun => exact ⟨_, congrFun' (.single (by assumption)), congrArg' (.single (by assumption))⟩
    | congrArg h =>
      have ⟨D, h₁, h₂⟩ := ih h
      exact ⟨_, congrArg' h₁, congrArg' h₂⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance RedAff.instConf : Confluent RedAff := ⟨RedAff.conf⟩

theorem red_aff_globally_conf : Relation.ReflTransGen RedAff A B → Relation.ReflTransGen RedAff A C → ∃ D,
  Relation.ReflTransGen RedAff B D ∧ Relation.ReflTransGen RedAff C D :=
  RedAff.instRedRel.globally_confluent.conf

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instConfRedAffTrans : Confluent RedAff (m := Relation.ReflTransGen) := RedAff.instRedRel.globally_confluent

def semi_complete {A B : Expr} (hr : A.RedAff B) : ∃ B', ∃ (h : A.RedAff B'), (step? A) = .some ⟨B', ⟨h⟩⟩ := by
  change ∃ _, ∃ _, (step? _) = .some _
  unfold step?
  split
  repeat exact ⟨_, (RedAff.instRedRel.sound rfl).down, rfl⟩
  case h_9 =>
    cases hr with
    | sigl h_x =>
      have ⟨_, hrx', heq'⟩ := semi_complete h_x
      exact ⟨_, .sigl (by assumption), by rw [heq']⟩
    | sigr h_y =>
      rename_i x y _
      have ⟨_, hry', heq'⟩ := semi_complete h_y
      match x.step? with
      | .none =>
        exact ⟨_, .sigr (by assumption), by rw [heq']⟩
      | .some ⟨_, ⟨h_x'⟩⟩ =>
        exact ⟨_, .sigl (by assumption), by rw [heq']⟩
  case h_10 =>
    cases hr with
    | coup h =>
      have ⟨_, hrx', heq'⟩ := semi_complete h
      exact ⟨_, .coup hrx', by simp_all⟩
  case h_11 =>
    cases hr with
    | sigma => simp_all
    | fstc =>
      simp_all
      rename_i h
      exact (h _ _ _ _ rfl rfl rfl rfl).elim
    | sndc =>
      simp_all
      rename_i h
      exact (h _ _ _ _ rfl rfl rfl rfl).elim
    | congrFun h =>
      have ⟨_, hrf, heqf⟩ := semi_complete h
      exact ⟨_, .congrFun hrf, by rw [heqf]⟩
    | congrArg h =>
      have ⟨_, hrx, heqx⟩ := semi_complete h
      rename_i f x _ _ _ _ _ _ _ _ _ _
      match f.step? with
      | .none => exact ⟨_, .congrArg hrx, by simp_all⟩
      | .some ⟨_, ⟨hrf⟩⟩ => exact ⟨_, .congrFun hrf, by simp⟩
    | comp' | quot | id | comp => simp_all
    | curr =>
      rename_i h _
      exact (h _ _ _ _  rfl).elim
  case h_12 hmk hcoup happ =>
    simp_all
    induction A <;> (
      first
      | (focus
        cases hr
        done)
      | (exact (hcoup _ rfl).elim)
      | (exact (happ _ _ rfl).elim)
      | (exact (hmk _ _ _ rfl).elim))

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedAff.instSemicomplete : SemiComplete RedAff := ⟨semi_complete⟩

theorem aff_complete (h : Relation.ReflTransGen RedAff A B)
  (hn : IsNorm RedAff B) : reduce RedAff A = ⟨B, ⟨h⟩⟩ :=
  RedAff.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instComplete : Complete (Relation.ReflTransGen RedAff) (P := IsNorm RedAff) := RedAff.instRedRel.instComplete

-- RedRel.reduce Size RedAff.instRedRel : (e : Expr) → (e' : Expr) × PULift (Relation.ReflTransGen RedAff e e')
#check reduce RedAff

/-
Complete.complete
  Id : ∀ (h : Relation.ReflTransGen RedAff ?m.8 ?m.9), IsNorm RedAff ?m.9 → Rel.run Id ?m.8 = pure ⟨?m.9, { down := h }⟩
-/
#check instComplete.complete

@[grind ., grind →]
theorem red_aff_decreasing? (h : Relation.ReflTransGen RedAff A B) : (size B) ≤ (size A) := by
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
theorem red_aff_trans_decreasing : Relation.TransGen RedAff A B → (size B) < (size A) :=
  RedAff.instRedRel.to_trans.decreasing

@[dcc_force_reduce, dcc_force_aff]
abbrev RedAff.reduce := Expr.reduce RedAff

attribute [dcc_force_reduce, dcc_force_aff] RedAff.reduce.eq_def

instance : Decidable (IsNorm RedAff A) :=
  match heq₀ : reduce RedAff A with
  | ⟨A', ⟨h⟩⟩ =>
    if heq : A' = A then
      have h_norm := reduce_norm (h := heq ▸ h) (A := A) (B := A) (hR := RedAff.instRedRel) (heq ▸ heq₀)
      .isTrue (fun ⟨a, b⟩ => by
        exact h_norm ⟨_, b⟩)
    else
      .isFalse (fun h => by
        have h := RedAff.instRedRel.reduce_norm_fst h
        simp_all)

end Expr
