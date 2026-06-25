import Dcc.Ast
import Dcc.Aff.Red
import Dcc.Eta.Red
import Dcc.Relation
import Mathlib.Logic.Relation
import Mathlib.Data.Option.Basic
import Mathlib.Data.ULift

namespace GenericExpr

@[dcc_judge]
def RedAffReflTrans.{u} {τ : Type u} := Relation.ReflTransGen (RedAff (τ := τ))

namespace RedAffReflTrans

def cases_head {a b : Expr} (r : RedAffReflTrans a b) :=
  Relation.ReflTransGen.cases_head (a := a) (b := b) r

def single.{u} {τ : Type u} {A B : GenericExpr τ}
  (r : RedAff A B) : (RedAffReflTrans (τ := τ)) A B := Relation.ReflTransGen.single r

def trans.{u} {τ : Type u} {A B C : GenericExpr τ} (r₁ : RedAffReflTrans A B)
  (r₂ : RedAffReflTrans B C) : RedAffReflTrans A C := Relation.ReflTransGen.trans r₁ r₂

def conf.{u} {τ : Type u} {A B C : GenericExpr τ} (h₁ : RedAffReflTrans A B) (h₂ : RedAffReflTrans A C) : ∃ D, RedAffReflTrans B D ∧ RedAffReflTrans C D := RedAff.instRedRel.globally_confluent.conf h₁ h₂

end RedAffReflTrans

end GenericExpr

namespace Expr

open GenericExpr

/-abbrev IsNorm := GenericExpr.IsNorm (α := GenericExpr (τ := Unit))

abbrev RedAff.instRedRel := GenericExpr.RedAff.instRedRel (τ := Unit)

abbrev reduce? : ∀ {t : Expr → ℕ} (r : Expr → Expr → Prop) [_hR : GenericExpr.RedRel r t]
  (e : Expr), Option ((e' : Expr) × (PULift.{1, 0} (Relation.TransGen r e e'))) := GenericExpr.reduce? (α := GenericExpr (τ := Unit))

abbrev reduce' : ∀ {t : Expr → ℕ} (r : Expr → Expr → Prop) [_hR : GenericExpr.RedRel r t]
  (e : Expr), Expr := GenericExpr.reduce'

abbrev decreasing? : ∀ {t : Expr → ℕ}
  (r : Expr → Expr → Prop) [_hR : GenericExpr.RedRel r t] {A B : Expr} (_hr : Relation.ReflTransGen r A B), t B ≤ t A := GenericExpr.decreasing? (α := GenericExpr (τ := Unit))-/

@[dcc_judge]
def RedAffTrans     := Relation.TransGen RedAff

@[dcc_judge]
def RedEtaReflTrans := Relation.ReflTransGen RedEta

@[dcc_judge]
def RedEtaTrans     := Relation.TransGen RedEta

namespace RedEtaReflTrans

def cases_head {a b : Expr} (r : RedEtaReflTrans a b) :=
  Relation.ReflTransGen.cases_head (a := a) (b := b) r

end RedEtaReflTrans

namespace RedAffTrans

def single (r : RedAff A B) : RedAffTrans A B := Relation.TransGen.single r

def trans (r₁ : RedAffTrans A B) (r₂ : RedAffTrans B C) : RedAffTrans A C := Relation.TransGen.trans r₁ r₂

def to_reflTrans {a b : Expr} (r : RedAffTrans a b) : RedAffReflTrans a b :=
  Relation.TransGen.to_reflTransGen (a := a) (b := b) r

end RedAffTrans

namespace RedEtaTrans

def to_reflTrans {a b : Expr} (r : RedEtaTrans a b) : RedEtaReflTrans a b :=
  Relation.TransGen.to_reflTransGen (a := a) (b := b) r

def single (r : RedEta A B) : RedEtaTrans A B := Relation.TransGen.single r

def trans (r₁ : RedEtaTrans A B) (r₂ : RedEtaTrans B C) : RedEtaTrans A C := Relation.TransGen.trans r₁ r₂

end RedEtaTrans

instance : Coe (RedAffReflTrans A B) (Relation.ReflTransGen RedAff A B) := ⟨fun e => e⟩
instance : Coe (RedEtaReflTrans A B) (Relation.ReflTransGen RedEta A B) := ⟨fun e => e⟩
instance : Coe (RedAffTrans A B) (Relation.TransGen RedAff A B)         := ⟨fun e => e⟩
instance : Coe (RedEtaTrans A B) (Relation.TransGen RedEta A B)         := ⟨fun e => e⟩

instance : Coe (Relation.ReflTransGen RedAff A B) (RedAffReflTrans A B) := ⟨fun e => e⟩
instance : Coe (Relation.ReflTransGen RedEta A B) (RedEtaReflTrans A B) := ⟨fun e => e⟩
instance : Coe (Relation.TransGen RedAff A B) (RedAffTrans A B)         := ⟨fun e => e⟩
instance : Coe (Relation.TransGen RedEta A B) (RedEtaTrans A B)         := ⟨fun e => e⟩

inductive Reduced : Expr → Expr → Prop
  | mk : RedAffTrans A B
    → IsNorm RedAff B
    → RedEtaReflTrans B C
    → IsNorm RedEta C
    → Reduced A C

def reduce_all? (e : Expr) : Option ((e' : Expr) × PLift (Reduced e e')) :=
  if h_some : (reduce? RedAff e).isSome then
    .some ⟨reduce' RedEta ((reduce? RedAff e).get h_some).fst, ⟨by
      have hn := reduce?_norm RedAff (A := e) (B := ((reduce? RedAff e).get h_some).fst)
        (by simp_all) (by simp_all)
      exact ⟨((reduce? RedAff e).get h_some).snd.down, hn, reduce_sound rfl, reduce_norm rfl⟩⟩⟩
  else
    .none
    /-sorry
  match heq : reduce? RedAff e with
  | .some ⟨e', ⟨h⟩⟩ =>
    have hn := reduce?_norm RedAff (A := e) (B := e') (by simp_all) (by simp_all)
    .some ⟨reduce' RedEta e', ⟨h, hn, reduce_sound rfl, reduce_norm rfl⟩⟩
  | _ => .none-/

theorem Reduced.unique : Reduced A B → Reduced A C → B = C := fun ⟨a, b, c, d⟩ ⟨g, h, i, j⟩ => by
  have ha := norm_unique a.to_reflTransGen b g.to_reflTransGen h
  exact norm_unique c d (ha ▸ i) j

theorem Reduced.unique' (h₁ : Reduced A B) (h₂ : Reduced A C) : h₁ ≍ h₂ := by
  have h := h₁.unique h₂
  cases h
  congr

def Reduced.norm_eta (h : Reduced A B) : IsNorm RedEta B :=
  match h with
  | ⟨_, _, _, h⟩ => h

theorem reduce_all?_reduces (h_some : (reduce_all? A).isSome) (h : ((reduce_all? A).get h_some).fst = B) : Reduced A B :=
  h ▸ ((reduce_all? A).get h_some).snd.down

inductive Reduces : Expr → Expr → Prop
  | mk : RedAffReflTrans A B
    → IsNorm RedAff B
    → RedEtaReflTrans B C
    → IsNorm RedEta C
    → Reduces A C

notation A "≡" B => ∃ C, Reduces A C ∧ Reduces B C

@[dcc_force_reduce]
def reduce_all := reduce' RedEta ∘ reduce' RedAff

@[grind ., grind <=, dcc_reduce, aesop safe forward (rule_sets := [DccReduce])]
theorem Reduces.unique : Reduces A B → Reduces A C → B = C := fun ⟨a, b, c, d⟩ ⟨g, h, i, j⟩ => by
  have ha := norm_unique a b g h
  exact norm_unique c d (ha ▸ i) j

@[aesop safe destruct (rule_sets := [DccReduce]), aesop safe apply (rule_sets := [DccReduce])]
theorem Reduces.unique' (h₁ : Reduces A B) (h₂ : Reduces A C) : h₁ ≍ h₂ := by
  have h := h₁.unique h₂
  cases h
  congr

@[dcc_reduce]
def Reduces.norm_eta (h : Reduces A B) : IsNorm RedEta B :=
  match h with
  | ⟨_, _, _, h⟩ => h

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
theorem Reduces.complete : Reduces A B → reduce_all A = B :=
  fun ⟨ha, hb, hc, hd⟩ => by
    unfold reduce_all
    unfold reduce'
    cases reduce_complete_fst ha hb; cases reduce_complete_fst hc hd; rfl

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
theorem Reduced.complete : Reduced A B → ∃ h, reduce_all? A = .some ⟨B, h⟩ :=
  fun ⟨ha, hb, hc, hd⟩ => by
    rename_i h₀ _
    unfold reduce_all?
    unfold reduce?
    split
    case isTrue h =>
      simp_all only [Option.some.injEq, Sigma.mk.injEq, Option.get_dite', exists_and_left, PLift.exists,
        exists_true_left]
      constructor
      have h := Reduces.complete ⟨ha.to_reflTransGen, hb, hc, hd⟩
      · change reduce' RedEta (reduce' RedAff A) = B
        exact h
      · congr
        simp_all only [Option.get_dite']
        · have h := Reduces.complete ⟨ha.to_reflTransGen, hb, hc, hd⟩
          change reduce' RedEta (reduce' RedAff A) = B
          exact h
        · grind
    case isFalse heq =>
      simp_all only [Option.isSome_dite', Decidable.not_not, reduceCtorEq, exists_false]
      have h := reduce_norm_fst heq.symm
      cases ha using Relation.TransGen.head_induction_on with
      | single hr => exact h ⟨_, heq.symm ▸ hr⟩
      | head h =>
        rename_i h_norm _ _ _
        exact h_norm ⟨_, heq.symm ▸ h⟩

--@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])] theorem

def reduce_reduces (h : reduce_all A = B) : Reduces A B := ⟨
  reduce_sound rfl,
  reduce_norm rfl,
  h ▸ (reduce_sound rfl),
  h ▸ (reduce_norm rfl)⟩

def reduce_reduces' : Reduces A (reduce_all A) := reduce_reduces rfl

def Reduced.to_reduces (h : Reduced A B) : Reduces A B :=
  match h with
  | ⟨ha, hb, hc, hd⟩ => ⟨ha.to_reflTrans, hb, hc, hd⟩

end Expr
