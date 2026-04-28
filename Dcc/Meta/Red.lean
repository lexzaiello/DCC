import Dcc.Attrs
import Dcc.Ast
import Dcc.Types
import Dcc.Aff.Size
import Dcc.Aff.Red
import Dcc.Relation

namespace Expr

inductive RedMeta : Expr → Expr → Prop
  | appl      : Relation.ReflTransGen RedAff (DCC (f_α env)) α
    → IsNorm RedAff α
    → RedMeta (DCC (App(m, n, f_α, f_β) env)) (App'.type α f_α f_β env m)

@[dcc_step, aesop norm (rule_sets := [DccStep])] def step_meta? (e : Expr) : Option ((e' : Expr) × (PULift.{1, 0} (RedMeta e e'))) :=
  match e with
  | DCC (App(_m, _n, _f_α, _f_β) _env) => .some ⟨_, ⟨.appl (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | _ => .none

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedMeta.instRedRel : RedRel RedMeta Size where
  run := step_meta?

@[dcc_step, aesop safe destruct (rule_sets := [DccStep])] theorem RedMeta.unique (h₁ : RedMeta A B) (h₂ : RedMeta A C) : B = C := by
  induction h₁ generalizing C with
  | appl hrt₁ hnorm₁ => cases h₂ with
    | appl hrt₂ hnorm₂ =>
      have h := norm_unique hrt₁ hnorm₁ hrt₂ hnorm₂
      simp_all

open Congruent in @[dcc_reduce, aesop safe apply (rule_sets := [DccReduce])] theorem RedMeta.conf (h₁ : RedMeta A B) (h₂ : RedMeta A C) : ∃ D, RedMeta.instRedRel.ReflTrans B D ∧ RedMeta.instRedRel.ReflTrans C D :=
  have h := RedMeta.unique h₁ h₂
  ⟨B, .refl, h ▸ .refl⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedMeta.instConf : Confluent RedMeta := ⟨RedMeta.conf⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instConfRedMetaTrans : Confluent RedMeta (m := Relation.ReflTransGen) := RedMeta.instRedRel.globally_confluent

def meta_semi_complete {A B : Expr} (hr : A.RedMeta B) : ∃ B', ∃ (h : A.RedMeta B'), (step_meta? A) = .some ⟨B', ⟨h⟩⟩ := by
  induction hr with
  | appl hrt hn =>
    have hc := reduce_complete hrt hn
    refine ⟨_, .appl hrt hn, by repeat (first | simp_all [dcc_step] | congr)⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedMeta.instSemicomplete : SemiComplete RedMeta := ⟨meta_semi_complete⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instCompleteMeta : Complete (Relation.ReflTransGen RedMeta) (P := IsNorm RedMeta) := RedMeta.instRedRel.instComplete

end Expr
