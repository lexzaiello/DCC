import Dcc.Relation
import Dcc.Ast
import Dcc.Types
import Dcc.Eta.Size
import Dcc.Aff.Red
import Dcc.Aff.Size

namespace Expr

inductive RedEta : Expr → Expr → Prop
  --| curr       : RedEta x x' → RedEta (DCC (Λ(α, β, x))) (DCC (Λ(α, β, x')))
  | curr_quot  : RedEta (DCC (Λ(α, Id(α), `(Coup(Id(α)), x)) y)) (DCC `(y, x))
  | curr_fst   : RedEta (DCC (Λ(α, β, x ∘ Fstc(β₂)) y)) (DCC `((β y), (x y)))
  | curr_fst'  : RedEta (DCC (Λ(α, β, x ∘' Fstc(β₂)) y)) (DCC `((β y), (x y)))
  | pi         : Relation.ReflTransGen RedAff env env'
    → IsNorm RedAff env'
    → RedEta (DCC Π(α, β)) p' → RedEta (DCC (Π(α, β) env)) (DCC (p' env))
  --| pi_quot    : RedEta x x' → RedEta (DCC (Π(α, `(β, x)))) (DCC (Π(α, `(β, x'))))
  --| quot       : RedEta x x' → RedEta (DCC `(β, x)) (DCC `(β, x'))
  | pi'        : RedEta β β' → RedEta (DCC (Π(α, β))) (DCC (Π(α, β')))
--  | sig        : RedEta (DCC (β env)) β' → RedEta (DCC (Σ(α, β) env)) (DCC Coup(β'))
  | sig'       : RedEta β β' → RedEta (DCC (Σ(α, β))) (DCC Σ(α, β'))
  | coup       : RedEta β β' → RedEta (DCC (Coup(β))) (DCC (Coup(β')))
  | quot_fst   : RedEta (DCC `(α, x) ∘ Fstc(β)) (DCC `(Coup(β), x))
  | quot'_fst  : RedEta (DCC `(α, x) ∘' Fstc(β)) (DCC `(Coup(β), x))
  | quot_snd   : RedEta (DCC `(α, x) ∘ Sndc(β)) (DCC `(Coup(β), x))
  | quot'_snd  : RedEta (DCC `(α, x) ∘' Sndc(β)) (DCC `(Coup(β), x))
  | quot_fst'  : RedEta (DCC (`(α, x) ∘ Fstc(β)) ∘ z) (DCC `(Coup(β), x) ∘ z)
  | quot'_fst' : RedEta (DCC (`(α, x) ∘' Fstc(β)) ∘' z) (DCC `(Coup(β), x) ∘' z)
  | quot_snd'  : RedEta (DCC (`(α, x) ∘ Sndc(β)) ∘ z) (DCC `(Coup(β), x) ∘ z)
  | quot'_snd' : RedEta (DCC (`(α, x) ∘' Sndc(β)) ∘' z) (DCC `(Coup(β), x) ∘' z)
  /-| pi_comp    : RedEta (DCC (Π(f_α, f_β) ∘ x)) (DCC (Π(f_α ∘ x, f_β ∘ x)))
  | pi'_comp   : RedEta (DCC (Π(f_α, f_β) ∘' x)) (DCC (Π(f_α ∘' x, f_β ∘' x)))-/
  | eql        : RedEta (DCC (Eql(f_α) env x)) (DCC (x = x))
  /-| quot_comp : RedEta (DCC (`(α, x) ∘ y)) x'
    → RedEta (DCC (`(α, x) ∘ (y ∘ z))) (DCC (x' ∘ z))-/

theorem RedEta.norm_aff (hn : IsNorm RedAff A) (h : RedEta A B) : IsNorm RedAff B := by
  induction h
  any_goals (
    focus
    intro ⟨_, h⟩
    cases h
    done
  )
  case pi h ih =>
    cases h with
    /-| pi_quot =>
      have h := ih hn.congrFun
      have h_norm_env := hn.congrArg
      intro ⟨_, h⟩
      cases h with
      | congrFun hr =>
        exact h ⟨_, hr⟩
      | congrArg hr =>
        exact h_norm_env ⟨_, hr⟩-/
    | pi' =>
      have hn_env := hn.congrArg
      have h := ih hn.congrFun
      intro ⟨_, h⟩
      cases h with
      | congrFun hr =>
        exact h ⟨_, hr⟩
      | congrArg hr =>
        exact hn_env ⟨_, hr⟩
  case coup ih =>
    intro ⟨_, h⟩
    cases h with
    | coup hr =>
      rename_i β β'₁ _ _
      have hn' : IsNorm RedAff β := fun ⟨_, h⟩ => by
        exact hn ⟨_, .coup h⟩
      exact (ih (by assumption)) ⟨_, (by assumption)⟩

@[dcc_force_eta, dcc_force_reduce, aesop norm (rule_sets := [DccStep])] def step_eta? (e : Expr) : Option ((e' : Expr) × (PULift.{1, 0} (RedEta e e'))) :=
  match e with
  | DCC (Eql(f_α) env x) => .some ⟨_, ⟨.eql⟩⟩
  | DCC (Λ(α, _b, `(_c, x)) y) =>
    if heq : (DCC (Λ(α, _b, `(_c, x)) y)) = (DCC (Λ(α, Id(α), `(Coup(Id(α)), x)) y)) then
      heq ▸ .some ⟨_, ⟨.curr_quot⟩⟩
    else .none
  | DCC (Λ(_α, β, x ∘ Fstc(_β₂)) y) => .some ⟨_, ⟨.curr_fst⟩⟩
  | DCC (Λ(_α, β, x ∘' Fstc(_β₂)) y) => .some ⟨_, ⟨.curr_fst'⟩⟩
  | DCC Σ(α, f_β) =>
    match f_β.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.sig' h⟩⟩
    | _ => .none
  | DCC Coup(f_β) =>
    match f_β.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.coup h⟩⟩
    | _ => .none
  /-| DCC (Σ(α, f_β) env) =>
    match (DCC (f_β env)).step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.sig h⟩⟩
    | _ => .none-/
  | DCC (Π(_f_α, f_β) _env) =>
    match (DCC Π(_f_α, f_β)).step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi (reduce_sound rfl) (reduce_norm rfl) h⟩⟩
    | _ => .none
  /-| DCC `(β, x) =>
    match x.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.quot h⟩⟩
    | _              => .none-/
  | DCC (Π(_f_α, f_β)) =>
    match f_β with
    /-| DCC `(_β, x) =>
      match x.step_eta? with
      | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi_quot h⟩⟩
      | _ => .none-/
    | x =>
      match x.step_eta? with
      | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi' h⟩⟩
      | _ => .none
  /-| DCC Λ(_α, _β, x) =>
    match x.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.curr h⟩⟩
    | .none => .none-/
  | (DCC `(α, x) ∘ Fstc(β)) => .some ⟨_, ⟨.quot_fst⟩⟩
  | (DCC `(α, x) ∘' Fstc(β)) => .some ⟨_, ⟨.quot'_fst⟩⟩
  | (DCC `(α, x) ∘ Sndc(β)) => .some ⟨_, ⟨.quot_snd⟩⟩
  | (DCC `(α, x) ∘' Sndc(β)) => .some ⟨_, ⟨.quot'_snd⟩⟩
  --| DCC (Π(f_α, f_β) ∘ x) => .some ⟨_, ⟨.pi_comp⟩⟩
  --| DCC (Π(f_α, f_β) ∘' x) => .some ⟨_, ⟨.pi'_comp⟩⟩
  | (DCC (`(α, x) ∘ Fstc(β)) ∘ z) => .some ⟨_, ⟨.quot_fst'⟩⟩
  | (DCC (`(α, x) ∘' Fstc(β)) ∘' z) => .some ⟨_, ⟨.quot'_fst'⟩⟩
  | (DCC (`(α, x) ∘ Sndc(β)) ∘ z) => .some ⟨_, ⟨.quot_snd'⟩⟩
  | (DCC (`(α, x) ∘' Sndc(β)) ∘' z) => .some ⟨_, ⟨.quot'_snd'⟩⟩
  | _ => .none

@[dcc_force_reduce, dcc_force_eta, aesop norm (rule_sets := [DccRel])]
instance RedEta.instRedRel : RedRel RedEta size where
  run := step_eta?

theorem red_eta_sn : ∀ (e : Expr), Acc (fun b a => RedEta a b) e := RedEta.instRedRel.sn

theorem red_eta_trans_sn : ∀ (e : Expr), Acc (fun b a => Relation.TransGen RedEta a b) e := RedEta.instRedRel.to_trans.sn

@[dcc_reduce, aesop safe forward (rule_sets := [DccRel])] theorem RedEta.unique (h₁ : RedEta A B) (h₂ : RedEta A C) : B = C := by
  induction h₁ generalizing C with
  -- | pi_comp | pi'_comp => sorry
  | quot_fst
  | coup | eql | curr_fst' | curr_fst | quot'_snd' | quot'_fst' | quot'_fst | quot'_snd | quot_snd' | quot_fst' | quot_snd | sig' | pi => cases h₂; aesop
  /-| pi_quot hr ih =>
    cases h₂
    · rename_i hr₂; aesop
    · rename_i hr₂; cases hr₂-/
  /-| quot =>
    cases h₂
    · aesop-/
  | pi' hr ih =>
    cases h₂
    · aesop
  /-| curr hr ih =>
    cases h₂ with
    | curr hr₂ => rw [ih hr₂]-/
  --| idl'
  --| idl
  | curr_quot => cases h₂; rfl
  --| sig => sorry

open Congruent in theorem RedEta.conf (h₁ : RedEta A B) (h₂ : RedEta A C) : ∃ D, RedEta.instRedRel.ReflTrans B D ∧ RedEta.instRedRel.ReflTrans C D := by
  have h := h₁.unique h₂
  exact ⟨B, h ▸ .refl, h ▸ .refl⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedEta.instConf : Confluent RedEta := ⟨RedEta.conf⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instConfRedEtaTrans : Confluent RedEta (m := Relation.ReflTransGen) := RedEta.instRedRel.globally_confluent

theorem RedEta.complete (h_red : RedEta A B) : step_eta? A = .some ⟨B, ⟨h_red⟩⟩ := by
  induction h_red <;> (
    unfold step_eta?
    aesop (rule_sets := [DccStep, DccReduce, DccSize, DccRel]))

def eta_semi_complete {A B : Expr} (h_red : A.RedEta B) : ∃ B', ∃ (h : A.RedEta B'), (step_eta? A) = .some ⟨B', ⟨h⟩⟩ :=
  ⟨_, _, h_red.complete⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedEta.instSemicomplete : SemiComplete RedEta := ⟨eta_semi_complete⟩

theorem eta_complete (h : Relation.ReflTransGen RedEta A B)
  (hn : IsNorm RedEta B) : reduce RedEta A = ⟨B, ⟨h⟩⟩ :=
  RedEta.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instCompleteEta : Complete (Relation.ReflTransGen RedEta) (P := IsNorm RedEta) := RedEta.instRedRel.instComplete

@[dcc_force_reduce, dcc_force_eta]
abbrev RedEta.reduce := Expr.reduce RedEta

attribute [dcc_force_reduce, dcc_force_eta] RedEta.reduce.eq_def

instance : Decidable (IsNorm RedEta A) :=
  match heq₀ : reduce RedEta A with
  | ⟨A', ⟨h⟩⟩ =>
    if heq : A' = A then
      have h_norm := reduce_norm (h := heq ▸ h) (A := A) (B := A) (hR := RedEta.instRedRel) (heq ▸ heq₀)
      .isTrue (fun ⟨a, b⟩ => by
        exact h_norm ⟨_, b⟩)
    else
      .isFalse (fun h => by
        have h := RedEta.instRedRel.reduce_norm_fst h
        simp_all)

end Expr
