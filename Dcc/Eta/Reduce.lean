import Dcc.Eta.Ast
import Dcc.Relation

namespace EtaExpr

open Relation (ReflTransGen)
open Expr (IsNorm decreasing? reduce RedRel reduce_norm reduce_sound norm_unique)

inductive Domain : EtaExpr → EtaExpr → Prop
  | eql₁     : Domain f_α δ → (DCCη Eql(f_α)).Domain (DCCη !(δ))
  | eql₂     : ReflTransGen RedAffEta (DCCη (f_α &(env))) τ
    → IsNorm RedAffEta τ
    → Domain (DCCη (Eql(f_α) &(env))) τ
  | refl₁    : Domain f_α δ → (DCCη refl(f_α)).Domain (DCCη !(δ))
  | refl₂    : ReflTransGen RedAffEta (DCCη (f_α &(env))) τ
    → IsNorm RedAffEta τ
    → Domain (DCCη (refl(f_α) &(env))) τ
  | unbox    : Domain (DCCη *(α)) (DCCη !(α))
  | id       : Domain (DCCη Id(α)) α
  | fstc     : Domain (DCCη Fstc(β)) (DCCη Coup(β))
  | sndc     : Domain (DCCη Sndc(β)) (DCCη Coup(β))
  | curr₁    : Domain (DCCη Λ(α, β, x)) α
  | curr₂    : ReflTransGen RedAffEta (DCCη (β y)) τ
    → IsNorm RedAffEta τ
    → Domain (DCCη (Λ(α, β, x) y)) τ
  | curr₁'   : Domain (DCCη !Λ(α, β, x)) (DCCη !(α))
  | curr₂'   : ReflTransGen RedAffEta (DCCη (β y)) τ
  → IsNorm RedAffEta τ
  → Domain (DCCη (!Λ(α, β, x) &(y))) (DCCη !(τ))
  | map      : Domain f α → Domain (DCCη !<f>) (DCCη !(α))
  | fmap     : Domain f α → Domain (DCCη $<f>) (DCCη !(α))
  | pair     : Domain M α → Domain (DCCη ⟦β⟧⟨M, N⟩) α
  /-
  TODO: Not sure how to fit Eval in here yet
  | eval     : Val.Domain Val(λ env 2 => f) α → Val.Domain Val(
  | eval     : Apply x y f'
    → Apply f' z e'
    → Apply Val(λ env 1 => Eval(_α, _β, x)) Val(neutral(⟦__β⟧(y, z))) e'-/
  | quot     : Domain (DCCη `(β, x)) β
  -- f ∘ g x
  -- again, need to handle second round
  -- can use β-reducer for this.
  | comp'    : Domain g α → Domain (DCCη f ∘' g) α
  | comp     : Domain g α → Domain (DCCη f ∘ g) α
  | comp₂    : Domain g α → Domain (DCCη f ∘∘ g) α
  | pi       : Domain f_α δ → Domain (DCCη Π(f_α, f_β)) δ

@[dcc_force_reduce, dcc_force_aff]
def domain? (e : EtaExpr) : Option ((τ : EtaExpr) × (PULift.{1, 0} (Domain e τ))) :=
  match e with
  | (DCCη Eql(f_α)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.eql₁ h⟩⟩
    | _ => .none
  | (DCCη (Eql(_f_α) &(_env))) => .some ⟨_, ⟨.eql₂ (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCCη refl(f_α)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.refl₁ h⟩⟩
    | _ => .none
  | (DCCη (refl(_f_α) &(_env))) => .some ⟨_, ⟨.refl₂ (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCCη *(_α)) => .some ⟨_, ⟨.unbox⟩⟩
  | (DCCη Id(_α)) => .some ⟨_, ⟨.id⟩⟩
  | (DCCη Fstc(_β)) => .some ⟨_, ⟨.fstc⟩⟩
  | (DCCη Sndc(_β)) => .some ⟨_, ⟨.sndc⟩⟩
  | (DCCη Λ(_α, _β, _x)) => .some ⟨_, ⟨.curr₁⟩⟩
  | (DCCη (Λ(_α, _β, _x) _y)) => .some ⟨_, ⟨.curr₂ (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCCη !Λ(_α, _β, _x)) => .some ⟨_, ⟨.curr₁'⟩⟩
  | (DCCη (!Λ(_α, _β, _x) &(_y))) => .some ⟨_, ⟨.curr₂' (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCCη !<f>) =>
    match f.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.map h⟩⟩
    | _ => .none
  | (DCCη $<f>) =>
    match f.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.fmap h⟩⟩
    | _ => .none
  | (DCCη ⟦_β⟧⟨M, _N⟩) =>
    match M.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pair h⟩⟩
    | _ => .none
  | (DCCη `(_β, _x)) => .some ⟨_, ⟨.quot⟩⟩
  | (DCCη _f ∘' g) =>
    match g.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp' h⟩⟩
    | _ => .none
  | (DCCη _f ∘ g) =>
    match g.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp h⟩⟩
    | _ => .none
  | (DCCη _f ∘∘ g) =>
    match g.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp₂ h⟩⟩
    | _ => .none
  | (DCCη Π(f_α, _f_β)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi h⟩⟩
    | _ => .none
  | _ => .none

@[dcc_force_reduce, dcc_force_aff]
instance Domain.instRedRel : Expr.RedRel Domain size where
  run := domain?
  decreasing := by
    intro x y h
    induction h
    any_goals (
      focus
      try dsimp
      try simp_all [dcc_rel, dcc_size, Rel.run]
      try grind
      try aesop (rule_sets := [DccRel, DccSize])
      try rfl
      done)
    any_goals (
      focus
      have h := decreasing? RedAffEta (by assumption)
      try dsimp
      try simp_all [dcc_rel, dcc_size, Rel.run]
      try grind
      try aesop (rule_sets := [DccRel, DccSize])
      try rfl
      try grind)

theorem Domain.deterministic (h₁ : Domain x τ₁) (h₂ : Domain x τ₂) : τ₁ = τ₂ := by
  induction h₁ generalizing τ₂
  any_goals (
    focus
    cases h₂
    aesop
    done)
  any_goals (
    focus
    cases h₂
    rename_i h₁ h₂ h₃ h₄
    have h := norm_unique h₁ h₂ h₄ h₃
    aesop)
  case curr₂' =>
    cases h₂
    rename_i h₁ h₂ _ h₃ h₄
    have h := norm_unique h₁ h₂ h₄ h₃
    aesop

@[dcc_reduce, aesop safe apply (rule_sets := [DccReduce])]
theorem Domain.conf (h₁ : Domain A B) (h₂ : Domain A C) : ∃ D, ReflTransGen Domain B D ∧ ReflTransGen Domain C D := by
  cases h₁.deterministic h₂
  exact ⟨_, .refl, .refl⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance Domain.instConf : Expr.Confluent Domain := ⟨Domain.conf⟩

def Domain.semi_complete {A B : EtaExpr} (hr : A.Domain B) : ∃ B', ∃ (h : A.Domain B'), (domain? A) = .some ⟨B', ⟨h⟩⟩ := by
  change ∃ _, ∃ _, (domain? _) = .some _
  unfold domain?
  split
  any_goals (exact ⟨_, (Domain.instRedRel.sound rfl).down, rfl⟩)
  any_goals (
    focus
    cases hr
    rename_i hr
    have ⟨_, hr', heq⟩ := hr.semi_complete
    exact ⟨_, by
      focus
      first
      | try constructor
        exact hr'
      | exact hr
      | exact hr', by
        simp_all⟩)
  case h_21 =>
    cases hr
    any_goals (focus
      try aesop
      done)
    case curr₂ =>
      simp_all
      rename_i h _ _
      exact (h _ _ _ _ rfl rfl rfl rfl).elim
    case curr₂' =>
      simp_all
      rename_i h
      exact (h _ _ _ _ rfl rfl rfl rfl).elim

inductive EtaReduces : EtaExpr → EtaExpr → Prop
  

end EtaExpr
