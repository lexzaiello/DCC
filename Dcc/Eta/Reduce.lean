import Dcc.Eta.Ast
import Dcc.Relation

namespace EtaExpr

open Relation (ReflTransGen)
open Expr (IsNorm decreasing? reduce RedRel reduce_norm reduce_sound norm_unique Complete reduce_complete reduce_complete_fst)

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

@[aesop safe forward (rule_sets := [DccReduce])]
theorem Domain.complete (h : Domain e τ) : domain? e = .some ⟨τ, ⟨h⟩⟩ := by
  induction h
  any_goals (
    focus
    dsimp [domain?]
    aesop
    done)
  any_goals (
    rename_i h₁ h₂
    dsimp [domain?]
    have h := reduce_complete h₁ h₂
    simp_all
    grind)
  any_goals (dsimp [domain?])

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

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance Domain.instSemicomplete : Expr.SemiComplete Domain := ⟨Domain.semi_complete⟩

theorem domain_complete (h : Relation.ReflTransGen Domain A B)
  (hn : Expr.IsNorm Domain B) : Expr.reduce Domain A = ⟨B, ⟨h⟩⟩ :=
  Domain.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance Domain.instComplete : Complete (Relation.ReflTransGen Domain) (P := Expr.IsNorm Domain) := Domain.instRedRel.instComplete

inductive EtaMap : (dom : EtaExpr) → (out : EtaExpr) → (hole_arg : EtaExpr) → (f' : EtaExpr) → Prop
  | id    : EtaMap dom hole_arg hole_arg (DCCη Id(dom))
  | par   : EtaMap dom (DCCη (f hole_arg)) hole_arg f
  | fstc  : EtaMap dom (DCCη hole(a)) (DCCη ⟦β⟧(hole(a), hole(a + 1))) (DCCη Fstc(β))
  | sndc  : EtaMap dom (DCCη hole(a + 1)) (DCCη ⟦β⟧(hole(a), hole(a + 1))) (DCCη Sndc(β))

def map_eta (dom : EtaExpr) (out : EtaExpr) (hole_arg : EtaExpr) : Option ((f' : EtaExpr) × PLift (EtaMap dom out hole_arg f')) :=
  if heq : out = hole_arg then
    heq ▸ .some ⟨_, ⟨.id⟩⟩
  else
    match out, hole_arg with
    | DCCη (_f hole_arg₂), hole_arg =>
      if heq : hole_arg₂ = hole_arg then
        heq ▸ .some ⟨_, ⟨.par⟩⟩
      else .none
    | (DCCη hole(n)), (DCCη ⟦_β⟧(hole(a), hole(b))) =>
      if h₁ : b = a + 1 then
        if h₂ : n = a then by
          cases h₁; cases h₂
          exact .some ⟨_, ⟨.fstc⟩⟩
        else if h₂ : n = a + 1 then by
          cases h₁; cases h₂
          exact .some ⟨_, ⟨.sndc⟩⟩
        else .none
      else .none
    | _, _ => .none

@[aesop safe forward (rule_sets := [DccReduce])]
theorem EtaMap.complete (h : EtaMap dom out hole_arg f') : map_eta dom out hole_arg = .some ⟨f', ⟨h⟩⟩ := by
  dsimp [map_eta]
  cases h
  any_goals (simp)
  · intro h
    cases h

@[aesop safe forward (rule_sets := [DccReduce])]
inductive EtaResult : (dom : EtaExpr) → (out : EtaExpr) → (hole_arg : EtaExpr) → (f' : EtaExpr) → Prop
  | map   : (EtaExpr.contains out hole_arg)
    → EtaMap dom out hole_arg f'
    → EtaResult dom out hole_arg f'
  | quot  : (¬ EtaExpr.contains out hole_arg)
    → EtaResult dom out hole_arg (DCCη `(dom, out))

def mk_eta_result (dom : EtaExpr) (out : EtaExpr) (hole_arg : EtaExpr) : Option ((f' : EtaExpr) × PLift (EtaResult dom out hole_arg f')) :=
  if h₁ : out.contains hole_arg then
    match map_eta dom out hole_arg with
    | .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.map h₁ h₂⟩⟩
    | _ => .none
  else
    .some ⟨_, ⟨.quot h₁⟩⟩

theorem EtaResult.complete (h : EtaResult dom out hole_arg f') : mk_eta_result dom out hole_arg = .some ⟨f', ⟨h⟩⟩ := by
  dsimp [mk_eta_result]
  cases h <;> aesop (rule_sets := [DccReduce])

inductive TmEtaReduces : (level : ℕ) → (f : EtaExpr) → (f' : EtaExpr) → Prop
  | coupl : Domain f (DCCη Coup(β))
    → ReflTransGen RedAffEta (DCCη (f ⟦β⟧(hole(level + 1), hole(level + 2)))) e'
    → IsNorm RedAffEta e'
    → EtaResult (DCCη Coup(β)) e' (DCCη ⟦β⟧(hole(level + 1), hole(level + 2))) f'
    → TmEtaReduces level f f'
  | sort  : Domain f (DCCη Sort m)
    → ReflTransGen RedAffEta (DCCη (f hole(level + 1))) e'
    → IsNorm RedAffEta e'
    → EtaResult (DCCη Sort m) e' (DCCη hole(level + 1)) f'
    → TmEtaReduces level f f'
  | top  : Domain f (DCCη ⊤)
    → ReflTransGen RedAffEta (DCCη (f hole(level + 1))) e'
    → IsNorm RedAffEta e'
    → EtaResult (DCCη ⊤) e' (DCCη hole(level + 1)) f'
    → TmEtaReduces level f f'
  | bot  : Domain f (DCCη ⊥)
    → ReflTransGen RedAffEta (DCCη (f hole(level + 1))) e'
    → IsNorm RedAffEta e'
    → EtaResult (DCCη ⊥) e' (DCCη hole(level + 1)) f'
    → TmEtaReduces level f f'
  | tm   : Domain e (DCCη (f x))
    → ReflTransGen RedAffEta (DCCη (e hole(level + 1))) e'
    → IsNorm RedAffEta e'
    → EtaResult (DCCη (f x)) e' (DCCη hole(level + 1)) f'
    → TmEtaReduces level e f'

def eta_reduce_tm (level : ℕ) (f : EtaExpr) : Option ((f' : EtaExpr) × (PLift (TmEtaReduces level f f'))) :=
  match f.domain? with
  | .some ⟨(DCCη Coup(β)), ⟨h₁⟩⟩ =>
    match mk_eta_result (DCCη Coup(β))
      (reduce RedAffEta (DCCη (f ⟦β⟧(hole(level + 1), hole(level + 2))))).fst
      (DCCη ⟦β⟧(hole(level + 1), hole(level + 2))) with
    | .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.coupl h₁ (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
    | _ => .none
  | .some ⟨(DCCη Sort m), ⟨h₁⟩⟩ =>
    match mk_eta_result (DCCη Sort m)
      (reduce RedAffEta (DCCη (f hole(level + 1)))).fst
      (DCCη hole(level + 1)) with
    | .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.sort h₁ (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
    | _ => .none
  | .some ⟨(DCCη ⊤), ⟨h₁⟩⟩ =>
    match mk_eta_result (DCCη ⊤)
      (reduce RedAffEta (DCCη (f hole(level + 1)))).fst
      (DCCη hole(level + 1)) with
    | .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.top h₁ (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
    | _ => .none
  | .some ⟨(DCCη ⊥), ⟨h₁⟩⟩ =>
    match mk_eta_result (DCCη ⊥)
      (reduce RedAffEta (DCCη (f hole(level + 1)))).fst
      (DCCη hole(level + 1)) with
    | .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.bot h₁ (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
    | _ => .none
  | .some ⟨DCCη (a b), ⟨h₁⟩⟩ =>
    match mk_eta_result (DCCη (a b))
      (reduce RedAffEta (DCCη (f hole(level + 1)))).fst
      (DCCη hole(level + 1)) with
    | .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.tm h₁ (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
    | _ => .none
  | _ => .none

theorem TmEtaReduces.complete (h : TmEtaReduces level f f') : eta_reduce_tm level f = .some ⟨f', ⟨h⟩⟩ := by
  dsimp [eta_reduce_tm]
  induction h <;> (
    focus
    rename_i h_domain hr hn hmk
    have ha := reduce_complete_fst hr hn
    cases ha
    have hb := h_domain.complete
    have hc := hmk.complete
    simp_all)

instance : Decidable (TmEtaReduces level f f') :=
  if h : (f.eta_reduce_tm level).isSome then
    if heq : ((f.eta_reduce_tm level).get h).fst = f' then
      .isTrue (heq ▸ ((f.eta_reduce_tm level).get h).snd.down)
    else
      .isFalse (fun h => by
        have h := h.complete
        simp_all)
  else
    .isFalse (fun h => by
      have h := h.complete
      simp_all)

instance : Decidable (∃ f', TmEtaReduces level f f') :=
  if heq : (f.eta_reduce_tm level).isSome then
    .isTrue ⟨_, ((f.eta_reduce_tm level).get heq).snd.down⟩
  else
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

inductive FnEtaReduces : (level : ℕ) → (f : EtaExpr) → (f' : EtaExpr) → Prop
  | pi  : FnEtaReduces level.succ f_α f_α'
    → FnEtaReduces level.succ.succ f_β f_β'
    → FnEtaReduces level (DCCη Π(f_α, f_β)) (DCCη Π(f_α', f_β'))
  | tm  : (¬ ∃ f_α f_β, f = (DCCη Π(f_α, f_β)))
    → TmEtaReduces level f f'
    → FnEtaReduces level f f'
  | tm' : (¬ ∃ f_α f_β, f = (DCCη Π(f_α, f_β)))
    → (¬ ∃ f', TmEtaReduces level f f')
    → FnEtaReduces level f f

instance : Decidable (∃ (f_α : EtaExpr) (f_β : EtaExpr), f = f_α.pi f_β) := by
  cases f
  case pi =>
    exact .isTrue (by aesop)
  any_goals (
    exact .isFalse (by
      intro ⟨_, _, heq⟩
      simp_all))

def fn_reduces (level : ℕ) (f : EtaExpr) : Option ((f' : EtaExpr) × (PLift (FnEtaReduces level f f'))) :=
  if heq : ∃ f_α f_β, f = (DCCη Π(f_α, f_β)) then
    match _heq : f with
    | (DCCη Π(f_α, f_β)) =>
      match f_α.fn_reduces level.succ with
      | .some ⟨_, ⟨h₁⟩⟩ =>
        match f_β.fn_reduces level.succ.succ with
        | .some ⟨_, ⟨h₂⟩⟩ =>
          .some ⟨_, ⟨.pi h₁ h₂⟩⟩
        | _ => .none
      | _ => .none
  else
    if heq₂ : ∃ f', TmEtaReduces level f f' then
      match _heq₃ : f.eta_reduce_tm level with
      | .some ⟨_f', ⟨h⟩⟩ =>
        .some ⟨_, ⟨.tm heq h⟩⟩
      | .none => .none
    else
      .some ⟨_, ⟨.tm' heq heq₂⟩⟩

@[aesop safe forward (rule_sets := [DccReduce])]
theorem FnEtaReduces.complete (h : FnEtaReduces level f f') : fn_reduces level f = .some ⟨f', ⟨h⟩⟩ := by
  induction h
  case pi h₁ h₂ heq₁ heq₂ =>
    dsimp [fn_reduces]
    simp_all
  case tm heq h₁ =>
    have h₂ := h₁.complete
    unfold fn_reduces
    simp [heq]
    split
    case isTrue =>
      aesop
    case isFalse h =>
      exact (h ⟨_, (by assumption)⟩).elim
  case tm' heq₁ heq₂ =>
    unfold fn_reduces
    simp [heq₁, heq₂]

instance : Decidable (∃ f', FnEtaReduces level f f') :=
  if heq : (f.fn_reduces level).isSome then
    .isTrue ⟨_, ((f.fn_reduces level).get heq).snd.down⟩
  else
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

inductive ToExpr : (e : EtaExpr) → (e' : Expr) → Prop
  | top    : ToExpr (DCCη ⊤) (DCC ⊤)
  | bot    : ToExpr (DCCη ⊥) (DCC ⊥)
  | tintro : ToExpr (DCCη ∗) (DCC ∗)
  | sort   : ToExpr (DCCη Sort m) (DCC Sort m)
  | map    : ToExpr f f' → ToExpr (DCCη !<f>) (DCC !<f'>)
  | fmap   : ToExpr f f' → ToExpr (DCCη $<f>) (DCC $<f'>)
  | boxed  : ToExpr f f' → ToExpr (DCCη &(f)) (DCC &(f'))
  | unbox  : ToExpr f f' → ToExpr (DCCη *(f)) (DCC *(f'))
  | bang   : ToExpr f f' → ToExpr (DCCη !(f)) (DCC !(f'))
  | eval   : ToExpr α α' → ToExpr β β' → ToExpr x x' → ToExpr (DCCη Eval(α, β, x)) (DCC Eval(α', β', x'))
  | quot   : ToExpr β β' → ToExpr x x' → ToExpr (DCCη `(β, x)) (DCC `(β', x'))
  | id     : ToExpr f f' → ToExpr (DCCη Id(f)) (DCC Id(f'))
  | fstc   : ToExpr f f' → ToExpr (DCCη Fstc(f)) (DCC Fstc(f'))
  | sndc   : ToExpr f f' → ToExpr (DCCη Sndc(f)) (DCC Sndc(f'))
  | curr   : ToExpr α α' → ToExpr β β' → ToExpr x x' → ToExpr (DCCη Λ(α, β, x)) (DCC Λ(α', β', x'))
  | curr'  : ToExpr α α' → ToExpr β β' → ToExpr x x' → ToExpr (DCCη !Λ(α, β, x)) (DCC !Λ(α', β', x'))
  | sigma  : ToExpr β β' → ToExpr x x' → ToExpr (DCCη Σ(β, x)) (DCC Σ(β', x'))
  | eq     : ToExpr β β' → ToExpr x x' → ToExpr (DCCη β = x) (DCC β' = x')
  | eql    : ToExpr f f' → ToExpr (DCCη Eql(f)) (DCC Eql(f'))
  | refl   : ToExpr f f' → ToExpr (DCCη refl(f)) (DCC refl(f'))
  | comp'  : ToExpr β β' → ToExpr x x' → ToExpr (DCCη β ∘' x) (DCC β' ∘' x')
  | comp   : ToExpr β β' → ToExpr x x' → ToExpr (DCCη β ∘ x) (DCC β' ∘ x')
  | comp₂  : ToExpr β β' → ToExpr x x' → ToExpr (DCCη β ∘∘ x) (DCC β' ∘∘ x')
  | app    : ToExpr f f' → ToExpr x x' → ToExpr (DCCη (f x)) (DCC (f' x'))
  | pi     : ToExpr f f' → ToExpr x x' → ToExpr (DCCη Π(f, x)) (DCC Π(f', x'))
  | mk     : ToExpr α α' → ToExpr β β' → ToExpr x x' → ToExpr (DCCη ⟦α⟧(β, x)) (DCC ⟦α'⟧(β', x'))
  | coup   : ToExpr f f' → ToExpr (DCCη Coup(f)) (DCC Coup(f'))
  | pair   : ToExpr x x' → ToExpr y y' → ToExpr z z' → ToExpr (DCCη ⟦x⟧⟨y, z⟩) (DCC ⟦x'⟧⟨y', z'⟩)

def to_expr (e : EtaExpr) : Option ((e' : Expr) × PLift (ToExpr e e')) :=
  match e with
  | DCCη ∗ => .some ⟨_, ⟨.tintro⟩⟩
  | DCCη ⊤ => .some ⟨_, ⟨.top⟩⟩
  | DCCη ⊥ => .some ⟨_, ⟨.bot⟩⟩
  | DCCη x = y =>
    match x.to_expr, y.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.eq h₁ h₂⟩⟩
    | _, _ => .none
  | DCCη Eql(x)  =>
    match x.to_expr with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.eql h⟩⟩
    | _ => .none
  | DCCη refl(x) =>
    match x.to_expr with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.refl h⟩⟩
    | _ => .none
  | DCCη Sort _m => .some ⟨_, ⟨.sort⟩⟩
  | DCCη Σ(x, y) =>
    match x.to_expr, y.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.sigma h₁ h₂⟩⟩
    | _, _ => .none
  | DCCη `(x, y) =>
    match x.to_expr, y.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.quot h₁ h₂⟩⟩
    | _, _ => .none
  | DCCη ⟦x⟧(y, z) =>
    match x.to_expr, y.to_expr, z.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩, .some ⟨_, ⟨h₃⟩⟩ =>
      .some ⟨_, ⟨.mk h₁ h₂ h₃⟩⟩
    | _, _, _ => .none
  | DCCη Coup(x) =>
    match x.to_expr with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.coup h⟩⟩
    | _ => .none
  | DCCη Id(x)      =>
    match x.to_expr with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.id h⟩⟩
    | _ => .none
  | DCCη Fstc(x)    =>
    match x.to_expr with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.fstc h⟩⟩
    | _ => .none
  | DCCη Sndc(x)    =>
    match x.to_expr with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.sndc h⟩⟩
    | _ => .none
  | DCCη Π(x, y) =>
    match x.to_expr, y.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.pi h₁ h₂⟩⟩
    | _, _ => .none
  | DCCη (x ∘' y) =>
    match x.to_expr, y.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.comp' h₁ h₂⟩⟩
    | _, _ => .none
  | DCCη (x ∘ y)  =>
    match x.to_expr, y.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.comp h₁ h₂⟩⟩
    | _, _ => .none
  | DCCη (x ∘∘ y)  =>
    match x.to_expr, y.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.comp₂ h₁ h₂⟩⟩
    | _, _ => .none
  | DCCη ⟦x⟧⟨y, z⟩   =>
    match x.to_expr, y.to_expr, z.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩, .some ⟨_, ⟨h₃⟩⟩ =>
      .some ⟨_, ⟨.pair h₁ h₂ h₃⟩⟩
    | _, _, _ => .none
  | DCCη Λ(x, y, z) =>
    match x.to_expr, y.to_expr, z.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩, .some ⟨_, ⟨h₃⟩⟩ =>
      .some ⟨_, ⟨.curr h₁ h₂ h₃⟩⟩
    | _, _, _ => .none
  | DCCη !Λ(x, y, z) =>
    match x.to_expr, y.to_expr, z.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩, .some ⟨_, ⟨h₃⟩⟩ =>
      .some ⟨_, ⟨.curr' h₁ h₂ h₃⟩⟩
    | _, _, _ => .none
  | DCCη Eval(x, y, z) =>
    match x.to_expr, y.to_expr, z.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩, .some ⟨_, ⟨h₃⟩⟩ =>
      .some ⟨_, ⟨.eval h₁ h₂ h₃⟩⟩
    | _, _, _ => .none
  | DCCη !(x)   =>
    match x.to_expr with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.bang h⟩⟩
    | _ => .none
  | DCCη *(x)   =>
    match x.to_expr with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.unbox h⟩⟩
    | _ => .none
  | DCCη &(x)   =>
    match x.to_expr with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.boxed h⟩⟩
    | _ => .none
  | DCCη !<x>   =>
    match x.to_expr with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.map h⟩⟩
    | _ => .none
  | DCCη $<x>   =>
    match x.to_expr with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.fmap h⟩⟩
    | _ => .none
  | DCCη (x y) =>
    match x.to_expr, y.to_expr with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.app h₁ h₂⟩⟩
    | _, _ => .none
  | .hole _n => .none

theorem ToExpr.complete (h : ToExpr e e') : e.to_expr = .some ⟨e', ⟨h⟩⟩ := by
  induction h
  any_goals (
    focus
    simp [EtaExpr.to_expr]
    try simp_all)

end EtaExpr
