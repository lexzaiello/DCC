import Dcc.Eta.Ast
import Dcc.Aff.Red
import Dcc.Relation
import Dcc.Types

/-
Only η rule we probably also need is:

(Π(f_α, f_β) env)
f_α env -> f_α'

if env exists at the top level, we can reduce
f_βenv -> f_β'

this gives us the Id curry reduction for free to coerce arrows nicely.
Although lowkey I want to just try the type-checker first on examples to see what works.

If things don't work, then we can upgrade to the tracer matching

Alternative:
we could make Λ quotation the canonical quotation, not `(α, β), but see if everything works first.
debug examples
-/

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

inductive Domain₂ : EtaExpr → EtaExpr → EtaExpr → Prop
  | eql      : Domain f_α δ → (DCCη Eql(f_α)).Domain₂ δ f_α
  | refl     : Domain f_α δ → (DCCη refl(f_α)).Domain₂ δ f_α
  | curr     : Domain₂ (DCCη Λ(α, β, x)) α β
  | curr'    : Domain₂ (DCCη !Λ(α, β, x)) (DCCη !(α)) (DCCη !<β>)

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

def domain₂? (e : EtaExpr) : Option ((α β : EtaExpr) × (PULift.{1, 0} (Domain₂ e α β))) :=
  match e with
  | (DCCη Eql(f_α)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, _, ⟨.eql h⟩⟩
    | _ => .none
  | (DCCη refl(f_α)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, _, ⟨.refl h⟩⟩
    | _ => .none
  | (DCCη Λ(_α, _β, _x)) => .some ⟨_, _, ⟨.curr⟩⟩
  | (DCCη !Λ(_α, _β, _x)) => .some ⟨_, _, ⟨.curr'⟩⟩
  | _ => none

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

@[aesop safe forward (rule_sets := [DccReduce])]
theorem Domain₂.complete (h : Domain₂ e α β) : e.domain₂? = .some ⟨α, β, ⟨h⟩⟩ := by
  cases h with
  | refl h_domain | eql h_domain =>
    have h := h_domain.complete
    simp [domain₂?, h]
  | curr | curr' =>
    simp [domain₂?]

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

/-
TODO:
- arity 2
- handle !Λ with domain !(α), insert &(hole)
-/

inductive EtaMap₂ : (dom₁ : EtaExpr)
  -- β hole₁
  → (dom₂ : EtaExpr)
  → (out : EtaExpr)
  → (hole₁ : EtaExpr)
  → (hole₂ : EtaExpr)
  → (f' : EtaExpr) → Prop
  | par      : EtaMap₂ dom₁ dom₂ (DCCη (f hole₁ hole₂)) hole₁ hole₂ f
  | id       : EtaMap₂ dom₁ dom₂ (DCCη (hole₁ hole₂)) (DCCη hole₁) (DCCη hole₂) (DCCη Id(dom₁))
-- hole₁ hole₂ = ⟦dom₂⟧(hole₁, hole₂) means this is Λ(dom₁, dom₂, Id(Coup(dom₂)))
-- this is basically 2 arg version of id
  | curr     : EtaMap₂ dom₁ dom₂ (DCCη ⟦dom₂⟧(hole₁, hole₂)) hole₁ hole₂ (DCCη Λ(dom₁, dom₂, Id(Coup(dom₂))))
  | curr'    : EtaMap₂ (DCCη !(α)) (DCCη !<β>)
      (DCCη &(⟦β⟧(hole₁, hole₂)))
      (DCCη &(hole₁)) (DCCη &(hole₂))
      (DCCη !Λ(α, β, Id(!(Coup(β)))))
  -- Exclusive with other two
  -- this is couple quotation
  -- if dom₂ is quotation i.e., `(dom₁, dom₂), then
  -- this is just simple double quotation `(dom₁, `(dom₂, c))

-- TODO: might need quot₁ if β is not dependent on α
inductive TmEtaReduces₂ : (level : ℕ) → (f : EtaExpr) → (f' : EtaExpr) → Prop
  | quot₂    : Domain₂ f α₀ β₀
    → (EtaExpr.is_bang α₀ = .some α)
    → (EtaExpr.is_bang_map β₀ = .some β)
    → (¬ EtaExpr.contains e' (DCCη &(hole(level + 1))))
    → (¬ EtaExpr.contains e' (DCCη &(hole(level + 2))))
    → ReflTransGen RedAffEta (DCCη (f &(hole(level + 1)) &(hole(level + 2)))) e'
    → IsNorm RedAffEta e'
    → TmEtaReduces₂ level f (DCCη !Λ(α, β, `(!(Coup(β)), e')))
  | quot₂'   : Domain₂ f α β
    → (EtaExpr.is_quote β = .none)
    → (EtaExpr.is_bang α = .none)
    → (EtaExpr.is_bang_map β = .none)
    → (¬ EtaExpr.contains e' (DCCη hole(level + 1)))
    → (¬ EtaExpr.contains e' (DCCη hole(level + 2)))
    → ReflTransGen RedAffEta (DCCη (f hole(level + 1) hole(level + 2))) e'
    → IsNorm RedAffEta e'
    → TmEtaReduces₂ level f (DCCη Λ(α, β, `(Coup(β), e')))
  | quot₃'   : Domain₂ f α (DCCη `(α₂, β))
    → (EtaExpr.is_bang α = .none)
    → (EtaExpr.is_bang_map (DCCη `(α₂, β)) = .none)
    → (¬ EtaExpr.contains e' (DCCη hole(level + 1)))
    → (¬ EtaExpr.contains e' (DCCη hole(level + 2)))
    → ReflTransGen RedAffEta (DCCη (f hole(level + 1) hole(level + 2))) e'
    → IsNorm RedAffEta e'
    → TmEtaReduces₂ level f (DCCη `(α, `(β, e')))
  | map      : Domain₂ f α β
    → (EtaExpr.is_bang α = .none)
    → (EtaExpr.is_bang_map β = .none)
    → (EtaExpr.contains e' (DCCη hole(level + 1)) ∨ EtaExpr.contains e' (DCCη hole(level + 2)))
    → ReflTransGen RedAffEta (DCCη (f hole(level + 1) hole(level + 2))) e'
    → IsNorm RedAffEta e'
    → (EtaMap₂ α β e' (DCCη hole(level + 1)) (DCCη hole(level + 2)) f')
    → TmEtaReduces₂ level f f'

def map_eta₂ (dom₁ dom₂ out hole₁ hole₂ : EtaExpr) : Option ((f' : EtaExpr) × PLift
  (EtaMap₂ dom₁ dom₂ out hole₁ hole₂ f')) :=
  if heqa : out = (DCCη (hole₁ hole₂)) then by
    cases heqa
    exact .some ⟨_, ⟨.id⟩⟩
  else
    match heq₁ : out with
    | (DCCη (f hole₃ hole₄)) =>
      if heq₂ : (DCCη (f hole₃ hole₄)) = (DCCη (f hole₁ hole₂)) then by
        rw [heq₂]
        exact .some ⟨_, ⟨.par⟩⟩
      else .none
    | (DCCη ⟦dom₃⟧(hole₃, hole₄)) =>
      if heq₂ : (DCCη ⟦dom₃⟧(hole₃, hole₄)) = (DCCη ⟦dom₂⟧(hole₁, hole₂)) then by
        rw [heq₂]
        exact .some ⟨_, ⟨.curr⟩⟩
      else .none
    | (DCCη &(⟦β⟧(hole₃, hole₄))) =>
      match heq₂ : dom₁, heq₃ : dom₂, heq₄ : hole₁, heq₅ : hole₂ with
      | (DCCη !(α)), (DCCη !<β₂>), (DCCη &(ha)), (DCCη &(hb)) =>
        if heq₄ : (DCCη &(⟦β⟧(hole₃, hole₄))) = (DCCη &(⟦β₂⟧(ha, hb))) then by
          rw [heq₄]
          cases heq₄
          exact .some ⟨_, ⟨.curr'⟩⟩
        else .none
      | _, _, _, _ => .none
    | _ => .none

theorem EtaMap₂.complete (h : EtaExpr.EtaMap₂ dom₁ dom₂ out hole₁ hole₂ f') : map_eta₂ dom₁ dom₂ out hole₁ hole₂ = .some ⟨f', ⟨h⟩⟩ := by
  cases h
  case par =>
    dsimp [map_eta₂]
    simp
    intro h
    cases h
  case curr' | curr | id =>
    dsimp [map_eta₂]
    simp

def eta_reduce_tm₂ (level : ℕ) (f : EtaExpr) : Option ((f' : EtaExpr) × (PLift (TmEtaReduces₂ level f f'))) :=
  match heq : f.domain₂? with
  | .some ⟨α₀, β₀, ⟨h⟩⟩ =>
    if h_bang : (α₀.is_bang).isSome ∧ (β₀.is_bang_map).isSome then
      let e' := (reduce RedAffEta (DCCη (f &(hole(level + 1)) &(hole(level + 2))))).fst
      if h_contains : ¬ e'.contains (DCCη &(hole(level + 1)))
        ∧ ¬ e'.contains (DCCη &(hole(level + 2))) then by
        exact .some ⟨(DCCη !Λ(#(α₀.is_bang.get h_bang.left), #(β₀.is_bang_map.get h_bang.right), `(!(Coup(#(β₀.is_bang_map.get h_bang.right))), e'))), ⟨.quot₂ h (by
          simp_all) (by
            simp_all) h_contains.left h_contains.right
          (reduce_sound rfl) (reduce_norm rfl)⟩⟩
      else .none
    else
      let e' := (reduce RedAffEta (DCCη (f hole(level + 1) hole(level + 2)))).fst
      if h_contains : ¬ e'.contains (DCCη hole(level + 1))
        ∧ ¬ e'.contains (DCCη hole(level + 2)) then
        if h_bang : α₀.is_bang = .none ∧ β₀.is_bang_map = .none then
          if h_quot : β₀.is_quote.isSome then
            .some ⟨(DCCη `(α₀, `(#((β₀.is_quote.get h_quot).snd.fst), e'))),
              ⟨.quot₃' (α₂ := (β₀.is_quote.get h_quot).fst) (by
                have heq := ((β₀.is_quote.get h_quot).snd.snd).down
                rw [heq] at h
                exact h) h_bang.left (((β₀.is_quote.get h_quot).snd.snd).down ▸ h_bang.right) (by simp [h_contains.left]) (by simp [h_contains.right]) (reduce_sound rfl) (reduce_norm rfl)⟩⟩
          else
            .some ⟨(DCCη Λ(α₀, β₀, `(Coup(β₀), e'))),
              ⟨.quot₂' h (by simp_all) h_bang.left h_bang.right h_contains.left h_contains.right (reduce_sound rfl) (reduce_norm rfl)⟩⟩
        else .none
      else if h_contains : e'.contains (DCCη hole(level + 1))
        ∨ e'.contains (DCCη hole(level + 2)) then
        if h_bang : α₀.is_bang = .none ∧ β₀.is_bang_map = .none then
          match map_eta₂ α₀ β₀ e' (DCCη hole(level + 1)) (DCCη hole(level + 2)) with
          | .some ⟨f', ⟨hf⟩⟩ =>
            .some ⟨f', ⟨.map h h_bang.left h_bang.right h_contains (reduce_sound rfl) (reduce_norm rfl) hf⟩⟩
          | _ => .none
        else .none
      else .none
  | .none => .none

theorem TmEtaReduces₂.complete (h : TmEtaReduces₂ level f f') : eta_reduce_tm₂ level f = .some ⟨f', ⟨h⟩⟩ := by
  unfold eta_reduce_tm₂
  cases h with
  | quot₂ h_domain h₁ h₂ h_contains₁ h_contains₂ hr hn =>
    have h_red_complete := reduce_complete_fst hr hn
    have h := h_domain.complete
    simp_all
    rw [h]
    simp [h₁, h₂, h_red_complete]
    grind
  | quot₃' =>
    rename_i h₁ h₂ hn h_contains₁ h_contains₂ h_domain hr
    have h_red_complete := reduce_complete_fst hr hn
    have h := h_domain.complete
    simp_all
    rw [h]
    simp [h₁, h₂, is_quote, h_red_complete]
    grind
  | quot₂' =>
    rename_i h₁ h₂ hn h_contains₁ h_contains₂ h_domain hr
    have h_red_complete := reduce_complete_fst hr hn
    have h := h_domain.complete
    simp_all
    rw [h]
    simp [h₁, h₂]
    grind
  | map =>
    rename_i h_bang₁ h_bang₂ hn h_contains h_domain hr h_map
    have h_red_complete := reduce_complete_fst hr hn
    have h := h_domain.complete
    have hb := h_map.complete
    simp_all
    rw [h]
    simp [h_bang₁, h_bang₂]
    cases h_red_complete.symm
    cases h_contains with
    | inl hl => simp [hl, hb]
    | inr hr => simp [hr, hb]

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
  | tm    : Domain f τ
    → (¬ ∃ β, τ = (DCCη Coup(β)))
    → ReflTransGen RedAffEta (DCCη (f hole(level + 1))) e'
    → IsNorm RedAffEta e'
    → EtaResult τ e' (DCCη hole(level + 1)) f'
    → TmEtaReduces level f f'

instance : Decidable (∃ (β : EtaExpr), f = (DCCη Coup(β))) := by
  cases f
  case coup =>
    exact .isTrue (by aesop)
  any_goals (
    exact .isFalse (by
      intro ⟨_, heq⟩
      simp_all))

def eta_reduce_tm (level : ℕ) (f : EtaExpr) : Option ((f' : EtaExpr) × (PLift (TmEtaReduces level f f'))) :=
  match f.domain? with
  | .some ⟨τ, ⟨h₁⟩⟩ =>
    if heq : ∃ β, τ = (DCCη Coup(β)) then by
      cases τ
      case coup β =>
        match mk_eta_result (DCCη Coup(β))
          (reduce RedAffEta (DCCη (f ⟦β⟧(hole(level + 1), hole(level + 2))))).fst
          (DCCη ⟦β⟧(hole(level + 1), hole(level + 2))) with
        | .some ⟨_, ⟨h₂⟩⟩ =>
          exact .some ⟨_, ⟨.coupl h₁ (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
        | _ => exact .none
      any_goals (simp_all)
    else
      match mk_eta_result τ
        (reduce RedAffEta (DCCη (f hole(level + 1)))).fst
        (DCCη hole(level + 1)) with
      | .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.tm h₁ (by simp_all) (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
      | _ => .none
  | _ => .none

@[aesop safe forward (rule_sets := [DccReduce])]
theorem TmEtaReduces.complete (h : TmEtaReduces level f f') : eta_reduce_tm level f = .some ⟨f', ⟨h⟩⟩ := by
  dsimp [eta_reduce_tm]
  induction h
  case coupl =>
    rename_i f β level e' f' h_domain hr hn hmk
    have hb := h_domain.complete
    have ha := reduce_complete_fst hr hn
    have hc := hmk.complete
    simp_all
    cases ha
    simp_all
  any_goals (
    focus
    rename_i f τ level e' f' h_domain heq hr hn hmk
    have hb := h_domain.complete
    have ha := reduce_complete_fst hr hn
    have hc := hmk.complete
    simp_all
    cases ha
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

instance : Decidable (TmEtaReduces₂ level f f') :=
  if h : (f.eta_reduce_tm₂ level).isSome then
    if heq : ((f.eta_reduce_tm₂ level).get h).fst = f' then
      .isTrue (heq ▸ ((f.eta_reduce_tm₂ level).get h).snd.down)
    else
      .isFalse (fun h => by
        have h := h.complete
        simp_all)
  else
    .isFalse (fun h => by
      have h := h.complete
      simp_all)

instance : Decidable (∃ f', TmEtaReduces₂ level f f') :=
  if heq : (f.eta_reduce_tm₂ level).isSome then
    .isTrue ⟨_, ((f.eta_reduce_tm₂ level).get heq).snd.down⟩
  else
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

inductive FnEtaReduces : (level : ℕ) → (f : EtaExpr) → (f' : EtaExpr) → Prop
  | pi   : FnEtaReduces level.succ f_α f_α'
    → FnEtaReduces level.succ.succ f_β f_β'
    → FnEtaReduces level (DCCη Π(f_α, f_β)) (DCCη Π(f_α', f_β'))
  | tm₁  : (¬ ∃ f_α f_β, f = (DCCη Π(f_α, f_β)))
    → f.arity = 1
    → TmEtaReduces level f f'
    → FnEtaReduces level f f'
  | tm₂  : (¬ ∃ f_α f_β, f = (DCCη Π(f_α, f_β)))
    → f.arity = 2
    → TmEtaReduces₂ level f f'
    → FnEtaReduces level f f'
  | tm'₁ : (¬ ∃ f_α f_β, f = (DCCη Π(f_α, f_β)))
    → f.arity = 1
    → (¬ ∃ f', TmEtaReduces level f f')
    → FnEtaReduces level f f
  | tm'₂ : (¬ ∃ f_α f_β, f = (DCCη Π(f_α, f_β)))
    → f.arity = 2
    → (¬ ∃ f', TmEtaReduces₂ level f f')
    → FnEtaReduces level f f

instance : Decidable (∃ (f_α : EtaExpr) (f_β : EtaExpr), f = f_α.pi f_β) := by
  cases f
  case pi =>
    exact .isTrue (by aesop)
  any_goals (
    exact .isFalse (by
      intro ⟨_, _, heq⟩
      simp_all))

instance : Decidable (∃ (f_α : EtaExpr) (f_β : EtaExpr) (env : EtaExpr), f = (f_α.pi f_β).app env) := by
  cases f
  case app f x =>
    if heq : ∃ f_α f_β, f = (DCCη Π(f_α, f_β)) then
      exact .isTrue (by simp_all)
    else
      exact .isFalse (by
        simp_all)
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
    if harity : f.arity = 1 then
      if heq₂ : ∃ f', TmEtaReduces level f f' then
        match _heq₃ : f.eta_reduce_tm level with
        | .some ⟨_f', ⟨h⟩⟩ =>
          .some ⟨_, ⟨.tm₁ heq harity h⟩⟩
        | .none => .none
      else
        .some ⟨_, ⟨.tm'₁ heq harity heq₂⟩⟩
    else if harity : f.arity = 2 then
      if heq₂ : ∃ f', TmEtaReduces₂ level f f' then
        match _heq₃ : f.eta_reduce_tm₂ level with
        | .some ⟨_f', ⟨h⟩⟩ =>
          .some ⟨_, ⟨.tm₂ heq harity h⟩⟩
        | .none => .none
      else
        .some ⟨_, ⟨.tm'₂ heq harity heq₂⟩⟩
    else .none

@[aesop safe forward (rule_sets := [DccReduce])]
theorem FnEtaReduces.complete (h : FnEtaReduces level f f') : fn_reduces level f = .some ⟨f', ⟨h⟩⟩ := by
  induction h
  case pi h₁ h₂ heq₁ heq₂ =>
    dsimp [fn_reduces]
    simp_all
  case tm₁ heq harity h₁ =>
    have h₂ := h₁.complete
    unfold fn_reduces
    simp [heq, harity]
    split
    case isTrue =>
      aesop
    case isFalse h =>
      exact (h ⟨_, (by assumption)⟩).elim
  case tm₂ heq harity h₁ =>
    have h₂ := h₁.complete
    unfold fn_reduces
    simp [heq, harity]
    split
    case isTrue =>
      aesop
    case isFalse h =>
      exact (h ⟨_, (by assumption)⟩).elim
  case tm'₁ heq₁ harity heq₂ =>
    unfold fn_reduces
    simp [heq₁, heq₂, harity]
  case tm'₂ heq₁ harity heq₂ =>
    unfold fn_reduces
    simp [heq₁, heq₂, harity]

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

@[aesop safe forward (rule_sets := [DccReduce])]
theorem ToExpr.complete (h : ToExpr e e') : e.to_expr = .some ⟨e', ⟨h⟩⟩ := by
  induction h
  any_goals (
    focus
    simp [EtaExpr.to_expr]
    try simp_all)

instance : Decidable (∃ e', ToExpr e e') :=
  if heq : e.to_expr.isSome then
    .isTrue ⟨_, (e.to_expr.get heq).snd.down⟩
  else
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

end EtaExpr

namespace Expr

open EtaExpr

inductive ToEtaExpr : (e : Expr) → (e' : EtaExpr) → Prop
  | top    : ToEtaExpr (DCC ⊤) (DCCη ⊤)
  | bot    : ToEtaExpr (DCC ⊥) (DCCη ⊥)
  | tintro : ToEtaExpr (DCC ∗) (DCCη ∗)
  | sort   : ToEtaExpr (DCC Sort m) (DCCη Sort m)
  | map    : ToEtaExpr f f' → ToEtaExpr (DCC !<f>) (DCCη !<f'>)
  | fmap   : ToEtaExpr f f' → ToEtaExpr (DCC $<f>) (DCCη $<f'>)
  | boxed  : ToEtaExpr f f' → ToEtaExpr (DCC &(f)) (DCCη &(f'))
  | unbox  : ToEtaExpr f f' → ToEtaExpr (DCC *(f)) (DCCη *(f'))
  | bang   : ToEtaExpr f f' → ToEtaExpr (DCC !(f)) (DCCη !(f'))
  | eval   : ToEtaExpr α α' → ToEtaExpr β β' → ToEtaExpr x x' → ToEtaExpr (DCC Eval(α, β, x)) (DCCη Eval(α', β', x'))
  | quot   : ToEtaExpr β β' → ToEtaExpr x x' → ToEtaExpr (DCC `(β, x)) (DCCη `(β', x'))
  | id     : ToEtaExpr f f' → ToEtaExpr (DCC Id(f)) (DCCη Id(f'))
  | fstc   : ToEtaExpr f f' → ToEtaExpr (DCC Fstc(f)) (DCCη Fstc(f'))
  | sndc   : ToEtaExpr f f' → ToEtaExpr (DCC Sndc(f)) (DCCη Sndc(f'))
  | curr   : ToEtaExpr α α' → ToEtaExpr β β' → ToEtaExpr x x' → ToEtaExpr (DCC Λ(α, β, x)) (DCCη Λ(α', β', x'))
  | curr'  : ToEtaExpr α α' → ToEtaExpr β β' → ToEtaExpr x x' → ToEtaExpr (DCC !Λ(α, β, x)) (DCCη !Λ(α', β', x'))
  | sigma  : ToEtaExpr β β' → ToEtaExpr x x' → ToEtaExpr (DCC Σ(β, x)) (DCCη Σ(β', x'))
  | eq     : ToEtaExpr β β' → ToEtaExpr x x' → ToEtaExpr (DCC β = x) (DCCη β' = x')
  | eql    : ToEtaExpr f f' → ToEtaExpr (DCC Eql(f)) (DCCη Eql(f'))
  | refl   : ToEtaExpr f f' → ToEtaExpr (DCC refl(f)) (DCCη refl(f'))
  | comp'  : ToEtaExpr β β' → ToEtaExpr x x' → ToEtaExpr (DCC β ∘' x) (DCCη β' ∘' x')
  | comp   : ToEtaExpr β β' → ToEtaExpr x x' → ToEtaExpr (DCC β ∘ x) (DCCη β' ∘ x')
  | comp₂  : ToEtaExpr β β' → ToEtaExpr x x' → ToEtaExpr (DCC β ∘∘ x) (DCCη β' ∘∘ x')
  | app    : ToEtaExpr f f' → ToEtaExpr x x' → ToEtaExpr (DCC (f x)) (DCCη (f' x'))
  | pi     : ToEtaExpr f f' → ToEtaExpr x x' → ToEtaExpr (DCC Π(f, x)) (DCCη Π(f', x'))
  | mk     : ToEtaExpr α α' → ToEtaExpr β β' → ToEtaExpr x x' → ToEtaExpr (DCC ⟦α⟧(β, x)) (DCCη ⟦α'⟧(β', x'))
  | coup   : ToEtaExpr f f' → ToEtaExpr (DCC Coup(f)) (DCCη Coup(f'))
  | pair   : ToEtaExpr x x' → ToEtaExpr y y' → ToEtaExpr z z' → ToEtaExpr (DCC ⟦x⟧⟨y, z⟩) (DCCη ⟦x'⟧⟨y', z'⟩)

def to_eta_expr (e : Expr) : ((e' : EtaExpr) × PLift (ToEtaExpr e e')) :=
  match e with
  | DCC ∗ => ⟨_, ⟨.tintro⟩⟩
  | DCC ⊤ => ⟨_, ⟨.top⟩⟩
  | DCC ⊥ => ⟨_, ⟨.bot⟩⟩
  | DCC x = y =>
    match x.to_eta_expr, y.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩ =>
      ⟨_, ⟨.eq h₁ h₂⟩⟩
  | DCC Eql(x)  =>
    match x.to_eta_expr with
    | ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.eql h⟩⟩
  | DCC refl(x) =>
    match x.to_eta_expr with
    | ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.refl h⟩⟩
  | DCC Sort _m => ⟨_, ⟨.sort⟩⟩
  | DCC Σ(x, y) =>
    match x.to_eta_expr, y.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩ =>
      ⟨_, ⟨.sigma h₁ h₂⟩⟩
  | DCC `(x, y) =>
    match x.to_eta_expr, y.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩ =>
      ⟨_, ⟨.quot h₁ h₂⟩⟩
  | DCC ⟦x⟧(y, z) =>
    match x.to_eta_expr, y.to_eta_expr, z.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩, ⟨_, ⟨h₃⟩⟩ =>
      ⟨_, ⟨.mk h₁ h₂ h₃⟩⟩
  | DCC Coup(x) =>
    match x.to_eta_expr with
    | ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.coup h⟩⟩
  | DCC Id(x)      =>
    match x.to_eta_expr with
    | ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.id h⟩⟩
  | DCC Fstc(x)    =>
    match x.to_eta_expr with
    | ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.fstc h⟩⟩
  | DCC Sndc(x)    =>
    match x.to_eta_expr with
    | ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.sndc h⟩⟩
  | DCC Π(x, y) =>
    match x.to_eta_expr, y.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩ =>
      ⟨_, ⟨.pi h₁ h₂⟩⟩
  | DCC (x ∘' y) =>
    match x.to_eta_expr, y.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩ =>
      ⟨_, ⟨.comp' h₁ h₂⟩⟩
  | DCC (x ∘ y)  =>
    match x.to_eta_expr, y.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩ =>
      ⟨_, ⟨.comp h₁ h₂⟩⟩
  | DCC (x ∘∘ y)  =>
    match x.to_eta_expr, y.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩ =>
      ⟨_, ⟨.comp₂ h₁ h₂⟩⟩
  | DCC ⟦x⟧⟨y, z⟩   =>
    match x.to_eta_expr, y.to_eta_expr, z.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩, ⟨_, ⟨h₃⟩⟩ =>
      ⟨_, ⟨.pair h₁ h₂ h₃⟩⟩
  | DCC Λ(x, y, z) =>
    match x.to_eta_expr, y.to_eta_expr, z.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩, ⟨_, ⟨h₃⟩⟩ =>
      ⟨_, ⟨.curr h₁ h₂ h₃⟩⟩
  | DCC !Λ(x, y, z) =>
    match x.to_eta_expr, y.to_eta_expr, z.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩, ⟨_, ⟨h₃⟩⟩ =>
      ⟨_, ⟨.curr' h₁ h₂ h₃⟩⟩
  | DCC Eval(x, y, z) =>
    match x.to_eta_expr, y.to_eta_expr, z.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩, ⟨_, ⟨h₃⟩⟩ =>
      ⟨_, ⟨.eval h₁ h₂ h₃⟩⟩
  | DCC !(x)   =>
    match x.to_eta_expr with
    | ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.bang h⟩⟩
  | DCC *(x)   =>
    match x.to_eta_expr with
    | ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.unbox h⟩⟩
  | DCC &(x)   =>
    match x.to_eta_expr with
    | ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.boxed h⟩⟩
  | DCC !<x>   =>
    match x.to_eta_expr with
    | ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.map h⟩⟩
  | DCC $<x>   =>
    match x.to_eta_expr with
    | ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.fmap h⟩⟩
  | DCC (x y) =>
    match x.to_eta_expr, y.to_eta_expr with
    | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩ =>
      ⟨_, ⟨.app h₁ h₂⟩⟩

@[aesop safe forward (rule_sets := [DccReduce])]
theorem ToEtaExpr.complete (h : ToEtaExpr e e') : e.to_eta_expr = ⟨e', ⟨h⟩⟩ := by
  induction h
  any_goals (
    focus
    simp [Expr.to_eta_expr]
    try simp_all
    try aesop
    try grind)

inductive RedEta? : (e₁ : Expr) → (e₄ : Expr) → Prop
  | mk₁ : ToEtaExpr e₁ e₂ → FnEtaReduces 0 e₂ e₃ → ToExpr e₃ e₄ → RedEta? e₁ e₄
  | mk₂ : ToEtaExpr e₁ e₂ → FnEtaReduces 0 e₂ e₃ → (¬ ∃ e₄, ToExpr e₃ e₄) → RedEta? e₁ e₁

def red_eta? (e₁ : Expr) : Option ((e₄ : Expr) × PLift (RedEta? e₁ e₄)) :=
  if h₁ : ∃ e₃, FnEtaReduces 0 (to_eta_expr e₁).fst e₃ then
    match heq₀ : (to_eta_expr e₁).fst.fn_reduces 0 with
    | .some ⟨e', ⟨h₂⟩⟩ =>
      if h₃ : ∃ e'', ToExpr e' e'' then
        match heq : e'.to_expr with
        | .some ⟨_, ⟨h₃⟩⟩ =>
          .some ⟨_, ⟨.mk₁ (to_eta_expr e₁).snd.down h₂ h₃⟩⟩
        | .none => .some ⟨_, ⟨.mk₂ (to_eta_expr e₁).snd.down h₂ (fun ⟨_, h⟩ => by
          have h := h.complete
          simp_all)⟩⟩
      else
        .some ⟨_, ⟨.mk₂ (to_eta_expr e₁).snd.down h₂ (fun ⟨_, h⟩ => by
          have h := h.complete
          simp_all)⟩⟩
    | .none => .none
  else
    .none

@[aesop safe forward (rule_sets := [DccReduce])]
theorem RedEta?.complete (h : RedEta? e e') : e.red_eta? = .some ⟨e', ⟨h⟩⟩ := by
  unfold red_eta?
  induction h
  case mk₁ h₁ h₂ h₃ =>
    have ha := h₁.complete
    have hb := h₂.complete
    have hc := h₃.complete
    rename_i e₂ e₃ e₄
    have h₄ : e.to_eta_expr.fst = e₂ := by
      simp_all
    have hh : ∃ ee, FnEtaReduces 0 e.to_eta_expr.fst ee := ⟨e₃, by
      simp_all⟩
    have hhh : ∃ e', ToExpr e₃ e' := ⟨e₄, by
      simp_all⟩
    simp [h₄]
    cases h₄
    simp [hh]
    rw [hb]
    simp
    simp [hhh]
    simp at *
    aesop
  case mk₂ e₂ e₃ h₁ h₂ h₃ =>
    have ha := h₁.complete
    have hb := h₂.complete
    have h : e.to_eta_expr.fst = e₂ := by
      simp_all
    have hh : ∃ ee, FnEtaReduces 0 e.to_eta_expr.fst ee := ⟨e₃, by
      simp_all⟩
    simp [ha]
    cases h
    simp [hh]
    cases ha
    split
    · simp_all
    · simp_all

instance : Decidable (∃ e', RedEta? e e') :=
  match heq : e.red_eta? with
  | .some ⟨_, ⟨h⟩⟩ => .isTrue ⟨_, h⟩
  | .none =>
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

instance : Decidable (∃ (f_α : Expr) (f_β : Expr), f = f_α.pi f_β) := by
  cases f
  case pi =>
    exact .isTrue (by aesop)
  any_goals (
    exact .isFalse (by
      intro ⟨_, _, heq⟩
      simp_all))

instance : Decidable (∃ (f_α : Expr) (f_β : Expr) (env : Expr), f = (f_α.pi f_β).app env) := by
  cases f
  case app f x =>
    if heq : ∃ f_α f_β, f = (DCC Π(f_α, f_β)) then
      exact .isTrue (by simp_all)
    else
      exact .isFalse (by
        simp_all)
  any_goals (
    exact .isFalse (by
      intro ⟨_, _, heq⟩
      simp_all))

inductive RedEta?? : (e : Expr) → (e' : Expr) → Prop
  | pi₁  : RedEta?? f_α f_α'
    → ToEtaExpr f_α f_α₁
    → Domain f_α₁ δ
    → ToExpr δ δ'
    → RedEta?? env env'
    → RedEta?? (DCC (f_β env)) f_β'
    → (f_β' ≠ (DCC (f_β env)))
    → RedEta?? (DCC (Π(f_α, f_β) env)) (DCC (Π(f_α', `(δ', f_β')) env'))
  | pi₁'  : RedEta?? f_α f_α'
    → ToEtaExpr f_α f_α₁
    → Domain f_α₁ δ
    → ToExpr δ δ'
    → RedEta?? env env'
    → RedEta?? (DCC (f_β env)) f_β'
    → (f_β' = (DCC (f_β env)))
    → RedEta?? (DCC (Π(f_α, f_β) env)) (DCC (Π(f_α', f_β) env'))
  | pi₂  : RedEta?? f_α f_α'
    → RedEta?? f_β f_β'
    → RedEta?? (DCC Π(f_α, f_β)) (DCC Π(f_α', f_β'))
  | tm₁  : (¬ ∃ f_α f_β env, e = (DCC (Π(f_α, f_β) env)))
    → (¬ ∃ f_α f_β, e = (DCC (Π(f_α, f_β))))
    → RedEta? e e' → RedEta?? e e'
  | tm₂  : (¬ ∃ f_α f_β env, e = (DCC (Π(f_α, f_β) env)))
    → (¬ ∃ f_α f_β, e = (DCC (Π(f_α, f_β))))
    → (¬ ∃ e', RedEta? e e')
    → Relation.ReflTransGen RedAff e e'
    → IsNorm RedAff e'
    → RedEta?? e e

def red_eta?? (e : Expr) : Option ((e' : Expr) × (PLift (RedEta?? e e'))) :=
  if heq : ∃ f_α f_β env, e = (DCC (Π(f_α, f_β) env)) then
    match e with
    | (DCC (Π(f_α, f_β) env)) =>
      let ⟨f_α₁, ⟨h₁⟩⟩ := f_α.to_eta_expr
      match f_α₁.domain? with
      | .some ⟨δ, ⟨h₂⟩⟩ =>
        match δ.to_expr with
        | .some ⟨δ', ⟨h₃⟩⟩ =>
          match env.red_eta??, f_α.red_eta??, (DCC (f_β env)).red_eta?? with
          | .some ⟨_, ⟨h₄⟩⟩, .some ⟨f_α', ⟨h₅⟩⟩, .some ⟨f_β', ⟨h₆⟩⟩ =>
            if heq : f_β' = (DCC (f_β env)) then
              .some ⟨_, ⟨.pi₁' h₅ h₁ h₂ h₃ h₄ h₆ heq⟩⟩
            else
              .some ⟨_, ⟨.pi₁ h₅ h₁ h₂ h₃ h₄ h₆ heq⟩⟩
          | _, _, _ => .none
        | _ => .none
      | _ => .none
  else
    if heq₂ : ∃ f_α f_β, e = (DCC Π(f_α, f_β)) then
      match e with
      | (DCC Π(f_α, f_β)) =>
        match f_α.red_eta??, f_β.red_eta?? with
        | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.pi₂ h₁ h₂⟩⟩
        | _, _ => .none
    else
      if heq₃ : ∃ e', RedEta? e e' then
        match _heq₄ : e.red_eta? with
        | .some ⟨_, ⟨h⟩⟩ =>
          .some ⟨_, ⟨.tm₁ heq heq₂ h⟩⟩
        | _ => .none
      else
        .some ⟨_, ⟨.tm₂ heq heq₂ heq₃ (reduce_sound rfl) (reduce_norm rfl)⟩⟩

@[aesop safe forward (rule_sets := [DccReduce])]
theorem RedEta??.complete (h : RedEta?? e e') : e.red_eta?? = .some ⟨e', ⟨h⟩⟩ := by
  induction h
  case pi₁ =>
    rename_i f_α f_α' f_α₁ δ δ' env env' f_β f_β' h₁ to_eta_expr h_domain h_to_expr h₃ h₄ hneq heq₁ heq₂ heq₃
    have heq₄ := to_eta_expr.complete
    have heq₅ := h_domain.complete
    have heq₆ : f_α.to_eta_expr.fst = f_α₁ := by
      simp_all
    have heq₇ := h_to_expr.complete
    unfold red_eta??
    simp
    simp [heq₁, heq₂, heq₃]
    cases heq₆
    simp [heq₅]
    simp_all
  case pi₁' =>
    rename_i f_α f_α' f_α₁ δ δ' env env' f_β f_β' h₁ to_eta_expr h_domain h_to_expr h₃ h₄ hneq heq₁ heq₂ heq₃
    have heq₄ := to_eta_expr.complete
    have heq₅ := h_domain.complete
    have heq₆ : f_α.to_eta_expr.fst = f_α₁ := by
      simp_all
    have heq₇ := h_to_expr.complete
    unfold red_eta??
    simp
    simp [heq₁, heq₂, heq₃]
    cases heq₆
    simp [heq₅]
    simp_all
  case pi₂ =>
    rename_i f_α f_α' f_β f_β' h₁ h₂ heq₁ heq₂
    unfold red_eta??
    simp
    simp [heq₁, heq₂]
  case tm₁ e₀ e'' hn₁ hn₂ h =>
    have he : ∃ e', RedEta? e₀ e' := by
      exact ⟨_, h⟩
    have h₁ := h.complete
    unfold red_eta??
    simp [hn₁, hn₂, he]
    rw [h₁]
  case tm₂ hn₁ hn₂ hn₃ hr hnorm =>
    have h₁ := reduce_complete hr hnorm
    rw [red_eta??]
    simp [hn₁, hn₂, hn₃]

instance : Decidable (∃ e', RedEta?? e e') :=
  match heq : e.red_eta?? with
  | .some ⟨_, ⟨h⟩⟩ => .isTrue ⟨_, h⟩
  | .none =>
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

inductive RedEta : Expr → Expr → Prop
  | refl : (¬ ∃ e', RedEta?? e e') → RedEta e e
  | step : RedEta?? e e' → RedEta e e'

def red_eta (e : Expr) : ((e' : Expr) × (PLift (RedEta e e'))) :=
  match heq₂ : e.red_eta?? with
  | .some ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.step h⟩⟩
  | .none => ⟨_, ⟨.refl (fun ⟨_, h⟩ => by
    have h := h.complete
    simp_all)⟩⟩

theorem RedEta.complete (h : RedEta e e') : e.red_eta = ⟨e', ⟨h⟩⟩ := by
  cases h
  case refl hn =>
    unfold red_eta
    split
    case h_1 hr _ => exact (hn ⟨_, hr⟩).elim
    · rfl
  case step h =>
    have h := h.complete
    simp [red_eta]
    split
    case h_1 =>
      simp_all
      grind
    · simp_all

/-
Top-level Π rule:

If Domain f_α = δ
and f_β env η-reduces to f_β', then

f_β' = `(δ, f_β')
-/

@[dcc_force_reduce]
theorem reduce_eta_sound (_heq : Expr.red_eta e = ⟨e', ⟨h⟩⟩) : Expr.RedEta e e' := h

@[dcc_force_reduce]
abbrev red_eta' (e : Expr) : Expr := e.red_eta.fst

#eval (DCC Id(Sort 1) ∘' Id(Sort 1)).red_eta.fst
#eval (DCC `(Sort 1, Sort 1)).red_eta.fst
#eval (DCC Id(Sort 1)).red_eta.fst
#eval (DCC Λ(Sort 1, Id(Sort 1), Id(Coup(Id(Sort 1))) ∘' Id(Coup(Id(Sort 1))))).red_eta.fst
#eval Sigma.fst <| reduce RedAffEta (DCCη (Λ(Sort 1, Id(Sort 1), Sndc(Coup(Id(Sort 1)))) hole(1) hole(2)))
#eval (DCC (Λ(Sort 1, Id(Sort 1), Sndc(Coup(Id(Sort 1)))) (Sort 0))).red_eta.fst
#eval (DCC Eql(Id(Sort 2))).red_eta.fst
#eval (DCC Eql(Id(Sort 2))).red_eta.fst
#eval (DCC ((Sort 0 : Sort 1) → Sort 2)).raw_repr
#eval (DCC (Λ(Sort 1, `(Sort 1, Sort 2), `(Coup(`(Sort 1, Sort 2)), (Sort 3))))).red_eta.fst
#eval (DCC (Π(Id(Sort 3) ∘' Id(Sort 3), `(Sort 3, Π(!<Id(Sort 2)>, Eql(Id(Sort 2))))) !(Sort 2))).red_eta.fst
#eval (DCC (Π(Id(Sort 3) ∘' Id(Sort 3), `(Sort 3, Π(!<Id(Sort 2)>, Eql(Id(Sort 2)))) ∘' Id(Sort 3)) !(Sort 2))).red_eta.fst

end Expr
