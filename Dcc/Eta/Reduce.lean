import Dcc.Eta.Ast
import Dcc.Aff.Red
import Dcc.Relation
import Dcc.Types
import Mathlib.Logic.Equiv.Defs

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

namespace GenericExpr

open Relation (ReflTransGen)
open GenericExpr (IsNorm decreasing? reduce RedRel reduce_norm reduce_sound norm_unique Complete reduce_complete reduce_complete_fst)

inductive Domain.{u} {τ_c : Type u} : GenericExpr (@EtaConst τ_c) → GenericExpr (@EtaConst τ_c) → Prop
  | eql₁     : Domain f_α δ → (DCC? Eql(f_α)).Domain (DCC? !(δ))
  | eql₂     : ReflTransGen (RedAff (τ := @EtaConst τ_c)) (DCC? (f_α &(env))) τ
    → IsNorm (RedAff (τ := @EtaConst τ_c)) τ
    → Domain (DCC? (Eql(f_α) &(env))) τ
  | refl₁    : Domain f_α δ → (DCC? refl(f_α)).Domain (DCC? !(δ))
  | refl₂    : ReflTransGen (RedAff (τ := @EtaConst τ_c)) (DCC? (f_α &(env))) τ
    → IsNorm (RedAff (τ := @EtaConst τ_c)) τ
    → Domain (DCC? (refl(f_α) &(env))) τ
  | unmap    : Domain f α → Domain (DCC? *<f>) (DCC? !(α))
  | unbox    : Domain (DCC? *(α)) (DCC? !(α))
  | id       : Domain (DCC? Id(α)) α
  | fstc     : Domain (DCC? Fstc(β)) (DCC? Coup(β))
  | sndc     : Domain (DCC? Sndc(β)) (DCC? Coup(β))
  | curr₁    : Domain (DCC? Λ(α, β, x)) α
  | curr₂    : ReflTransGen (RedAff (τ := @EtaConst τ_c)) (DCC? (β y)) τ
    → IsNorm (RedAff (τ := @EtaConst τ_c)) τ
    → Domain (DCC? (Λ(α, β, x) y)) τ
  | curr₁'   : Domain (DCC? !Λ(α, β, x)) (DCC? !(α))
  | curr₂'   : ReflTransGen (RedAff (τ := @EtaConst τ_c)) (DCC? (β y)) τ
  → IsNorm (RedAff (τ := @EtaConst τ_c)) τ
  → Domain (DCC? (!Λ(α, β, x) &(y))) (DCC? !(τ))
  | map      : Domain f α → Domain (DCC? !<f>) (DCC? !(α))
  | fmap     : Domain f α → Domain (DCC? $<f>) (DCC? !(α))
  | pair     : Domain M α → Domain (DCC? ⟦β⟧⟨M, N⟩) α
  /-
  TODO: Not sure how to fit Eval in here yet
  | eval     : Val.Domain Val(λ env 2 => f) α → Val.Domain Val(
  | eval     : Apply x y f'
    → Apply f' z e'
    → Apply Val(λ env 1 => Eval(_α, _β, x)) Val(neutral(⟦__β⟧(y, z))) e'-/
  | quot     : Domain (DCC? `(β, x)) β
  -- f ∘ g x
  -- again, need to handle second round
  -- can use β-reducer for this.
  | comp'    : Domain g α → Domain (DCC? f ∘' g) α
  | comp     : Domain g α → Domain (DCC? f ∘ g) α
  | comp₂    : Domain g α → Domain (DCC? f ∘∘ g) α
  | pi       : Domain f_α δ → Domain (DCC? Π(f_α, f_β)) δ

inductive Domain₂.{u} {τ_c : Type u} : GenericExpr (@EtaConst τ_c) → GenericExpr (@EtaConst τ_c) → GenericExpr (@EtaConst τ_c) → Prop
  | comp'    : Domain g α → Domain₂ f β γ → Domain₂ (DCC? (f ∘' g)) α (DCC? γ ∘' g)
  | eql      : Domain f_α δ → (DCC? Eql(f_α)).Domain₂ δ f_α
  | refl     : Domain f_α δ → (DCC? refl(f_α)).Domain₂ δ f_α
  | curr     : Domain₂ (DCC? Λ(α, β, x)) α β
  | curr'    : Domain₂ (DCC? !Λ(α, β, x)) (DCC? !(α)) (DCC? !<β>)

@[dcc_force_reduce, dcc_force_aff]
def domain?.{u} {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr (@EtaConst τ_c)) : Option ((τ : GenericExpr (@EtaConst τ_c)) × (PULift.{1, 0} (Domain e τ))) :=
  match e with
  | (DCC? Eql(f_α)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.eql₁ h⟩⟩
    | _ => .none
  | (DCC? (Eql(_f_α) &(_env))) => .some ⟨_, ⟨.eql₂ (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? refl(f_α)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.refl₁ h⟩⟩
    | _ => .none
  | (DCC? (refl(_f_α) &(_env))) => .some ⟨_, ⟨.refl₂ (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? *<f>) =>
    match f.domain? with
    | .some ⟨_, ⟨h⟩⟩ =>
      .some ⟨_, ⟨.unmap h⟩⟩
    | _ => .none
  | (DCC? *(_α)) => .some ⟨_, ⟨.unbox⟩⟩
  | (DCC? Id(_α)) => .some ⟨_, ⟨.id⟩⟩
  | (DCC? Fstc(_β)) => .some ⟨_, ⟨.fstc⟩⟩
  | (DCC? Sndc(_β)) => .some ⟨_, ⟨.sndc⟩⟩
  | (DCC? Λ(_α, _β, _x)) => .some ⟨_, ⟨.curr₁⟩⟩
  | (DCC? (Λ(_α, _β, _x) _y)) => .some ⟨_, ⟨.curr₂ (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? !Λ(_α, _β, _x)) => .some ⟨_, ⟨.curr₁'⟩⟩
  | (DCC? (!Λ(_α, _β, _x) &(_y))) => .some ⟨_, ⟨.curr₂' (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? !<f>) =>
    match f.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.map h⟩⟩
    | _ => .none
  | (DCC? $<f>) =>
    match f.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.fmap h⟩⟩
    | _ => .none
  | (DCC? ⟦_β⟧⟨M, _N⟩) =>
    match M.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pair h⟩⟩
    | _ => .none
  | (DCC? `(_β, _x)) => .some ⟨_, ⟨.quot⟩⟩
  | (DCC? _f ∘' g) =>
    match g.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp' h⟩⟩
    | _ => .none
  | (DCC? _f ∘ g) =>
    match g.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp h⟩⟩
    | _ => .none
  | (DCC? _f ∘∘ g) =>
    match g.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp₂ h⟩⟩
    | _ => .none
  | (DCC? Π(f_α, _f_β)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi h⟩⟩
    | _ => .none
  | _ => .none

def domain₂?.{u} {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr (@EtaConst τ_c)) : Option ((α β : GenericExpr (@EtaConst τ_c)) × (PULift.{1, 0} (Domain₂ e α β))) :=
  match e with
  | DCC? f ∘' g =>
    match g.domain?, f.domain₂? with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, _, ⟨h₂⟩⟩ =>
      .some ⟨_, _, ⟨.comp' h₁ h₂⟩⟩
    | _, _ => .none
  | (DCC? Eql(f_α)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, _, ⟨.eql h⟩⟩
    | _ => .none
  | (DCC? refl(f_α)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, _, ⟨.refl h⟩⟩
    | _ => .none
  | (DCC? Λ(_α, _β, _x)) => .some ⟨_, _, ⟨.curr⟩⟩
  | (DCC? !Λ(_α, _β, _x)) => .some ⟨_, _, ⟨.curr'⟩⟩
  | _ => none

@[aesop safe forward (rule_sets := [DccReduce])]
theorem Domain.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {e τ : GenericExpr (@EtaConst τ_c)} (h : Domain e τ) : (domain? (τ_c := τ_c)) e = .some ⟨τ, ⟨h⟩⟩ := by
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
theorem Domain₂.complete.{u} {τ_c : Type u} [DecidableEq τ_c]
  {e α β : GenericExpr (@EtaConst τ_c)} (h : Domain₂ e α β) : e.domain₂? = .some ⟨α, β, ⟨h⟩⟩ := by
  induction h with
  | comp' h₁ h₂ ih => simp [domain₂?, ih, h₁.complete]
  | refl h_domain | eql h_domain =>
    have h := h_domain.complete
    simp [domain₂?, h]
  | curr | curr' =>
    simp [domain₂?]

@[dcc_force_reduce, dcc_force_aff]
instance Domain.instRedRel.{u} {τ_c : Type u} [DecidableEq τ_c] : GenericExpr.RedRel (Domain (τ_c := τ_c)) size where
  run := domain?

theorem Domain.deterministic.{u} {τ_c : Type u} {x τ₁ τ₂ : GenericExpr (τ := EtaConst (τ := τ_c))} (h₁ : Domain (τ_c := τ_c) x τ₁) (h₂ : Domain (τ_c := τ_c) x τ₂) : τ₁ = τ₂ := by
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
theorem Domain.conf.{u} {τ_c : Type u} {A B C : GenericExpr (τ := EtaConst (τ := τ_c))} (h₁ : Domain A B) (h₂ : Domain A C) : ∃ D, ReflTransGen Domain B D ∧ ReflTransGen Domain C D := by
  cases h₁.deterministic h₂
  exact ⟨_, .refl, .refl⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance Domain.instConf.{u} {τ_c : Type u} : GenericExpr.Confluent (Domain (τ_c := τ_c)) := ⟨Domain.conf⟩

def Domain.semi_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {A B : GenericExpr (τ := EtaConst (τ := τ_c))}
  (hr : A.Domain B) : ∃ B', ∃ (h : A.Domain B'), (domain? A) = .some ⟨B', ⟨h⟩⟩ := by
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
  case h_22 =>
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

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance Domain.instSemicomplete.{u} {τ_c : Type u} [DecidableEq τ_c] : GenericExpr.SemiComplete (Domain (τ_c := τ_c)) := ⟨Domain.semi_complete⟩

theorem domain_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {A B : GenericExpr (τ := EtaConst (τ := τ_c))} (h : Relation.ReflTransGen Domain A B)
  (hn : GenericExpr.IsNorm Domain B) : GenericExpr.reduce (Domain (τ_c := τ_c)) A = ⟨B, ⟨h⟩⟩ :=
  Domain.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance Domain.instComplete.{u} {τ_c : Type u} [DecidableEq τ_c] : Complete (Relation.ReflTransGen (Domain (τ_c := τ_c))) (P := GenericExpr.IsNorm Domain) := Domain.instRedRel.instComplete

inductive EtaMap.{u} {τ_c : Type u} : (dom : GenericExpr (τ := EtaConst (τ := τ_c))) → (out : GenericExpr (τ := EtaConst (τ := τ_c))) → (hole_arg : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | id    : EtaMap dom hole_arg hole_arg (DCC? Id(dom))
  | par   : EtaMap dom (DCC? (f hole_arg)) hole_arg f
  | fstc  : EtaMap dom (DCC? &(hole(a))) (DCC? ⟦β⟧(&(hole(a)), &(hole(a + 1)))) (DCC? Fstc(β))
  | sndc  : EtaMap dom (DCC? &(hole(a + 1))) (DCC? ⟦β⟧(&(hole(a)), &(hole(a + 1)))) (DCC? Sndc(β))
  | fstc' : EtaMap dom (DCC? hole(a)) (DCC? ⟦β⟧(&(hole(a)), &(hole(a + 1)))) (DCC? *<Fstc(β)>)
  | sndc' : EtaMap dom (DCC? hole(a + 1)) (DCC? ⟦β⟧(&(hole(a)), &(hole(a + 1)))) (DCC? *<Sndc(β)>)

/-
hole(a) hole(a + 1)

⟦β⟧(hole(a), hole(a + 1))

This is canonically Eval id

but does it require pair?


pair is superfluous

there is some canonical eta reduction for eval.
for one thing, self application is invalid.
so hole(1) hole(1)
is not valid.

From curien's paper

App ∘ ⟨x ∘ Λ, z⟩

If ⟦β⟧(hole(1), hole(2))

reduces to hole(2) !(⊤). this eta-reduction absolutely works.
the order is just kinda wacky.

no this is fine. because our sorts are wrapped in quotation for the environment.
absolutely do the eta rule.

but the order is swapped. why did that happen?

can we change the type of ∘∘?
probably not.
-/

def map_eta.{u} {τ_c : Type u} [DecidableEq τ_c] (dom : GenericExpr (τ := EtaConst (τ := τ_c))) (out : GenericExpr (τ := EtaConst (τ := τ_c))) (hole_arg : GenericExpr (τ := EtaConst (τ := τ_c))) : Option ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × PLift (EtaMap dom out hole_arg f')) :=
  if heq : out = hole_arg then
    heq ▸ .some ⟨_, ⟨.id⟩⟩
  else
    match out, hole_arg with
    | DCC? (_f hole_arg₂), hole_arg =>
      if heq : hole_arg₂ = hole_arg then
        heq ▸ .some ⟨_, ⟨.par⟩⟩
      else .none
    | (DCC? &(hole(n))), (DCC? ⟦_β⟧(&(hole(a)), &(hole(b)))) =>
      if h₁ : b = a + 1 then
        if h₂ : n = a then by
          cases h₁; cases h₂
          exact .some ⟨_, ⟨.fstc⟩⟩
        else if h₂ : n = a + 1 then by
          cases h₁; cases h₂
          exact .some ⟨_, ⟨.sndc⟩⟩
        else .none
      else .none
    | (DCC? hole(n)), (DCC? ⟦_β⟧(&(hole(a)), &(hole(b)))) =>
      if h₁ : b = a + 1 then
        if h₂ : n = a then by
          cases h₁; cases h₂
          exact .some ⟨_, ⟨.fstc'⟩⟩
        else if h₂ : n = a + 1 then by
          cases h₁; cases h₂
          exact .some ⟨_, ⟨.sndc'⟩⟩
        else .none
      else .none
    | _, _ => .none

@[aesop safe forward (rule_sets := [DccReduce])]
theorem EtaMap.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {dom out hole_arg f' : GenericExpr (τ := EtaConst (τ := τ_c))}
  (h : EtaMap (τ_c := τ_c) dom out hole_arg f') : map_eta dom out hole_arg = .some ⟨f', ⟨h⟩⟩ := by
  dsimp [map_eta]
  cases h
  any_goals (simp)
  · intro h
    cases h

@[aesop safe forward (rule_sets := [DccReduce])]
inductive EtaResult.{u} {τ_c : Type u} [BEq τ_c] : (dom : GenericExpr (τ := EtaConst (τ := τ_c))) → (out : GenericExpr (τ := EtaConst (τ := τ_c))) → (hole_arg : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | map   : (GenericExpr.contains out hole_arg)
    → EtaMap dom out hole_arg f'
    → EtaResult dom out hole_arg f'
  | quot  : (¬ GenericExpr.contains out hole_arg)
    → EtaResult dom out hole_arg (DCC? `(dom, out))

/-
TODO:
- arity 2
- handle !Λ with domain !(α), insert &(hole)
-/

inductive EtaMap₂.{u} {τ_c : Type u} : (dom₁ : GenericExpr (τ := EtaConst (τ := τ_c)))
  -- β hole₁
  → (dom₂ : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (out : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (hole₁ : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (hole₂ : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | par      : EtaMap₂ dom₁ dom₂ (DCC? (f hole₁ hole₂)) hole₁ hole₂ f
  | id       : EtaMap₂ dom₁ dom₂ (DCC? (hole₁ hole₂)) (DCC? hole₁) (DCC? hole₂) (DCC? Id(dom₁))
-- hole₁ hole₂ = ⟦dom₂⟧(hole₁, hole₂) means this is Λ(dom₁, dom₂, Id(Coup(dom₂)))
-- this is basically 2 arg version of id
  | curr     : EtaMap₂ dom₁ dom₂ (DCC? ⟦dom₂⟧(hole₁, hole₂)) hole₁ hole₂ (DCC? Λ(dom₁, dom₂, Id(Coup(dom₂))))
  | curr'    : EtaMap₂ (DCC? !(α)) (DCC? !<β>)
      (DCC? &(⟦β⟧(hole₁, hole₂)))
      (DCC? &(hole₁)) (DCC? &(hole₂))
      (DCC? !Λ(α, β, Id(!(Coup(β)))))
  -- Exclusive with other two
  -- this is couple quotation
  -- if dom₂ is quotation i.e., `(dom₁, dom₂), then
  -- this is just simple double quotation `(dom₁, `(dom₂, c))

inductive TmEtaReduces.{u} {τ_c : Type u} [BEq τ_c] : (level : ℕ) → (f : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | coupl : Domain f (DCC? Coup(β))
    → ReflTransGen RedAff (DCC? (f ⟦β⟧(&(hole(level + 1)), &(hole(level + 2))))) e'
    → IsNorm RedAff e'
    → EtaResult (DCC? Coup(β)) e' (DCC? ⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))) f'
    → TmEtaReduces level f f'
  | tm    : Domain f τ
    → (¬ ∃ β, τ = (DCC? Coup(β)))
    → (¬ ∃ β, τ = (DCC? !(Coup(β))))
    → ReflTransGen RedAff (DCC? (f hole(level + 1))) e'
    → IsNorm RedAff e'
    → EtaResult τ e' (DCC? hole(level + 1)) f'
    → TmEtaReduces level f f'
  | bang₁ : Domain f (DCC? !(Coup(β)))
    → ReflTransGen RedAff (DCC? (f &(⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))))) e'
    → IsNorm RedAff e'
    → EtaResult (DCC? !(Coup(β))) e' (DCC? &(⟦β⟧(&(hole(level + 1)), &(hole(level + 2))))) f'
    → TmEtaReduces level f f'

def mk_eta_result.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c] (dom : GenericExpr (τ := EtaConst (τ := τ_c)))
  (out : GenericExpr (τ := EtaConst (τ := τ_c))) (hole_arg : GenericExpr (τ := EtaConst (τ := τ_c))) : Option ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × PLift (EtaResult dom out hole_arg f')) :=
  if h₁ : out.contains hole_arg then
    match map_eta dom out hole_arg with
    | .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.map h₁ h₂⟩⟩
    | _ => .none
  else
    .some ⟨_, ⟨.quot h₁⟩⟩

instance decExistsCoupE.{u} {τ : Type u} {f : GenericExpr (τ := τ)} : Decidable (∃ (β : GenericExpr (τ := τ)), f = (DCC? Coup(β))) := by
  cases f
  case coup =>
    exact .isTrue (by aesop)
  any_goals (
    exact .isFalse (by
      intro ⟨_, heq⟩
      simp_all))

instance : Decidable (∃ (β : GenericExpr τ), f = (DCC? !(Coup(β)))) := by
  cases f
  case bang x =>
    cases x
    case coup =>
      exact .isTrue (by aesop)
    any_goals (
      exact .isFalse (by
        intro ⟨_, heq⟩
        simp_all))
  any_goals (
    exact .isFalse (by
      intro ⟨_, heq⟩
      simp_all))

def eta_reduce_tm.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c] (level : ℕ)
  (f : GenericExpr (τ := EtaConst (τ := τ_c))) : Option ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × (PLift (TmEtaReduces level f f'))) :=
  match f.domain? with
  | .some ⟨τ, ⟨h₁⟩⟩ =>
    if heq : ∃ β, τ = (DCC? Coup(β)) then by
      cases τ
      case coup β =>
        match mk_eta_result (DCC? Coup(β))
          (reduce RedAff (DCC? (f ⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))))).fst
          (DCC? ⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))) with
        | .some ⟨_, ⟨h₂⟩⟩ =>
          exact .some ⟨_, ⟨.coupl h₁ (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
        | _ => exact .none
      any_goals (simp_all)
    else if heq₂ : ∃ β, τ = (DCC? !(Coup(β))) then by
      cases τ
      case bang β =>
        cases β
        case coup β =>
          match mk_eta_result (DCC? !(Coup(β)))
            (reduce RedAff (DCC? (f &(⟦β⟧(&(hole(level + 1)), &(hole(level + 2))))))).fst
            (DCC? &(⟦β⟧(&(hole(level + 1)), &(hole(level + 2))))) with
          | .some ⟨_, ⟨h₂⟩⟩ =>
            exact .some ⟨_, ⟨.bang₁ h₁ (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
          | _ => exact .none
        any_goals (simp_all)
      any_goals (simp_all)
    else
      match mk_eta_result τ
        (reduce RedAff (DCC? (f hole(level + 1)))).fst
        (DCC? hole(level + 1)) with
      | .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.tm h₁ (by simp_all) (by simp_all) (reduce_sound rfl) (reduce_norm rfl) h₂⟩⟩
      | _ => .none
  | _ => .none

-- TODO: might need quot₁ if β is not dependent on α
inductive TmEtaReduces₂.{u} {τ_c : Type u} [BEq τ_c] : (level : ℕ) → (f : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | quot₂    : Domain₂ f α₀ β₀
    → (GenericExpr.is_bang α₀ = .some α)
    → (GenericExpr.is_bang_map β₀ = .some β)
    → (¬ GenericExpr.contains e' (DCC? &(hole(level + 1))))
    → (¬ GenericExpr.contains e' (DCC? &(hole(level + 2))))
    → ReflTransGen RedAff (DCC? (f &(hole(level + 1)) &(hole(level + 2)))) e'
    → IsNorm RedAff e'
    → TmEtaReduces₂ level f (DCC? !Λ(α, β, `(!(Coup(β)), e')))
  | quot₂'   : Domain₂ f α f_β
    → (GenericExpr.is_quote f_β = .none)
    → (GenericExpr.is_bang α = .none)
    → (GenericExpr.is_bang_map f_β = .none)
    → (¬ GenericExpr.contains e' (DCC? hole(level + 1)))
    → (¬ GenericExpr.contains e' (DCC? hole(level + 2)))
    → ReflTransGen RedAff (DCC? (f hole(level + 1) hole(level + 2))) e'
    → IsNorm RedAff e'
    → TmEtaReduces₂ level f (DCC? Λ(α, f_β, `(Coup(f_β), e')))
  | quot₃'   : Domain₂ f α (DCC? `(α₂, β))
    → (GenericExpr.is_bang α = .none)
    → (¬ GenericExpr.contains e' (DCC? hole(level + 1)))
    → (¬ GenericExpr.contains e' (DCC? hole(level + 2)))
    → ReflTransGen RedAff (DCC? (f hole(level + 1) hole(level + 2))) e'
    → IsNorm RedAff e'
    → TmEtaReduces₂ level f (DCC? `(α, `(β, e')))
  | map      : Domain₂ f α β
    → (GenericExpr.is_bang α = .none)
    → (GenericExpr.is_bang_map β = .none)
    → (GenericExpr.contains e' (DCC? hole(level + 1)) ∨ GenericExpr.contains e' (DCC? hole(level + 2)))
    → ReflTransGen RedAff (DCC? (f hole(level + 1) hole(level + 2))) e'
    → IsNorm RedAff e'
    → (EtaMap₂ α β e' (DCC? hole(level + 1)) (DCC? hole(level + 2)) f')
    → TmEtaReduces₂ level f f'

def map_eta₂.{u} {τ_c : Type u} [DecidableEq τ_c] (dom₁ dom₂ out hole₁ hole₂ : GenericExpr (τ := EtaConst (τ := τ_c))) : Option
  ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × PLift
  (EtaMap₂ dom₁ dom₂ out hole₁ hole₂ f')) :=
  if heqa : out = (DCC? (hole₁ hole₂)) then by
    cases heqa
    exact .some ⟨_, ⟨.id⟩⟩
  else
    match heq₁ : out with
    | (DCC? (f hole₃ hole₄)) =>
      if heq₂ : (DCC? (f hole₃ hole₄)) = (DCC? (f hole₁ hole₂)) then by
        rw [heq₂]
        exact .some ⟨_, ⟨.par⟩⟩
      else .none
    | (DCC? ⟦dom₃⟧(hole₃, hole₄)) =>
      if heq₂ : (DCC? ⟦dom₃⟧(hole₃, hole₄)) = (DCC? ⟦dom₂⟧(hole₁, hole₂)) then by
        rw [heq₂]
        exact .some ⟨_, ⟨.curr⟩⟩
      else .none
    | (DCC? &(⟦β⟧(hole₃, hole₄))) =>
      match heq₂ : dom₁, heq₃ : dom₂, heq₄ : hole₁, heq₅ : hole₂ with
      | (DCC? !(α)), (DCC? !<β₂>), (DCC? &(ha)), (DCC? &(hb)) =>
        if heq₄ : (DCC? &(⟦β⟧(hole₃, hole₄))) = (DCC? &(⟦β₂⟧(ha, hb))) then by
          rw [heq₄]
          cases heq₄
          exact .some ⟨_, ⟨.curr'⟩⟩
        else .none
      | _, _, _, _ => .none
    | _ => .none

theorem EtaMap₂.complete.{u} {τ_c : Type u} [DecidableEq τ_c]
  {dom₁ dom₂ out hole₁ hole₂ f' : GenericExpr (τ := EtaConst (τ := τ_c))} (h : GenericExpr.EtaMap₂ (τ_c := τ_c) dom₁ dom₂ out hole₁ hole₂ f') : map_eta₂ dom₁ dom₂ out hole₁ hole₂ = .some ⟨f', ⟨h⟩⟩ := by
  cases h
  case par =>
    dsimp [map_eta₂]
    simp
    intro h
    cases h
  case curr' | curr | id =>
    dsimp [map_eta₂]
    simp

def eta_reduce_tm₂.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c] (level : ℕ) (f : GenericExpr (τ := EtaConst (τ := τ_c))) : Option ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × (PLift (TmEtaReduces₂ level f f'))) :=
  match heq : f.domain₂? with
  | .some ⟨α₀, β₀, ⟨h⟩⟩ =>
    if h_bang : (α₀.is_bang).isSome ∧ (β₀.is_bang_map).isSome then
      let e' := (reduce RedAff (DCC? (f &(hole(level + 1)) &(hole(level + 2))))).fst
      if h_contains : ¬ e'.contains (DCC? &(hole(level + 1)))
        ∧ ¬ e'.contains (DCC? &(hole(level + 2))) then by
        exact .some ⟨(DCC? !Λ(#(α₀.is_bang.get h_bang.left), #(β₀.is_bang_map.get h_bang.right), `(!(Coup(#(β₀.is_bang_map.get h_bang.right))), e'))), ⟨.quot₂ h (by
          simp_all) (by
            simp_all) h_contains.left h_contains.right
          (reduce_sound rfl) (reduce_norm rfl)⟩⟩
      else .none
    else
      let e' := (reduce RedAff (DCC? (f hole(level + 1) hole(level + 2)))).fst
      if h_contains : ¬ e'.contains (DCC? hole(level + 1))
        ∧ ¬ e'.contains (DCC? hole(level + 2)) then
        if h_bang : α₀.is_bang = .none then
          match h_quot_eq₀ : β₀.is_quote with
          | .some ⟨α₂, β, ⟨h_quot_eq⟩⟩ =>
            .some ⟨_,
              ⟨.quot₃'
                (h_quot_eq ▸ h)
                h_bang
                (by
                  change ¬e'.contains _
                  simp [h_contains.left])
                (by
                  change ¬e'.contains _
                  simp [h_contains.right])
                  (reduce_sound rfl)
                  (reduce_norm rfl)⟩⟩
          | .none =>
            if h_bang₂ : β₀.is_bang_map = .none then
              .some ⟨_,
                ⟨.quot₂'
                  h
                  h_quot_eq₀
                  h_bang h_bang₂ h_contains.left h_contains.right (reduce_sound rfl) (reduce_norm rfl)⟩⟩
            else .none
        else .none
      else if h_contains : e'.contains (DCC? hole(level + 1))
        ∨ e'.contains (DCC? hole(level + 2)) then
        if h_bang : α₀.is_bang = .none ∧ β₀.is_bang_map = .none then
          match map_eta₂ α₀ β₀ e' (DCC? hole(level + 1)) (DCC? hole(level + 2)) with
          | .some ⟨f', ⟨hf⟩⟩ =>
            .some ⟨f', ⟨.map h h_bang.left h_bang.right h_contains (reduce_sound rfl) (reduce_norm rfl) hf⟩⟩
          | _ => .none
        else .none
      else .none
  | .none => .none

#eval (repr ∘ Sigma.fst) <$> (DCC? ((Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)) ∘'
                         Fstc(Π(Sndc(`(⊤, Sort 1)),
                                Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                      Fstc((Sndc(`(⊤, Sort 1)) ∘'
                              Fstc(Π(Sndc(`(⊤, Sort 1)),
                                     Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                       `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))))).eta_reduce_tm₂ (τ_c := Unit) 0

#eval (repr ∘ Sigma.fst) <$> (DCC? ((Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)) ∘'
                         Fstc(Π(Sndc(`(⊤, Sort 1)),
                                Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))) ∘'
                      Fstc((Sndc(`(⊤, Sort 1)) ∘'
                              Fstc(Π(Sndc(`(⊤, Sort 1)),
                                     Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)),
                                       `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))))))).domain₂? (τ_c := Unit)

theorem EtaResult.complete.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c]
  {dom out hole_arg f' : GenericExpr (τ := EtaConst (τ := τ_c))} (h : EtaResult (τ_c := τ_c) dom out hole_arg f') : mk_eta_result dom out hole_arg = .some ⟨f', ⟨h⟩⟩ := by
  dsimp [mk_eta_result]
  cases h <;> aesop (rule_sets := [DccReduce])

@[aesop safe forward (rule_sets := [DccReduce])]
theorem TmEtaReduces.complete.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c] {f f' : GenericExpr (τ := EtaConst (τ := τ_c))}
  (h : TmEtaReduces (τ_c := τ_c) level f f') : eta_reduce_tm level f = .some ⟨f', ⟨h⟩⟩ := by
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
  case bang₁ =>
    rename_i f β level e' f' h_domain hr hn hmk
    have hb := h_domain.complete
    have ha := reduce_complete_fst hr hn
    have hc := hmk.complete
    simp_all
    cases ha
    simp_all
  any_goals (
    focus
    rename_i f τ level e' f' h_domain heq heq₂ hr hn hmk
    have hb := h_domain.complete
    have ha := reduce_complete_fst hr hn
    have hc := hmk.complete
    simp_all
    cases ha
    simp_all)

theorem TmEtaReduces₂.complete.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c] {f f' : GenericExpr (τ := EtaConst (τ := τ_c))}
  (h : TmEtaReduces₂ (τ_c := τ_c) level f f') : eta_reduce_tm₂ level f = .some ⟨f', ⟨h⟩⟩ := by
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
    rename_i α α₂ β e' h_bang hn h_contains₁ h_contains₂ h_domain hr
    have h_red_complete := reduce_complete_fst hr hn
    have h := h_domain.complete
    rw [h]
    simp
    simp [h_bang, h_red_complete, h_contains₁, h_contains₂, is_quote]
    grind
  | quot₂' =>
    rename_i α β e' h_quote h_bang h_bang_map hn h_contains₁ h_contains₂ h_domain hr
    have h_red_complete := reduce_complete_fst hr hn
    have h := h_domain.complete
    rw [h]
    simp
    simp [h_bang, h_red_complete, h_contains₁, h_contains₂]
    simp [h_bang_map]
    split
    · simp_all
    case h_2 =>
      simp_all
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

instance TmEtaReduces.instDecidable.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c]
  {f f' : GenericExpr (τ := EtaConst (τ := τ_c))} : Decidable (TmEtaReduces (τ_c := τ_c) level f f') :=
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

instance TmEtaReduces.instExistsDecidable.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c]
  {f : GenericExpr (τ := EtaConst (τ := τ_c))} : Decidable (∃ f', TmEtaReduces (τ_c := τ_c) level f f') :=
  if heq : (f.eta_reduce_tm level).isSome then
    .isTrue ⟨_, ((f.eta_reduce_tm level).get heq).snd.down⟩
  else
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

instance TmEtaReduces₂.instDecidable.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c]
  {f f' : GenericExpr (τ := EtaConst (τ := τ_c))} : Decidable (TmEtaReduces₂ (τ_c := τ_c) level f f') :=
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

instance TmEtaReduces₂.instExistsDecidable.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c]
  {f : GenericExpr (τ := EtaConst (τ := τ_c))} : Decidable (∃ f', TmEtaReduces₂ (τ_c := τ_c) level f f') :=
  if heq : (f.eta_reduce_tm₂ level).isSome then
    .isTrue ⟨_, ((f.eta_reduce_tm₂ level).get heq).snd.down⟩
  else
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

inductive FnEtaReduces.{u} {τ_c : Type u} [BEq τ_c] : (level : ℕ) →
  (f : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | pi   : FnEtaReduces level.succ f_α f_α'
    → FnEtaReduces level.succ.succ f_β f_β'
    → FnEtaReduces level (DCC? Π(f_α, f_β)) (DCC? Π(f_α', f_β'))
  | tm₁  : (¬ ∃ f_α f_β, f = (DCC? Π(f_α, f_β)))
    → f.arity = 1
    → TmEtaReduces level f f'
    → FnEtaReduces level f f'
  | tm₂  : (¬ ∃ f_α f_β, f = (DCC? Π(f_α, f_β)))
    → f.arity = 2
    → TmEtaReduces₂ level f f'
    → FnEtaReduces level f f'
  | tm'₁ : (¬ ∃ f_α f_β, f = (DCC? Π(f_α, f_β)))
    → f.arity = 1
    → (¬ ∃ f', TmEtaReduces level f f')
    → FnEtaReduces level f f
  | tm'₂ : (¬ ∃ f_α f_β, f = (DCC? Π(f_α, f_β)))
    → f.arity = 2
    → (¬ ∃ f', TmEtaReduces₂ level f f')
    → FnEtaReduces level f f

instance instExistsPiDecidable : Decidable (∃ (f_α : GenericExpr τ) (f_β : GenericExpr τ), f = f_α.pi f_β) := by
  cases f
  case pi =>
    exact .isTrue (by aesop)
  any_goals (
    exact .isFalse (by
      intro ⟨_, _, heq⟩
      simp_all))

instance : Decidable (∃ (f_α : GenericExpr τ) (f_β : GenericExpr τ) (env : GenericExpr τ), f = (f_α.pi f_β).app env) := by
  cases f
  case app f x =>
    if heq : ∃ f_α f_β, f = (DCC? Π(f_α, f_β)) then
      exact .isTrue (by simp_all)
    else
      exact .isFalse (by
        simp_all)
  any_goals (
    exact .isFalse (by
      intro ⟨_, _, heq⟩
      simp_all))

def fn_reduces.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c] (level : ℕ) (f : GenericExpr (τ := EtaConst (τ := τ_c))) : Option
  ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × (PLift (FnEtaReduces level f f'))) :=
  if heq : ∃ f_α f_β, f = (DCC? Π(f_α, f_β)) then
    match _heq : f with
    | (DCC? Π(f_α, f_β)) =>
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
theorem FnEtaReduces.complete.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c]
  {f f' : GenericExpr (τ := EtaConst (τ := τ_c))}
  (h : FnEtaReduces level f f') : fn_reduces (τ_c := τ_c) level f = .some ⟨f', ⟨h⟩⟩ := by
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

instance FnEtaReduces.instExistsDecidable.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c]
  {f : GenericExpr (τ := EtaConst (τ := τ_c))} : Decidable (∃ f', FnEtaReduces level f f') :=
  if heq : (f.fn_reduces level).isSome then
    .isTrue ⟨_, ((f.fn_reduces level).get heq).snd.down⟩
  else
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

/-
New ToExpr is quite simple, since eta expr and expr are just

GenericExpr τ vs GenericExpr (EtaConst τ)
-/

def eta_to_expr.{u} {τ_c : Type u} (e : GenericExpr (τ := EtaConst (τ := τ_c)))
  (hn_contains : ¬ e.contains_hole) : GenericExpr τ_c :=
  match e with
  | DCC? ∗ => DCC? ∗
  | DCC? ⊤ => DCC? ⊤
  | DCC? ⊥ => DCC? ⊥
  | DCC? x = y =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' => (DCC? x' = y')
  | DCC? Eql(x)  =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? Eql(x'))
  | DCC? refl(x) =>
    match x.eta_to_expr (by simp_all [contains_hole])with
    | x' => (DCC? refl(x'))
  | DCC? Sort _m => (DCC? Sort _m)
  | DCC? Σ(x, y) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' => (DCC? Σ(x', y'))
  | DCC? `(x, y) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' => (DCC? `(x', y'))
  | DCC? ⟦x⟧(y, z) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]), z.eta_to_expr (by simp_all [contains_hole]) with
    | x', y', z' => (DCC? ⟦x'⟧(y', z'))
  | DCC? Coup(x) =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? Coup(x'))
  | DCC? Id(x)      =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? Id(x'))
  | DCC? Fstc(x)    =>
    match x.eta_to_expr (by simp_all [contains_hole])with
    | x' => (DCC? Fstc(x'))
  | DCC? Sndc(x)    =>
    match x.eta_to_expr (by simp_all [contains_hole])with
    | x' => (DCC? Sndc(x'))
  | DCC? Π(x, y) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' =>
      (DCC? Π(x', y'))
  | DCC? (x ∘' y) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' =>
      (DCC? x' ∘' y')
  | DCC? (x ∘ y)  =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' =>
      (DCC? x' ∘ y')
  | DCC? (x ∘∘ y)  =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' =>
      (DCC? x' ∘∘ y')
  | DCC? ⟦x⟧⟨y, z⟩   =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]), z.eta_to_expr (by simp_all [contains_hole]) with
    | x', y', z' =>
      (DCC? ⟦x'⟧⟨y', z'⟩)
  | DCC? Λ(x, y, z) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]), z.eta_to_expr (by simp_all [contains_hole]) with
    | x', y', z' =>
      (DCC? Λ(x', y', z'))
  | DCC? !Λ(x, y, z) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]), z.eta_to_expr (by simp_all [contains_hole]) with
    | x', y', z' =>
      (DCC? !Λ(x', y', z'))
  | DCC? Eval(x, y, z) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]), z.eta_to_expr (by simp_all [contains_hole]) with
    | x', y', z' =>
      (DCC? Eval(x', y', z'))
  | DCC? !(x)   =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? !(x'))
  | DCC? *(x)   =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? *(x'))
  | DCC? *<x>   =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? *<x'>)
  | DCC? &(x)   =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? &(x'))
  | DCC? !<x>   =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? !<x'>)
  | DCC? $<x>   =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? $<x'>)
  | DCC? (x y) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' =>
      (DCC? (x' y'))
  | .const (.hole _) => by simp_all [contains_hole]
  | .const (.const x) => (.const x)

def expr_to_eta.{u} {τ_c : Type u} (e : GenericExpr (τ := τ_c)) : (GenericExpr (τ := EtaConst (τ := τ_c))) :=
  match e with
  | DCC? ∗ => DCC? ∗
  | DCC? ⊤ => DCC? ⊤
  | DCC? ⊥ => DCC? ⊥
  | DCC? x = y =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' => (DCC? x' = y')
  | DCC? Eql(x)  =>
    match x.expr_to_eta with
    | x' => (DCC? Eql(x'))
  | DCC? refl(x) =>
    match x.expr_to_eta with
    | x' => (DCC? refl(x'))
  | DCC? Sort _m => (DCC? Sort _m)
  | DCC? Σ(x, y) =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? Σ(x', y'))
  | DCC? `(x, y) =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? `(x', y'))
  | DCC? ⟦x⟧(y, z) =>
    match x.expr_to_eta, y.expr_to_eta, z.expr_to_eta with
    | x', y', z' =>
      (DCC? ⟦x'⟧(y', z'))
  | DCC? Coup(x) =>
    match x.expr_to_eta with
    | x' => (DCC? Coup(x'))
  | DCC? Id(x)      =>
    match x.expr_to_eta with
    | x' => (DCC? Id(x'))
  | DCC? Fstc(x)    =>
    match x.expr_to_eta with
    | x' => (DCC? Fstc(x'))
  | DCC? Sndc(x)    =>
    match x.expr_to_eta with
    | x' => (DCC? Sndc(x'))
  | DCC? Π(x, y) =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? Π(x', y'))
  | DCC? (x ∘' y) =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? x' ∘' y')
  | DCC? (x ∘ y)  =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? x' ∘ y')
  | DCC? (x ∘∘ y)  =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? x' ∘∘ y')
  | DCC? ⟦x⟧⟨y, z⟩   =>
    match x.expr_to_eta, y.expr_to_eta, z.expr_to_eta with
    | x', y', z' =>
      (DCC? ⟦x'⟧⟨y', z'⟩)
  | DCC? Λ(x, y, z) =>
    match x.expr_to_eta, y.expr_to_eta, z.expr_to_eta with
    | x', y', z' =>
      (DCC? Λ(x', y', z'))
  | DCC? !Λ(x, y, z) =>
    match x.expr_to_eta, y.expr_to_eta, z.expr_to_eta with
    | x', y', z' =>
      (DCC? !Λ(x', y', z'))
  | DCC? Eval(x, y, z) =>
    match x.expr_to_eta, y.expr_to_eta, z.expr_to_eta with
    | x', y', z' =>
      (DCC? Eval(x', y', z'))
  | DCC? !(x)   =>
    match x.expr_to_eta with
    | x' => (DCC? !(x'))
  | DCC? *(x)   =>
    match x.expr_to_eta with
    | x' => (DCC? *(x'))
  | DCC? *<x>   =>
    match x.expr_to_eta with
    | x' => (DCC? *<x'>)
  | DCC? &(x)   =>
    match x.expr_to_eta with
    | x' => (DCC? &(x'))
  | DCC? !<x>   =>
    match x.expr_to_eta with
    | x' => (DCC? !<x'>)
  | DCC? $<x>   =>
    match x.expr_to_eta with
    | x' => (DCC? $<x'>)
  | DCC? (x y) =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? (x' y'))
  | .const x => (.const (.const x))

inductive RedEta?.{u} {τ_c : Type u} [hdecEq : DecidableEq τ_c] [hBEq : BEq τ_c] : (e₁ : GenericExpr (τ := τ_c)) → (e₄ : GenericExpr (τ := τ_c)) → Prop
  | mk₁ : FnEtaReduces 0 (expr_to_eta e₁) e₃ → (hn : ¬ e₃.contains_hole) → RedEta? e₁ (eta_to_expr e₃ hn)
  | mk₂ : FnEtaReduces 0 (expr_to_eta e₁) e₃ → (hn : e₃.contains_hole)   → RedEta? e₁ e₁

def red_eta?.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c] (e₁ : GenericExpr τ_c) : Option ((e₄ : GenericExpr τ_c) × PLift (RedEta? e₁ e₄)) :=
  if ∃ e₃, FnEtaReduces 0 (expr_to_eta e₁) e₃ then
    match (expr_to_eta e₁).fn_reduces 0 with
    | .some ⟨e', ⟨h₂⟩⟩ =>
      if h_contains : e'.contains_hole then
        .some ⟨_, ⟨.mk₂ h₂ h_contains⟩⟩
      else .some ⟨_, ⟨.mk₁ h₂ h_contains⟩⟩
    | .none => .none
  else
    .none

@[aesop safe forward (rule_sets := [DccReduce])]
theorem RedEta?.complete.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {e e' : GenericExpr (τ := τ_c)} (h : RedEta? e e') : e.red_eta? = .some ⟨e', ⟨h⟩⟩ := by
  unfold red_eta?
  induction h
  case mk₁ h₁ h₂ | mk₂ h₁ h₂ =>
    have ha := h₁.complete
    have hh : ∃ e₃, FnEtaReduces 0 (expr_to_eta e) e₃ := ⟨_, h₁⟩
    grind

instance RedEta?.instDecidable.{u} {τ_c : Type u} [hdecEq : DecidableEq τ_c] [hBEq : BEq τ_c] {e : GenericExpr (τ := τ_c)} : Decidable (∃ e', RedEta? (hdecEq := hdecEq) (hBEq := hBEq) e e') :=
  match heq : e.red_eta? with
  | .some ⟨_, ⟨h⟩⟩ => .isTrue ⟨_, h⟩
  | .none =>
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

instance : Decidable (∃ (f_α : GenericExpr τ) (f_β : GenericExpr τ), f = f_α.pi f_β) := by
  cases f
  case pi =>
    exact .isTrue (by aesop)
  any_goals (
    exact .isFalse (by
      intro ⟨_, _, heq⟩
      simp_all))

instance : Decidable (∃ (f_α : GenericExpr τ) (f_β : GenericExpr τ) (env : GenericExpr τ), f = (f_α.pi f_β).app env) := by
  cases f
  case app f x =>
    if heq : ∃ f_α f_β, f = (DCC? Π(f_α, f_β)) then
      exact .isTrue (by simp_all)
    else
      exact .isFalse (by
        simp_all)
  any_goals (
    exact .isFalse (by
      intro ⟨_, _, heq⟩
      simp_all))

instance : Decidable (∃ (g f_α f_β : GenericExpr τ), f = (f_α.pi f_β).comp' g) := by
  cases f
  case comp' f g =>
    cases f
    case pi =>
      exact .isTrue (by aesop)
    any_goals (
      exact .isFalse (by
        intro ⟨_, _, heq⟩
        simp_all))
  any_goals (
    exact .isFalse (by
      intro ⟨_, _, heq⟩
      simp_all))

instance : Decidable (∃ (β : GenericExpr τ), f = (DCC? Coup(β))) := by
  cases f
  case coup =>
    exact .isTrue (by aesop)
  any_goals (
    exact .isFalse (by
      intro ⟨_, heq⟩
      simp_all))

instance : Decidable (∃ (α : GenericExpr τ), e = (DCC? Id(α))) := by
  cases e
  case id =>
    exact .isTrue (by aesop)
  any_goals (
    exact .isFalse (by
      intro ⟨_, heq⟩
      simp_all))

instance : Decidable (∃ (α : GenericExpr τ), e = (DCC? !(α))) := by
  cases e
  case bang =>
    exact .isTrue (by aesop)
  any_goals (
    exact .isFalse (by
      intro ⟨_, heq⟩
      simp_all))

inductive RedEta??.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] : (e : GenericExpr (τ := τ_c)) → (e' : GenericExpr (τ := τ_c)) → Prop
  | pi₁  : RedEta?? f_α f_α'
    → Domain (expr_to_eta f_α) δ
    → (hn : ¬ δ.contains_hole)
    → RedEta?? env env'
    → Relation.ReflTransGen RedAff (DCC? (f_β env)) f_β_env
    → IsNorm RedAff f_β_env
    → RedEta?? f_β_env f_β'
    → (f_β' ≠ (DCC? (f_β env)))
    → RedEta?? (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', `(#(eta_to_expr δ hn), f_β')) env'))
  | coup  : RedEta?? β β' → RedEta?? (DCC? Coup(β)) (DCC? Coup(β'))
  | bang  : RedEta?? β β' → RedEta?? (DCC? !(β)) (DCC? !(β'))
  | pi₁'  : RedEta?? f_α f_α'
    → Domain (expr_to_eta f_α) δ
    → (hn : ¬ δ.contains_hole)
    → RedEta?? env env'
    → Relation.ReflTransGen RedAff (DCC? (f_β env)) f_β_env
    → IsNorm RedAff f_β_env
    → RedEta?? f_β_env f_β'
    → (f_β' = (DCC? (f_β env)))
    → RedEta?? (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', f_β) env'))
  | pi₂  : RedEta?? f_α f_α'
    → RedEta?? f_β f_β'
    → RedEta?? (DCC? Π(f_α, f_β)) (DCC? Π(f_α', f_β'))
  | pi₃  : Relation.ReflTransGen RedAff (DCC? f_α) f_α₁
    → IsNorm RedAff f_α₁
    → RedEta?? (DCC? (f_α₁ ∘' g)) f_α'
    → Relation.ReflTransGen RedAff (DCC? f_β) f_β₁
    → IsNorm RedAff f_β₁
    → RedEta?? (DCC? (f_β₁ ∘' g)) f_β'
    → RedEta?? (DCC? (Π(f_α, f_β) ∘' g)) (DCC? Π(f_α', f_β'))
  | tm₁  : (¬ ∃ f_α f_β env, e = (DCC? (Π(f_α, f_β) env)))
    → (¬ ∃ f_α f_β, e = (DCC? (Π(f_α, f_β))))
    → (¬ ∃ g f_α f_β, e = (DCC? (Π(f_α, f_β)) ∘' g))
    → (¬ ∃ β, e = (DCC? Coup(β)))
    → (¬ ∃ β, e = (DCC? !(β)))
    → RedEta? e e' → RedEta?? e e'
  | tm₂  : (¬ ∃ f_α f_β env, e = (DCC? (Π(f_α, f_β) env)))
    → (¬ ∃ f_α f_β, e = (DCC? (Π(f_α, f_β))))
    → (¬ ∃ g f_α f_β, e = (DCC? (Π(f_α, f_β)) ∘' g))
    → (¬ ∃ β, e = (DCC? Coup(β)))
    → (¬ ∃ β, e = (DCC? !(β)))
    → (¬ ∃ e', RedEta? e e')
    → Relation.ReflTransGen RedAff e e'
    → IsNorm RedAff e'
    → RedEta?? e e

/-def RedEta??.transport {A B : GenericExpr Unit} (hr : RedEta?? A B) : RedEta?? A.expr_to_eta B.expr_to_eta := by
  induction hr
  · simp [expr_to_eta]
    
    sorry-/

def to_eta_no_hole.{u} {τ : Type u} {e : GenericExpr τ} : ¬ (expr_to_eta e).contains_hole := by
  induction e <;> (simp_all [expr_to_eta, contains_hole])

def to_eta_left_inv.{u} {τ : Type u}
  {e : GenericExpr τ} : eta_to_expr (expr_to_eta e) to_eta_no_hole = e := by
  unfold expr_to_eta
  split
  any_goals (simp [eta_to_expr])
  any_goals (
    focus
    rename_i x
    have ha := x.to_eta_left_inv
    simp [ha]
    done)
  any_goals (
    focus
    rename_i x y
    have ha := x.to_eta_left_inv
    have hb := y.to_eta_left_inv
    simp [ha, hb]
    done)
  any_goals (
    focus
    rename_i x y z
    have ha := x.to_eta_left_inv
    have hb := y.to_eta_left_inv
    have hc := z.to_eta_left_inv
    simp [ha, hb, hc])

--def to_from_eta_eq_iff.{u} {τ : Type u} {e : GenericExpr τ} {e' : GenericExpr (@EtaConst τ)} : expr_to_eta e = e' ↔

def to_eta_right_inv.{u} {τ : Type u} {e : GenericExpr (@EtaConst τ)} (hn : ¬ e.contains_hole) :
  (expr_to_eta (eta_to_expr e hn)) = e := by
  induction e
  any_goals (simp_all [eta_to_expr, expr_to_eta])
  any_goals (
    focus
    aesop
    done)
  any_goals (grind)
  case const x =>
    unfold contains_hole at hn
    simp at hn
    cases x with
    | hole => simp_all
    | const => simp [eta_to_expr, expr_to_eta]

def red_eta??.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] (e : GenericExpr τ_c) : Option ((e' : GenericExpr τ_c) × (PLift (RedEta?? e e'))) :=
  if heq : ∃ f_α f_β env, e = (DCC? (Π(f_α, f_β) env)) then
    match e with
    | (DCC? (Π(f_α, f_β) env)) =>
      match f_α.expr_to_eta.domain? with
      | .some ⟨δ, ⟨h₂⟩⟩ =>
        have h_dec₁ : env.size < (DCC? (Π(f_α, f_β) env)).size := by
          grind
        have h_dec₂ : f_α.size < (DCC? (Π(f_α, f_β) env)).size := by
          grind
        have h_dec₂ : (DCC? (f_α env)).size < (DCC? (Π(f_α, f_β) env)).size := by
          grind
        have h_dec₃ : (reduce RedAff (DCC? (f_β env))).fst.size < (DCC? (Π(f_α, f_β) env)).size := by
          have h := (reduce RedAff (DCC? (f_β env))).snd.down
          have h_le : (reduce RedAff (DCC? (f_β env))).fst.size ≤ (DCC? (f_β env)).size :=
            red_aff_decreasing? h
          grind
        match env.red_eta??, f_α.red_eta??, (reduce RedAff (DCC? (f_β env))).fst.red_eta?? with
        | .some ⟨_, ⟨h₄⟩⟩, .some ⟨f_α', ⟨h₅⟩⟩, .some ⟨f_β', ⟨h₆⟩⟩ =>
          if h₃ : δ.contains_hole then
            .none
          else
            if heq : f_β' = (DCC? (f_β env)) then
              .some ⟨_, ⟨.pi₁' h₅ h₂ h₃ h₄ (reduce_sound rfl) (reduce_norm rfl) h₆ heq⟩⟩
            else
              .some ⟨_, ⟨.pi₁ h₅ h₂ h₃ h₄ (reduce_sound rfl) (reduce_norm rfl) h₆ heq⟩⟩
        | _, _, _ => .none
      | _ => .none
  else
    if heq₂ : ∃ f_α f_β, e = (DCC? Π(f_α, f_β)) then
      match e with
      | (DCC? Π(f_α, f_β)) =>
        have h_dec₁ : f_α.size < (DCC? Π(f_α, f_β)).size := by
          grind
        have h_dec₂ : f_β.size < (DCC? Π(f_α, f_β)).size := by
          grind
        match f_α.red_eta??, f_β.red_eta?? with
        | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.pi₂ h₁ h₂⟩⟩
        | _, _ => .none
    else
      if heq₂' : ¬ (∃ g f_α f_β, e = (DCC? Π(f_α, f_β) ∘' g)) then
        if heq₂'' : ∃ β, e = (DCC? Coup(β)) then
          match e with
          | (DCC? Coup(β)) =>
            have h_dec : β.size < (DCC? Coup(β)).size := by
              grind
            match β.red_eta?? with
            | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.coup h⟩⟩
            | _ => .none
          | _ => .none
        else
          if heq₂''' : ∃ α, e = (DCC? !(α)) then
            match e with
            | DCC? !(β) =>
              have h_dec : β.size < (DCC? !(β)).size := by
                grind
              match β.red_eta?? with
              | .some ⟨_, ⟨h⟩⟩ =>
                .some ⟨_, ⟨.bang h⟩⟩
              | _ => .none
          else if heq₃ : ∃ e', RedEta? e e' then
            match _heq₄ : e.red_eta? with
            | .some ⟨_, ⟨h⟩⟩ =>
              .some ⟨_, ⟨.tm₁ heq heq₂ heq₂' heq₂'' heq₂''' h⟩⟩
            | _ => .none
          else
            .some ⟨_, ⟨.tm₂ heq heq₂ heq₂' heq₂'' heq₂''' heq₃ (reduce_sound rfl) (reduce_norm rfl)⟩⟩
      else
        match e with
        | (DCC? (Π(f_α, f_β) ∘' g)) =>
          have h_dec₁ : (reduce RedAff f_α).fst.size ≤ f_α.size :=
            decreasing? _ (reduce RedAff f_α).snd.down
          have h_dec₂ : (reduce RedAff f_β).fst.size ≤ f_β.size :=
            decreasing? _ (reduce RedAff f_β).snd.down
          have h_dec₃ : (DCC? (#((reduce RedAff f_α).fst) ∘' g)).size < (DCC? Π(f_α, f_β) ∘' g).size := by
            grind
          have h_dec₄ : (DCC? (#((reduce RedAff f_β).fst) ∘' g)).size < (DCC? Π(f_α, f_β) ∘' g).size := by
            grind
          match (DCC? (#((reduce RedAff f_α).fst) ∘' g)).red_eta??, (DCC? (#((reduce RedAff f_β).fst) ∘' g)).red_eta?? with
          | .some ⟨f_α', ⟨h₁⟩⟩, .some ⟨f_β', ⟨h₂⟩⟩ =>
            .some ⟨_, ⟨.pi₃ (reduce_sound rfl) (reduce_norm rfl)
              h₁ (reduce_sound rfl) (reduce_norm rfl)  h₂⟩⟩
          | _, _ => .none
        | _ => .none
termination_by e.size

@[aesop safe forward (rule_sets := [DccReduce])]
theorem RedEta??.complete.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {e e' : GenericExpr (τ := τ_c)} (h : RedEta?? e e') : e.red_eta?? = .some ⟨e', ⟨h⟩⟩ := by
  induction h
  case pi₁ | pi₁' =>
    rename_i f_α δ δ' env env' f_β f_β_env f_β' h₁ to_eta_expr h_domain h_to_expr h₃ hrenv hnenv h₄ hneq heq₁ heq₂ heq₃
    have heq₄ := reduce_complete hrenv hnenv
    have heq₅ : (reduce RedAff (f_β_env.app env')).fst = f_β' := by
      simp_all
    unfold red_eta??
    simp
    simp [h_domain.complete, heq₁, heq₂]
    cases heq₅
    cases heq₄
    simp [heq₃]
    simp_all
  case pi₂ =>
    rename_i f_α f_α' f_β f_β' h₁ h₂ heq₁ heq₂
    unfold red_eta??
    simp
    simp [heq₁, heq₂]
  case tm₁ e₀ e'' hn'''' hn''' hn'' hn₁ hn₂ h =>
    have he : ∃ e', RedEta? e₀ e' := by
      exact ⟨_, h⟩
    have h₁ := h.complete
    unfold red_eta??
    simp [hn''', hn'''', hn'', hn₁, hn₂, he]
    rw [h₁]
  case tm₂ hn''' hn' hn'' hn₁ hn₂ hn₃ hr hnorm =>
    have h₁ := reduce_complete hr hnorm
    rw [red_eta??]
    simp [hn''', hn', hn'', hn₁, hn₂, hn₃]
  case pi₃ hrt₁ hn₁ hr₁ hrt₂ hn₂ hr₂ heq₁ heq₂ =>
    have heq₃ := reduce_complete hrt₁ hn₁
    have heq₄ := reduce_complete hrt₂ hn₂
    have heq₅ := reduce_complete_fst hrt₁ hn₁
    have heq₆ := reduce_complete_fst hrt₂ hn₂
    cases heq₅; cases heq₆
    unfold red_eta??
    simp_all
  case coup hr₁ heq₁ =>
    unfold red_eta??
    simp [heq₁]
  case bang hr₁ heq₁ =>
    unfold red_eta??
    simp [heq₁]

instance RedEta??.instDecidable.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {e : GenericExpr τ_c}: Decidable (∃ e', RedEta?? (τ_c := τ_c) e e') :=
  match heq : e.red_eta?? with
  | .some ⟨_, ⟨h⟩⟩ => .isTrue ⟨_, h⟩
  | .none =>
    .isFalse (fun ⟨_, h⟩ => by
      have h := h.complete
      simp_all)

inductive RedEta₂.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] : GenericExpr τ_c → GenericExpr τ_c → Prop
  | refl : (¬ ∃ e', RedEta?? e e') → RedEta₂ e e
  | step : RedEta?? e e' → RedEta₂ e e'

def red_eta.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] (e : GenericExpr τ_c) : ((e' : GenericExpr τ_c) × (PLift (RedEta₂ e e'))) :=
  match heq₂ : e.red_eta?? with
  | .some ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.step h⟩⟩
  | .none => ⟨_, ⟨.refl (fun ⟨_, h⟩ => by
    have h := h.complete
    simp_all)⟩⟩

theorem RedEta₂.complete.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {e e' : GenericExpr τ_c} (h : RedEta₂ e e') : e.red_eta = ⟨e', ⟨h⟩⟩ := by
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
theorem reduce_eta_sound.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {e e' : GenericExpr τ_c} {h : RedEta₂ e e'} (_heq : red_eta e = ⟨e', ⟨h⟩⟩) : RedEta₂ e e' := h

@[dcc_force_reduce]
abbrev red_eta'₂.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] (e : GenericExpr τ_c) : GenericExpr τ_c := e.red_eta.fst

#eval (DCC Id(Sort 1) ∘' Id(Sort 1)).red_eta.fst
#eval (DCC `(Sort 1, Sort 1)).red_eta.fst
#eval (DCC Id(Sort 1)).red_eta.fst
#eval (DCC Λ(Sort 1, Id(Sort 1), Id(Coup(Id(Sort 1))) ∘' Id(Coup(Id(Sort 1))))).red_eta.fst
#eval (DCC (Λ(Sort 1, Id(Sort 1), Sndc(Coup(Id(Sort 1)))) (Sort 0))).red_eta.fst
#eval (DCC Eql(Id(Sort 2))).red_eta.fst
#eval (DCC Eql(Id(Sort 2))).red_eta.fst
#eval (DCC ((Sort 0 : Sort 1) → Sort 2)).raw_repr
#eval (DCC (Λ(Sort 1, `(Sort 1, Sort 2), `(Coup(`(Sort 1, Sort 2)), (Sort 3))))).red_eta.fst
#eval (DCC (Π(Id(Sort 3) ∘' Id(Sort 3), `(Sort 3, Π(!<Id(Sort 2)>, Eql(Id(Sort 2))))) !(Sort 2))).red_eta.fst
#eval (DCC (Π(Id(Sort 3) ∘' Id(Sort 3), `(Sort 3, Π(!<Id(Sort 2)>, Eql(Id(Sort 2)))) ∘' Id(Sort 3)) !(Sort 2))).red_eta.fst

/-def RedEta₂.transport.{u} {τ : Type u} [BEq τ] [DecidableEq τ] {e e' : GenericExpr τ}
  (h : RedEta₂ e e') : RedEta₂ e.expr_to_eta e'.expr_to_eta := by
  induction heq : h
  
  sorry-/

end GenericExpr

open GenericExpr in
instance : GenericExpr τ ≃ { x : GenericExpr (@EtaConst τ) // ¬ contains_hole x} where
  toFun       := (⟨·.expr_to_eta, to_eta_no_hole⟩)
  invFun      := fun ⟨x, hn⟩ => eta_to_expr x hn
  left_inv  x := by simp [to_eta_left_inv]
  right_inv x := by simp [to_eta_right_inv]

namespace Expr

theorem norm_eta {e : Expr} (h : GenericExpr.IsNorm RedAff e) : GenericExpr.IsNorm GenericExpr.RedAff (e.expr_to_eta (τ_c := Unit)) := by
  
  sorry

theorem norm_eta {e : Expr} (h : GenericExpr.IsNorm RedAff e) : GenericExpr.IsNorm GenericExpr.RedAff (e.expr_to_eta (τ_c := Unit)) := by
  unfold GenericExpr.expr_to_eta
  split
  any_goals (
    intro ⟨_, h⟩
    cases h)
  case eql' x y x' hr =>
    have h := norm_eta (e := x) (fun ⟨_, hr⟩ => h ⟨_, .eql' hr⟩)
    exact h ⟨_, hr⟩
  case eqr' x y y' hr =>
    have h := norm_eta (e := y) (fun ⟨_, hr⟩ => h ⟨_, .eqr' hr⟩)
    exact h ⟨_, hr⟩
  case sigl x y z x' hr =>
    have h := norm_eta (e := y) (fun ⟨_, hr⟩ => h ⟨_, .sigl hr⟩)
    exact h ⟨_, hr⟩
  case sigr x y z x' hr =>
    have h := norm_eta (e := z) (fun ⟨_, hr⟩ => h ⟨_, .sigr hr⟩)
    exact h ⟨_, hr⟩
  case coup x β' hr =>
    have h := norm_eta (e := x) (fun ⟨_, hr⟩ => h ⟨_, .coup hr⟩)
    exact h ⟨_, hr⟩
  case pil x y f_α' hr =>
    have h := norm_eta (e := x) (fun ⟨_, hr⟩ => h ⟨_, .pil hr⟩)
    exact h ⟨_,  hr⟩
  case pir x y f_α' hr =>
    have h := norm_eta (e := y) (fun ⟨_, hr⟩ => h ⟨_, .pir hr⟩)
    exact h ⟨_,  hr⟩
  case pairl x y f_α' hr =>
    have h := norm_eta (e := x) (fun ⟨_, hr⟩ => h ⟨_, .pairl hr⟩)
    exact h ⟨_,  hr⟩
  case pairr x y f_α' hr =>
    have h := norm_eta (e := y) (fun ⟨_, hr⟩ => h ⟨_, .pairr hr⟩)
    exact h ⟨_,  hr⟩
  case bang x x' hr =>
    have h := norm_eta (e := x) (fun ⟨_, hr⟩ => h ⟨_, .bang hr⟩)
    exact h ⟨_,  hr⟩
  case h_29 x y =>
    have ha := norm_eta h.congrFun
    have hb := norm_eta h.congrArg
    simp
    induction x generalizing y
    any_goals (
      focus
      intro ⟨_, h⟩
      cases h
      · rename_i hr
        exact ha ⟨_, hr⟩
      · rename_i hr
        exact hb ⟨_, hr⟩
      done
    )
    · induction y
      any_goals (
        focus
        simp [GenericExpr.expr_to_eta]
        intro ⟨_, h⟩
        cases h with
        | congrFun h => cases h
        | congrArg h => cases h
        done)
      

end Expr
