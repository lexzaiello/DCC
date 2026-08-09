import Dcc.Relation
import Dcc.Ast
import Dcc.Types
import Dcc.Aff.Red
import Dcc.Eta.Size
import Dcc.Aff.Size
import Mathlib.Tactic

namespace GenericExpr

/-
(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))) ∘'
   Fst(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))))

pi_comp may be safe.
-/

/-
η-reduction with NbE:

Note: all combinators have type-points, so we can index them by types.

we can use our type normal forms for this.
-/

inductive RedEta.{u} {τ : Type u} : GenericExpr τ → GenericExpr τ → Prop
  --| curr       : RedEta x x' → RedEta (DCC? (Λ(α, β, x))) (DCC? (Λ(α, β, x')))
  | comp_fstc    : RedEta (DCC? Λ(α, β, x)) f' → RedEta
    (DCC? (Λ(α, β, x) ∘' Fst(b))) (DCC? f' ∘' Fst(b))
  | curr_quot_c  : RedEta (DCC? Λ(α, `(α, β), `(Coup(`(α, β)), x))) (DCC? `(α, `(β, x)))
  | curr_quot'   : RedEta (DCC? (Λ(α, Id(α), `(Coup(Id(α)), x) ∘' Id(_a)) y)) (DCC? `(y, x))
  | curr_quot    : RedEta (DCC? (Λ(α, Id(α), `(Coup(Id(α)), x)) y)) (DCC? `(y, x))
  | curr_fst     : RedEta (DCC? (Λ(α, β, x ∘ Fst(Coup(β))) y)) (DCC? `((β y), (x y)))
  | curr_fst'    : RedEta (DCC? (Λ(α, β, x ∘' Fst(Coup(β))) y)) (DCC? `((β y), (x y)))
  | pi           : Relation.ReflTransGen RedAff env env'
    → IsNorm RedAff env'
    → RedEta (DCC? Π(α, β)) p' → RedEta (DCC? (Π(α, β) env)) (DCC? (p' env))
  --| pi_quot    : RedEta x x' → RedEta (DCC? (Π(α, `(β, x)))) (DCC? (Π(α, `(β, x'))))
  --| quot       : RedEta x x' → RedEta (DCC? `(β, x)) (DCC? `(β, x'))
  | pi'          : RedEta β β' → RedEta (DCC? (Π(α, β))) (DCC? (Π(α, β')))
--  | sig        : RedEta (DCC? (β env)) β' → RedEta (DCC? (Σ(α, β) env)) (DCC? Coup(β'))
  | sig'          : RedEta β β' → RedEta (DCC? (Σ(α, β))) (DCC? Σ(α, β'))
  | coup          : RedEta β β' → RedEta (DCC? (Coup(β))) (DCC? (Coup(β')))
  | quot_unbox    : RedEta (DCC? `(α, x) ∘' *(α₂)) (DCC? `(!(α), x))
  | quot_unbox'   : RedEta (DCC? `(α, x) ∘ *(α₂)) (DCC? `(!(α), x))
  --| quot'_unbox   : RedEta (DCC? (`(α, x) ∘' *(α₂)) ∘' z) (DCC? `(!(α), x) ∘' z)
  --| quot'_unbox'  : RedEta (DCC? (`(α, x) ∘ *(α₂)) ∘ z) (DCC? `(!(α), x) ∘ z)
  --| quot'_unbox₂  : RedEta (DCC? `(α, x) ∘' *(α₂) ∘' z) (DCC? `(!(α), x) ∘' z)
  --| quot'_unbox'₂ : RedEta (DCC? `(α, x) ∘ *(α₂) ∘ z) (DCC? `(!(α), x) ∘ z)
  | quot_fst      : RedEta (DCC? `(α, x) ∘ Fst(β)) (DCC? `(Coup(β), x))
  | quot'_fst     : RedEta (DCC? `(α, x) ∘' Fst(β)) (DCC? `(Coup(β), x))
  | quot_snd      : RedEta (DCC? `(α, x) ∘ Snd(β)) (DCC? `(Coup(β), x))
  | quot'_snd     : RedEta (DCC? `(α, x) ∘' Snd(β)) (DCC? `(Coup(β), x))
  --| quot_fst'     : RedEta (DCC? (`(α, x) ∘ Fst(β)) ∘ z) (DCC? `(Coup(β), x) ∘ z)
  --| quot'_fst'    : RedEta (DCC? (`(α, x) ∘' Fst(β)) ∘' z) (DCC? `(Coup(β), x) ∘' z)
  --| quot_snd'     : RedEta (DCC? (`(α, x) ∘ Snd(β)) ∘ z) (DCC? `(Coup(β), x) ∘ z)
  --| quot'_snd'    : RedEta (DCC? (`(α, x) ∘' Snd(β)) ∘' z) (DCC? `(Coup(β), x) ∘' z)
  --| quot_fst'₂     : RedEta (DCC? `(α, x) ∘ Fst(β) ∘ z) (DCC? `(Coup(β), x) ∘ z)
  --| quot'_fst'₂    : RedEta (DCC? `(α, x) ∘' Fst(β) ∘' z) (DCC? `(Coup(β), x) ∘' z)
  --| quot_snd'₂     : RedEta (DCC? `(α, x) ∘ Snd(β) ∘ z) (DCC? `(Coup(β), x) ∘ z)
  --| quot'_snd'₂    : RedEta (DCC? `(α, x) ∘' Snd(β) ∘' z) (DCC? `(Coup(β), x) ∘' z)
  --| pi_comp    : RedEta (DCC? (Π(f_α, f_β) ∘ x)) (DCC? (Π(f_α ∘ x, f_β ∘ x))) TURBO SUS DELETED
  --| pi'_comp   : RedEta (DCC? (Π(f_α, f_β) ∘' x)) (DCC? (Π(f_α ∘' x, f_β ∘' x)))
  | compl      : RedEta (DCC? (a ∘ b)) a' → RedEta (DCC? ((a ∘ b) ∘ c)) (DCC? (a' ∘ c))
  | compl'     : RedEta (DCC? (a ∘' b)) a' → RedEta (DCC? ((a ∘' b) ∘' c)) (DCC? (a' ∘' c))
  /-| pair_snd   : Relation.ReflTransGen RedAff N N' → IsNorm RedAff N'
    → RedEta (DCC? (Eval(_a, _b, Snd(_c)) ∘ ⟦_d⟧⟨Id(_e), Λ(_f, _g, N ∘' Fst(_h))⟩)) N'
  | pair_snd'  : Relation.ReflTransGen RedAff N N' → IsNorm RedAff N'
    → RedEta (DCC? (Eval(_a, _b, f ∘' Snd(_c)) ∘ ⟦_d⟧⟨Id(_e), Λ(_f, _g, N ∘' Fst(_h))⟩)) (DCC? (f ∘' N'))
  | pair_fst   : Relation.ReflTransGen RedAff M M'
    → IsNorm RedAff M' → RedEta (DCC? (Eval(_a, _b, Fst(_c)) ∘ ⟦_d⟧⟨M, N⟩)) M'
  | pair_fst'  : Relation.ReflTransGen RedAff M M'
    → IsNorm RedAff M' → RedEta (DCC? (Eval(_a, _b, f ∘' Fst(_c)) ∘ ⟦_d⟧⟨M, N⟩)) (DCC? (f ∘' M'))-/
  | quot       : RedEta x x' → RedEta (DCC? `(β, x)) (DCC? `(β, x'))
  /-| quot_comp : RedEta (DCC? (`(α, x) ∘ y)) x'
    → RedEta (DCC (`(α, x) ∘ (y ∘ z))) (DCC (x' ∘ z))-/

theorem RedEta.norm_aff (hn : IsNorm RedAff A) (h : RedEta A B) : IsNorm RedAff B := by
  induction h
  any_goals (
    focus
    intro ⟨_, h⟩
    cases h
    done
  )
  /-case pair_fst hrt hnm =>
    intro ⟨_, h⟩
    exact hnm ⟨_, h⟩
  case pair_snd hrt hnm =>
    intro ⟨_, h⟩
    exact hnm ⟨_, h⟩-/
  /-case pi_comp | pi'_comp =>
    intro ⟨_, h⟩
    cases h with
    | pil h => cases h
    | pir h => cases h-/
  case pi' β β' α h ih =>
    have hnα : IsNorm RedAff α := by
      intro ⟨_, h⟩
      exact hn ⟨_, .pil h⟩
    have hnβ : IsNorm RedAff β := by
      intro ⟨_, h⟩
      exact hn ⟨_, .pir h⟩
    have h := ih hnβ
    intro ⟨_, hr⟩
    cases hr with
    | pil =>
      exact hnα ⟨_, by assumption⟩
    | pir => exact h ⟨_, by assumption⟩
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

@[dcc_force_eta, dcc_force_reduce, aesop norm (rule_sets := [DccStep])] def step_eta?.{u} {τ : Type u} [DecidableEq τ] (e : GenericExpr τ) :
  Option ((e' : GenericExpr τ) × (PULift.{1, 0} (RedEta e e'))) :=
  match e with
  | (DCC? Λ(α, β, x) ∘' Fst(b)) =>
    match (DCC? Λ(α, β, x)).step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp_fstc h⟩⟩
    | _ => .none
  | (DCC? `(α, x) ∘' *(α₂)) => .some ⟨_, ⟨.quot_unbox⟩⟩
  | (DCC? `(α, x) ∘ *(α₂)) => .some ⟨_, ⟨.quot_unbox'⟩⟩
  --| (DCC? (`(α, x) ∘' *(α₂)) ∘' z) => .some ⟨_, ⟨.quot'_unbox⟩⟩
  --| (DCC? (`(α, x) ∘ *(α₂)) ∘ z) => .some ⟨_, ⟨.quot'_unbox'⟩⟩
  --| (DCC? `(α, x) ∘' *(α₂) ∘' z) => .some ⟨_, ⟨.quot'_unbox₂⟩⟩
  --| (DCC? `(α, x) ∘ *(α₂) ∘ z) => .some ⟨_, ⟨.quot'_unbox'₂⟩⟩
  | (DCC? Λ(α, `(_a, β), `(Coup(`(_b, _c)), x))) =>
    if heq : (DCC? Λ(α, `(_a, β), `(Coup(`(_b, _c)), x))) = (DCC? Λ(α, `(α, β), `(Coup(`(α, β)), x))) then
      heq ▸ .some ⟨_, ⟨.curr_quot_c⟩⟩
    else .none
  | DCC? (Λ(α, _b, `(_c, x) ∘' Id(_a)) y) =>
    if heq : (DCC? (Λ(α, _b, `(_c, x) ∘' Id(_a)) y)) = (DCC? (Λ(α, Id(α), `(Coup(Id(α)), x) ∘' Id(_a)) y)) then
      heq ▸ .some ⟨_, ⟨.curr_quot'⟩⟩
    else .none
  | DCC? (Λ(α, _b, `(_c, x)) y) =>
    if heq : (DCC? (Λ(α, _b, `(_c, x)) y)) = (DCC? (Λ(α, Id(α), `(Coup(Id(α)), x)) y)) then
      heq ▸ .some ⟨_, ⟨.curr_quot⟩⟩
    else .none
  | DCC? (Λ(_α, β, x ∘ Fst(Coup(β₂))) y) =>
    if heq : β₂ = β then
      heq ▸ .some ⟨_, ⟨.curr_fst⟩⟩
    else .none
  | DCC? (Λ(_α, β, x ∘' Fst(Coup(β₂))) y) =>
    if heq : β₂ = β then
      heq ▸ .some ⟨_, ⟨.curr_fst'⟩⟩
    else .none
  | DCC? Σ(α, f_β) =>
    match f_β.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.sig' h⟩⟩
    | _ => .none
  | DCC? Coup(f_β) =>
    match f_β.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.coup h⟩⟩
    | _ => .none
  /-| DCC? (Σ(α, f_β) env) =>
    match (DCC? (f_β env)).step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.sig h⟩⟩
    | _ => .none-/
  | DCC? (Π(_f_α, f_β) _env) =>
    match (DCC? Π(_f_α, f_β)).step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi (reduce_sound rfl) (reduce_norm rfl) h⟩⟩
    | _ => .none
  /-| DCC? `(β, x) =>
    match x.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.quot h⟩⟩
    | _              => .none-/
  | DCC? (Π(_f_α, f_β)) =>
    match f_β with
    /-| DCC? `(_β, x) =>
      match x.step_eta? with
      | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi_quot h⟩⟩
      | _ => .none-/
    | x =>
      match x.step_eta? with
      | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi' h⟩⟩
      | _ => .none
  /-| DCC? Λ(_α, _β, x) =>
    match x.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.curr h⟩⟩
    | .none => .none-/
  | (DCC? `(α, x) ∘ Fst(β)) => .some ⟨_, ⟨.quot_fst⟩⟩
  | (DCC? `(α, x) ∘' Fst(β)) => .some ⟨_, ⟨.quot'_fst⟩⟩
  | (DCC? `(α, x) ∘ Snd(β)) => .some ⟨_, ⟨.quot_snd⟩⟩
  | (DCC? `(α, x) ∘' Snd(β)) => .some ⟨_, ⟨.quot'_snd⟩⟩
  /-| DCC? (Π(f_α, f_β) ∘ x) => .some ⟨_, ⟨.pi_comp⟩⟩
  | DCC? (Π(f_α, f_β) ∘' x) => .some ⟨_, ⟨.pi'_comp⟩⟩-/
  --| (DCC? (`(α, x) ∘ Fst(β)) ∘ z) => .some ⟨_, ⟨.quot_fst'⟩⟩
  --| (DCC? (`(α, x) ∘' Fst(β)) ∘' z) => .some ⟨_, ⟨.quot'_fst'⟩⟩
  --| (DCC? (`(α, x) ∘ Snd(β)) ∘ z) => .some ⟨_, ⟨.quot_snd'⟩⟩
  --| (DCC? (`(α, x) ∘' Snd(β)) ∘' z) => .some ⟨_, ⟨.quot'_snd'⟩⟩
  --| (DCC? `(α, x) ∘ Fst(β) ∘ z) => .some ⟨_, ⟨.quot_fst'₂⟩⟩
  --| (DCC? `(α, x) ∘' Fst(β) ∘' z) => .some ⟨_, ⟨.quot'_fst'₂⟩⟩
  --| (DCC? `(α, x) ∘ Snd(β) ∘ z) => .some ⟨_, ⟨.quot_snd'₂⟩⟩
  --| (DCC? `(α, x) ∘' Snd(β) ∘' z) => .some ⟨_, ⟨.quot'_snd'₂⟩⟩
  | DCC? (a ∘ b) ∘ c =>
    match (DCC? (a ∘ b)).step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.compl h⟩⟩
    | _ => none
  | DCC? (a ∘' b) ∘' c =>
    match (DCC? (a ∘' b)).step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.compl' h⟩⟩
    | _ => none
  /-| DCC? (Eval(_a, _b, Snd(_c)) ∘ ⟦_d⟧⟨Id(_e), Λ(_f, _g, N ∘' Fst(_h))⟩) =>
    .some ⟨_, ⟨.pair_snd (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | DCC? (Eval(_a, _b, f ∘' Snd(_c)) ∘ ⟦_d⟧⟨Id(_e), Λ(_f, _g, N ∘' Fst(_h))⟩) =>
    .some ⟨_, ⟨.pair_snd' (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? (Eval(_a, _b, Fst(_c)) ∘ ⟦_d⟧⟨M, N⟩)) =>
    .some ⟨_, ⟨.pair_fst (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? (Eval(_a, _b, f ∘' Fst(_c)) ∘ ⟦_d⟧⟨M, N⟩)) =>
    .some ⟨_, ⟨.pair_fst' (reduce_sound rfl) (reduce_norm rfl)⟩⟩-/
  | DCC? `(_β, x) =>
    match x.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.quot h⟩⟩
    | _ => .none
  | _ => .none

@[dcc_force_reduce, dcc_force_eta, aesop norm (rule_sets := [DccRel])]
instance RedEta.instRedRel.{u} {τ : Type u} [DecidableEq τ] : RedRel (RedEta (τ := τ)) eta_size where
  run := step_eta?

theorem red_eta_sn.{u} {τ : Type u} [DecidableEq τ] : ∀ (e : GenericExpr τ), Acc (fun b a => RedEta a b) e := RedEta.instRedRel.sn

theorem red_eta_trans_sn.{u} {τ : Type u} [DecidableEq τ] : ∀ (e : GenericExpr τ), Acc (fun b a => Relation.TransGen RedEta a b) e :=
  RedEta.instRedRel.to_trans.sn

@[dcc_reduce, aesop safe forward (rule_sets := [DccRel])] theorem RedEta.unique.{u} {τ : Type u}
  {A B C : GenericExpr τ}
  (h₁ : RedEta (τ := τ) A B) (h₂ : RedEta (τ := τ) A C) : B = C := by
  induction h₁ generalizing C with
  --| pi_comp | pi'_comp
  | quot_fst
  | curr_quot_c | quot | compl | compl' | quot_unbox | quot_unbox' | coup | curr_fst' | curr_fst | quot'_fst | quot'_snd | quot_snd | sig' | pi => cases h₂; aesop
  /-| pi_quot hr ih =>
    cases h₂
    · rename_i hr₂; aesop
    · rename_i hr₂; cases hr₂-/
  /-| quot =>
    cases h₂
    · aesop-/
  /-| pair_snd hr ih | pair_fst hr ih =>
    cases h₂
    exact norm_unique hr (by assumption) (by assumption) (by assumption)
  | pair_fst' hr ih | pair_snd' hr ih =>
    have hra := reduce_complete (by assumption) (by assumption)
    cases h₂
    have hrb := reduce_complete (by assumption) (by assumption)
    aesop-/
  | comp_fstc hr ih | pi' hr ih =>
    cases h₂
    · aesop
  /-| curr hr ih =>
    cases h₂ with
    | curr hr₂ => rw [ih hr₂]-/
  --| idl'
  --| idl
  | curr_quot' | curr_quot => cases h₂; rfl
  --| sig => sorry

open Congruent in theorem RedEta.conf.{u} {τ : Type u} [DecidableEq τ] {A B C : GenericExpr τ}
  (h₁ : RedEta A B) (h₂ : RedEta A C) : ∃ D, RedEta.instRedRel.ReflTrans B D ∧ RedEta.instRedRel.ReflTrans C D := by
  have h := h₁.unique h₂
  exact ⟨B, h ▸ .refl, h ▸ .refl⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance RedEta.instConf.{u} {τ : Type u} [DecidableEq τ] : Confluent (RedEta (τ := τ)) := ⟨RedEta.conf⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instConfRedEtaTrans.{u} {τ : Type u} [DecidableEq τ] : Confluent
  (RedEta (τ := τ)) (m := Relation.ReflTransGen) := RedEta.instRedRel.globally_confluent

theorem RedEta.complete.{u} {τ : Type u} [DecidableEq τ]
  {A B : GenericExpr τ} (h_red : RedEta (τ := τ) A B) : step_eta? A = .some ⟨B, ⟨h_red⟩⟩ := by
  induction h_red <;> (aesop (rule_sets := [DccStep, DccReduce, DccSize, DccRel]))

def eta_semi_complete.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ]
  (h_red : A.RedEta B) : ∃ B', ∃ (h : A.RedEta B'), (step_eta? A) = .some ⟨B', ⟨h⟩⟩ :=
  ⟨_, _, h_red.complete⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedEta.instSemicomplete.{u} {τ : Type u} [DecidableEq τ] : SemiComplete (RedEta (τ := τ)) := ⟨eta_semi_complete⟩

theorem eta_complete.{u} {τ : Type u} [DecidableEq τ] {A B : GenericExpr τ} (h : Relation.ReflTransGen RedEta A B)
  (hn : IsNorm RedEta B) : reduce (RedEta (τ := τ)) A = ⟨B, ⟨h⟩⟩ :=
  RedEta.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instCompleteEta.{u} {τ : Type u} [DecidableEq τ] : Complete
  (Relation.ReflTransGen (RedEta (τ := τ))) (P := IsNorm RedEta) := RedEta.instRedRel.instComplete

@[dcc_force_reduce, dcc_force_eta]
abbrev RedEta.reduce.{u} {τ : Type u} [DecidableEq τ] := GenericExpr.reduce (RedEta (τ := τ))

attribute [dcc_force_reduce, dcc_force_eta] RedEta.reduce.eq_def

instance instNormDec.{u} {τ : Type u} [DecidableEq τ] {A : GenericExpr τ} : Decidable (IsNorm (RedEta (τ := τ)) A) :=
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

#check RedEta.reduce

#eval Sigma.fst <| RedEta.reduce (DCC (Λ(Sort 1, Id(Sort 1), Snd(Coup(Id(Sort 1)))) (Sort 0)))

end GenericExpr

abbrev Expr.RedEta := GenericExpr.RedEta (τ := Unit)
