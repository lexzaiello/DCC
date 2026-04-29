import Dcc.Ast
import Dcc.Types
import Dcc.Eta.Size

namespace Expr

inductive RedEta : Expr → Expr → Prop
  | curr      : RedEta x x' → RedEta (DCC (Λ(α, β, x))) (DCC (Λ(α, β, x')))
  | curr_quot : RedEta (DCC (Λ(α, Id(α), `(Coup(Id(α)), x)) y)) (DCC `(y, x))
  | curr_fst  : RedEta (DCC (Λ(α, β, x ∘ Fstc(β₂)) y)) (DCC `(β, x))
  /-
   pi rule might break things
  -/
  | pi        : RedEta (DCC Π(α, β)) p' → RedEta (DCC (Π(α, β) env)) (DCC (p' env))
  | pi_quot   : RedEta x x' → RedEta (DCC (Π(α, `(β, x)))) (DCC (Π(α, `(β, x'))))
  | pi'       : RedEta β β' → RedEta (DCC (Π(α, β))) (DCC (Π(α, β')))
  | sig       : RedEta (DCC (Σ(β))) b' → RedEta (DCC (Σ(β) env)) (DCC (b' env))
  | sig'      : RedEta β β' → RedEta (DCC (Σ(β))) (DCC Σ(β'))
  | idl       : RedEta (DCC (Id(α) ∘ f)) f
  | fst       : RedEta (DCC (Fst(_β) _env) ∘ ⟨x, y⟩) x
  | snd       : RedEta (DCC (Snd(_β) _env) ∘ ⟨x, y⟩) y
  | beta      : RedEta
    (DCC ((App(_f_α, _f_β) _env) ∘ ⟨Λ(α, _β, x), y⟩))
    (DCC (x ∘ ⟨Id(α), y⟩))
  | ai        : RedEta (DCC Λ(α, β, (App(f_α, f_β) env))) (DCC Id((Π(f_α, f_β) env)))
  | fsi       : RedEta (DCC ⟨(Fst(_β) env), (Snd(_β₂) env₂)⟩) (DCC Id((Σ(_β) env)))
  | uncur     : RedEta (DCC Λ(α, β,
    (App(_f_α, _f_β) _env) ∘ ⟨f ∘ (Fst(_x) _env₁), (Snd(_x₂) _env₂)⟩)) f

@[dcc_step, aesop norm (rule_sets := [DccStep])] def step_eta? (e : Expr) : Option ((e' : Expr) × (PULift.{1, 0} (RedEta e e'))) :=
  match e with
  | DCC (Λ(α, _b, `(_c, x)) y) =>
    if heq : DCC (Λ(α, _b, `(_c, x)) y) = (DCC (Λ(α, Id(α), `(Coup(Id(α)), x)) y)) then
      heq ▸ .some ⟨_, ⟨.curr_quot⟩⟩
    else .none
  | DCC (Λ(_α, _β, _x ∘ Fstc(_β₂)) _y) => .some ⟨_, ⟨.curr_fst⟩⟩
  | DCC Σ(f_β) =>
    match f_β.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.sig' h⟩⟩
    | _ => .none
  | DCC (Σ(f_β) _env) =>
    match (DCC Σ(f_β)).step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.sig h⟩⟩
    | _ => .none
  | DCC (Π(_f_α, f_β) _env) =>
    match (DCC Π(_f_α, f_β)).step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi h⟩⟩
    | _ => .none
  | DCC (Π(_f_α, f_β)) =>
    match f_β with
    | DCC `(_β, x) =>
      match x.step_eta? with
      | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi_quot h⟩⟩
      | _ => .none
    | x =>
      match x.step_eta? with
      | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi' h⟩⟩
      | _ => .none
  | (DCC (Id(_α) ∘ _f)) => .some ⟨_, ⟨.idl⟩⟩
  | (DCC (Fst(_β) _env) ∘ ⟨_x, _y⟩) => .some ⟨_, ⟨.fst⟩⟩
  | (DCC (Snd(_β) _env) ∘ ⟨_x, _y⟩) => .some ⟨_, ⟨.snd⟩⟩
  | DCC Λ(α, β, x) =>
    match x.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.curr h⟩⟩
    | .none =>
      match DCC Λ(α, β, x) with
      | (DCC Λ(_α, _β, (App(_f_α, _f_β) _env))) => .some ⟨_, ⟨.ai⟩⟩
      | (DCC Λ(_α, _β,
        (App(_f_α, _f_β) _env) ∘ ⟨_f ∘ (Fst(_x) _env₁), (Snd(_x₂) _env₂)⟩)) =>
        .some ⟨_, ⟨.uncur⟩⟩
      | _ => .none
  | (DCC ((App(_f_α, _f_β) _env) ∘ ⟨Λ(__α, __β, _x), _y⟩)) => .some ⟨_, ⟨.beta⟩⟩
  | (DCC ⟨(Fst(_β) _env), (Snd(_β₂) _env₂)⟩) => .some ⟨_, ⟨.fsi⟩⟩
  | _ => .none

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedEta.instRedRel : RedRel RedEta EtaSize where
  run := step_eta?

@[simp] theorem RedEta.unique (h₁ : RedEta A B) (h₂ : RedEta A C) : B = C := by
  induction h₁ generalizing C with
  | sig' | pi | curr_fst | sig => cases h₂; aesop
  | pi_quot hr ih =>
    cases h₂
    · rename_i hr₂; aesop
    · rename_i hr₂; cases hr₂
  | pi' hr ih =>
    cases h₂
    · rename_i hr₂; cases hr
    · aesop
  | curr hr ih =>
    cases h₂ with
    | curr hr₂ => rw [ih hr₂]
    | ai | uncur => cases hr
  | ai | uncur =>
    cases h₂
    · rename_i h; cases h
    · rfl
  | curr_quot | snd | fst | idl | beta | fsi => cases h₂; rfl

open Congruent in theorem RedEta.conf (h₁ : RedEta A B) (h₂ : RedEta A C) : ∃ D, RedEta.instRedRel.ReflTrans B D ∧ RedEta.instRedRel.ReflTrans C D := by
  have h := h₁.unique h₂
  exact ⟨B, h ▸ .refl, h ▸ .refl⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedEta.instConf : Confluent RedEta := ⟨RedEta.conf⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instConfRedEtaTrans : Confluent RedEta (m := Relation.ReflTransGen) := RedEta.instRedRel.globally_confluent

theorem RedEta.complete (h_red : RedEta A B) : step_eta? A = .some ⟨B, ⟨h_red⟩⟩ := by
  induction h_red <;> (unfold step_eta?; aesop (rule_sets := [DccStep, DccReduce, DccSize, DccRel]))

def eta_semi_complete {A B : Expr} (h_red : A.RedEta B) : ∃ B', ∃ (h : A.RedEta B'), (step_eta? A) = .some ⟨B', ⟨h⟩⟩ :=
  ⟨_, _, h_red.complete⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedEta.instSemicomplete : SemiComplete RedEta := ⟨eta_semi_complete⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instCompleteEta : Complete (Relation.ReflTransGen RedEta) (P := IsNorm RedEta) := RedEta.instRedRel.instComplete

end Expr
