import Dcc.Relation
import Dcc.Ast
import Dcc.Types
import Dcc.Eta.Size
import Dcc.Aff.Red
import Dcc.Aff.Size

/-
(Subst(`(⊤, Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
         Fst(`(⊤, Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))))
     ∗) ∘
  Fstc(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))), Sort 0))
-/

/-
Σ-normalization to Coup:

Σ(f_β) env

f_β env →_η f_β'

Coup(f_β')
-/

namespace Expr

/-
TODO: need to reduce (x y) in curr_fst.
Very dumb in the first place.
Will need to mess around with size a bit for this to work.
-/

inductive RedEta : Expr → Expr → Prop
  | curr      : RedEta x x' → RedEta (DCC (Λ(α, β, x))) (DCC (Λ(α, β, x')))
  | curr_quot : RedEta (DCC (Λ(α, Id(α), `(Coup(Id(α)), x)) y)) (DCC `(y, x))
  | curr_fst  : Relation.ReflTransGen RedAff (DCC (β y)) β'
    → IsNorm RedAff β'
    → Relation.ReflTransGen RedAff (DCC (x y)) (DCC xy)
    → IsNorm RedAff (DCC xy)
    → RedEta (DCC (Λ(α, β, x ∘ Fstc(β₂)) y)) (DCC `(β', xy))
  | curr_fst' : Relation.ReflTransGen RedAff (DCC (β y)) β'
    → IsNorm RedAff β'
    → Relation.ReflTransGen RedAff (DCC (x y)) (DCC xy)
    → IsNorm RedAff (DCC xy)
    → RedEta (DCC (Λ(α, β, x ∘' Fstc(β₂)) y)) (DCC `(β', xy))
  | pi         : RedEta (DCC Π(α, β)) p' → RedEta (DCC (Π(α, β) env)) (DCC (p' env))
  | pi_quot    : RedEta x x' → RedEta (DCC (Π(α, `(β, x)))) (DCC (Π(α, `(β, x'))))
  | pi'        : RedEta β β' → RedEta (DCC (Π(α, β))) (DCC (Π(α, β')))
  | sig        : RedEta (DCC (β env)) β' → RedEta (DCC (Σ(β) env)) (DCC Coup(β'))
  | sig'       : RedEta β β' → RedEta (DCC (Σ(β))) (DCC Σ(β'))
  | idl        : RedEta (DCC (Id(α) ∘ f)) f
  | idl'       : RedEta (DCC (Id(α) ∘' f)) f
  | fsi        : RedEta (DCC ⟨(Fst(_β) env), (Snd(_β₂) env₂)⟩) (DCC Id((Σ(_β) env)))
  | subst_fst  : RedEta (DCC (Subst(`(⊤, x), Fst(`(⊤, f_β))) ∗)) (DCC (x ∘' Fstc(f_β)))
  | quot_fst   : RedEta (DCC `(α, x) ∘ Fstc(β)) (DCC `(Coup(β), x))
  | quot'_fst  : RedEta (DCC `(α, x) ∘' Fstc(β)) (DCC `(Coup(β), x))
  | quot_snd   : RedEta (DCC `(α, x) ∘ Sndc(β)) (DCC `(Coup(β), x))
  | quot'_snd  : RedEta (DCC `(α, x) ∘' Sndc(β)) (DCC `(Coup(β), x))
  | quot_fst'  : RedEta (DCC (`(α, x) ∘ Fstc(β)) ∘ z) (DCC `(Coup(β), x) ∘ z)
  | quot'_fst' : RedEta (DCC (`(α, x) ∘' Fstc(β)) ∘' z) (DCC `(Coup(β), x) ∘' z)
  | quot_snd'  : RedEta (DCC (`(α, x) ∘ Sndc(β)) ∘ z) (DCC `(Coup(β), x) ∘ z)
  | quot'_snd' : RedEta (DCC (`(α, x) ∘' Sndc(β)) ∘' z) (DCC `(Coup(β), x) ∘' z)
  | pi_comp    : RedEta (DCC (Π(f_α, f_β) ∘ x)) (DCC (Π(f_α ∘ x, f_β ∘ x)))
  | pi'_comp   : RedEta (DCC (Π(f_α, f_β) ∘' x)) (DCC (Π(f_α ∘' x, f_β ∘' x)))
  /-| quot_comp : RedEta (DCC (`(α, x) ∘ y)) x'
    → RedEta (DCC (`(α, x) ∘ (y ∘ z))) (DCC (x' ∘ z))-/

@[dcc_step, aesop norm (rule_sets := [DccStep])] def step_eta? (e : Expr) : Option ((e' : Expr) × (PULift.{1, 0} (RedEta e e'))) :=
  match e with
  | DCC (Λ(α, _b, `(_c, x)) y) =>
    if heq : DCC (Λ(α, _b, `(_c, x)) y) = (DCC (Λ(α, Id(α), `(Coup(Id(α)), x)) y)) then
      heq ▸ .some ⟨_, ⟨.curr_quot⟩⟩
    else .none
  | DCC (Λ(_α, β, x ∘ Fstc(_β₂)) y) =>
    .some ⟨_, ⟨.curr_fst
    (reduce_sound rfl)
    (reduce_norm rfl)
    (reduce_sound rfl)
    (reduce_norm rfl)⟩⟩
  | DCC (Λ(_α, β, x ∘' Fstc(_β₂)) y) =>
    .some ⟨_, ⟨.curr_fst'
    (reduce_sound rfl)
    (reduce_norm rfl)
    (reduce_sound rfl)
    (reduce_norm rfl)⟩⟩
  | DCC Σ(f_β) =>
    match f_β.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.sig' h⟩⟩
    | _ => .none
  | DCC (Σ(f_β) env) =>
    match (DCC (f_β env)).step_eta? with
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
  | (DCC (Id(_α) ∘' _f)) => .some ⟨_, ⟨.idl'⟩⟩
  | DCC Λ(_α, _β, x) =>
    match x.step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.curr h⟩⟩
    | .none => .none
  | (DCC ⟨(Fst(_β) _env), (Snd(_β₂) _env₂)⟩) => .some ⟨_, ⟨.fsi⟩⟩
  | DCC (Subst(`(⊤, x), Fst(`(⊤, f_β))) ∗) => .some ⟨_, ⟨.subst_fst⟩⟩
  | (DCC `(α, x) ∘ Fstc(β)) => .some ⟨_, ⟨.quot_fst⟩⟩
  | (DCC `(α, x) ∘' Fstc(β)) => .some ⟨_, ⟨.quot'_fst⟩⟩
  | (DCC `(α, x) ∘ Sndc(β)) => .some ⟨_, ⟨.quot_snd⟩⟩
  | (DCC `(α, x) ∘' Sndc(β)) => .some ⟨_, ⟨.quot'_snd⟩⟩
  | DCC (Π(f_α, f_β) ∘ x) => .some ⟨_, ⟨.pi_comp⟩⟩
  | DCC (Π(f_α, f_β) ∘' x) => .some ⟨_, ⟨.pi'_comp⟩⟩
  | (DCC (`(α, x) ∘ Fstc(β)) ∘ z) => .some ⟨_, ⟨.quot_fst'⟩⟩
  | (DCC (`(α, x) ∘' Fstc(β)) ∘' z) => .some ⟨_, ⟨.quot'_fst'⟩⟩
  | (DCC (`(α, x) ∘ Sndc(β)) ∘ z) => .some ⟨_, ⟨.quot_snd'⟩⟩
  | (DCC (`(α, x) ∘' Sndc(β)) ∘' z) => .some ⟨_, ⟨.quot'_snd'⟩⟩
  /-| (DCC (`(α, x) ∘ (y ∘ z))) =>
    match (DCC `(α, x) ∘ y).step_eta? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.quot_comp h⟩⟩
    | .none => .none-/
  | _ => .none

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance RedEta.instRedRel : RedRel RedEta Size where
  run := step_eta?

theorem red_eta_sn : ∀ (e : Expr), Acc (fun b a => RedEta a b) e := RedEta.instRedRel.sn

theorem red_eta_trans_sn : ∀ (e : Expr), Acc (fun b a => Relation.TransGen RedEta a b) e := RedEta.instRedRel.to_trans.sn

@[simp] theorem RedEta.unique (h₁ : RedEta A B) (h₂ : RedEta A C) : B = C := by
  induction h₁ generalizing C with
  | pi'_comp | quot'_snd' | quot'_fst' | quot'_fst | quot'_snd | quot_snd' | quot_fst' | pi_comp | quot_snd | quot_fst | subst_fst | sig' | pi | sig => cases h₂; aesop
  | curr_fst hr₁ hn₁ hr₁a hn₁a =>
    cases h₂ with
    | curr_fst hr₂ hn₂ hr₂a hn₂a =>
      simp_all [norm_unique hr₁ hn₁ hr₂ hn₂, norm_unique hr₁a hn₁a hr₂a hn₂a]
  | curr_fst' hr₁ hn₁ hr₁a hn₁a =>
    cases h₂ with
    | curr_fst' hr₂ hn₂ hr₂a hn₂a =>
      simp_all [norm_unique hr₁ hn₁ hr₂ hn₂, norm_unique hr₁a hn₁a hr₂a hn₂a]
  /-| quot_comp ih =>
    cases h₂
    aesop-/
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
  | idl' | curr_quot | idl | fsi => cases h₂; rfl

open Congruent in theorem RedEta.conf (h₁ : RedEta A B) (h₂ : RedEta A C) : ∃ D, RedEta.instRedRel.ReflTrans B D ∧ RedEta.instRedRel.ReflTrans C D := by
  have h := h₁.unique h₂
  exact ⟨B, h ▸ .refl, h ▸ .refl⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedEta.instConf : Confluent RedEta := ⟨RedEta.conf⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instConfRedEtaTrans : Confluent RedEta (m := Relation.ReflTransGen) := RedEta.instRedRel.globally_confluent

theorem RedEta.complete (h_red : RedEta A B) : step_eta? A = .some ⟨B, ⟨h_red⟩⟩ := by
  induction h_red
  any_goals (focus
    unfold step_eta?
    aesop (rule_sets := [DccStep, DccReduce, DccSize, DccRel])
    done)
  case curr_fst' hr₁ hn₁ hr₂ hn₂ | curr_fst hr₁ hn₁ hr₂ hn₂ =>
    unfold step_eta?
    have ha := reduce_complete_fst hr₁ hn₁
    have hb := reduce_complete_fst hr₂ hn₂
    aesop (rule_sets := [DccStep, DccReduce, DccSize, DccRel])

def eta_semi_complete {A B : Expr} (h_red : A.RedEta B) : ∃ B', ∃ (h : A.RedEta B'), (step_eta? A) = .some ⟨B', ⟨h⟩⟩ :=
  ⟨_, _, h_red.complete⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedEta.instSemicomplete : SemiComplete RedEta := ⟨eta_semi_complete⟩

theorem eta_complete (h : Relation.ReflTransGen RedEta A B)
  (hn : IsNorm RedEta B) : reduce RedEta A = ⟨B, ⟨h⟩⟩ :=
  RedEta.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instCompleteEta : Complete (Relation.ReflTransGen RedEta) (P := IsNorm RedEta) := RedEta.instRedRel.instComplete

end Expr
