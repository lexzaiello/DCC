import Dcc.CC.Ast
import Dcc.CC.Judge2

/-
Λ(?, ?, x ∘ Snd) = `(x)

f ∘ `(x) = `(f x)

`(?, `(
-/

namespace Expr

/-
Only count β in size of Pi so we can normalize greedily.
-/

/-
Need eta rules to handle potential apps produced by Π
-/

inductive RedEta : Expr → Expr → Prop
  /-
   pi rule might break things
  -/
  | pi       : Size env (m + 1)
    → RedAffTrans (DCC (f_α env)) α
    → IsNormAff α
    → RedEta (DCC (f_β env)) β
    → RedEta (DCC (Π(f_α, f_β) env)) (DCC (Π(`(⊤, α), `(⊤, β)) ∗))
  | idr      : RedEta (DCC (f ∘ Id(α))) f
  | fst      : RedEta (DCC (Fst(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨x, y⟩) x
  | snd      : RedEta (DCC (Snd(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨x, y⟩) y
  | snd'     : RedEta (DCC Λ(α, _b, x ∘ (Snd(_c) _env))) (DCC `(α, x))
  | beta     : RedEta
    (DCC ((App(_f_α, _f_β, _f_γ) _env) ∘ ⟦m, α, _b, γ⟧⟨Λ(_α, _β, x), y⟩))
    (DCC (x ∘ ⟦m, α, Fstc(Id(Sort m)), γ⟧⟨Id(α), y⟩))
  | ai       : RedEta (DCC Λ(α, β, (App(f_α, f_β, f_γ) env))) (DCC Id((Π(f_α, f_β) env)))
  | fsi      : RedEta (DCC ⟦m, a, b, c⟧⟨(Fst(_β) env), (Snd(_β₂) env₂)⟩) (DCC Id((Σ(_β) env)))
  | uncur    : RedEta (DCC Λ(α, β,
    (App(_f_α, _f_β, _f_γ) _env) ∘ ⟦_m, _a, _b, _c⟧⟨f ∘ (Fst(_x) _env₁), (Snd(_x₂) _env₂)⟩)) f

@[aesop safe apply, grind ., grind →, simp] theorem RedEta.decreasing (h : RedEta e e') : (size e').fst < (size e).fst := by
  induction h <;> (try grind)

def sn_eta (e : Expr) : Acc (fun b a => RedEta a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing
  exact e'.sn_eta)
termination_by e.size.fst

def RedEtaTrans     := Relation.TransGen RedEta
def RedEtaReflTrans := Relation.ReflTransGen RedEta

@[aesop safe apply, grind ., grind →, simp] theorem RedEtaTrans.decreasing : RedEtaTrans e e' → (size e').fst < (size e).fst := by
  intro h
  induction h with
  | single h => exact h.decreasing
  | tail h₁ hr ih =>
    have h := hr.decreasing
    grind

theorem sn_eta_trans (e : Expr) : Acc (fun b a => RedEtaTrans a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing
  exact e'.sn_eta_trans)
termination_by e.size.fst

/-
η-reduction is deterministic
-/
theorem RedEta.unique (h₁ : RedEta A B) (h₂ : RedEta A C) : B = C := by
  induction h₁ generalizing C with
  | pi _ h_r₁ h_norm₁ _ ih =>
    cases h₂ with
    | pi _ hr₂ h_norm₂ =>
      have ha := h_r₁.norm_unique h_norm₁ hr₂ h_norm₂
      have hb := ih (by assumption)
      simp_all
  | uncur | ai | fsi | beta | snd' | snd | fst | idr => cases h₂; rfl

instance instWellFoundedEta      : WellFounded (fun a b => RedEta b a) := ⟨sn_eta⟩
instance instWellFoundedEtaTrans : WellFounded (fun a b => RedEtaTrans b a) := ⟨sn_eta_trans⟩

theorem RedEtaReflTrans.conf (h₁ : RedEtaReflTrans A B) (h₂ : RedEtaReflTrans A C) :
  ∃ D, RedEtaReflTrans B D ∧ RedEtaReflTrans C D := by
  induction A using instWellFoundedEta.induction generalizing B C with
  | h _ ih =>
    match h₁.cases_head, h₂.cases_head with
    | .inr ⟨_, hra, hrc⟩, .inr ⟨_, hra', hrc'⟩ =>
      have heq := hra.unique hra'
      exact ih _ hra hrc (heq ▸ hrc')
    | .inl heq₁, .inl heq₂ => exact ⟨B, .refl, heq₂.symm ▸ h₁⟩
    | .inl heq₁, .inr _ => exact ⟨C, heq₁.symm ▸ h₂, .refl⟩
    | .inr _, .inl heq₁ => exact ⟨B, .refl, heq₁.symm ▸ h₁⟩

@[simp] def step_η? (e : Expr) : Option ((e' : Expr) × (PLift (RedEta e e'))) :=
  match e with
  | DCC (Π(f_α, f_β) env) =>
    match env.size with
    | ⟨m + 1, ⟨h_size⟩⟩ =>
      match heq₀ : step_star? (DCC (f_α env)) with
      | .some α =>
        match (DCC (f_β env)).step_η? with
        | .some ⟨β, ⟨h⟩⟩ =>
          .some ⟨_, ⟨.pi h_size (step_star?_sound heq₀) (step_star?_norm heq₀) h⟩⟩
        | _ => .none
      | _ => .none
    | _ => .none
  | (DCC (f ∘ Id(α))) => .some ⟨_, ⟨.idr⟩⟩
  | (DCC (Fst(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨x, y⟩) => .some ⟨_, ⟨.fst⟩⟩
  | (DCC (Snd(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨x, y⟩) => .some ⟨_, ⟨.snd⟩⟩
  | (DCC Λ(α, _b, x ∘ (Snd(_c) _env))) => .some ⟨_, ⟨.snd'⟩⟩
  | (DCC ((App(_f_α, _f_β, _f_γ) _env) ∘ ⟦m, α, _b, γ⟧⟨Λ(_α, _β, x), y⟩)) => .some ⟨_, ⟨.beta⟩⟩
  | (DCC Λ(α, β, (App(f_α, f_β, f_γ) env))) => .some ⟨_, ⟨.ai⟩⟩
  | (DCC ⟦m, a, b, c⟧⟨(Fst(_β) env), (Snd(_β₂) env₂)⟩) => .some ⟨_, ⟨.fsi⟩⟩
  | (DCC Λ(α, β,
    (App(_f_α, _f_β, _f_γ) _env) ∘ ⟦_m, _a, _b, _c⟧⟨f ∘ (Fst(_x) _env₁), (Snd(_x₂) _env₂)⟩)) =>
      .some ⟨_, ⟨.uncur⟩⟩
  | _ => .none
termination_by sizeOf e

def reduce_η (e : Expr) : Expr :=
  match step_η? e with
  | .some ⟨e', ⟨h⟩⟩ =>
    -- This hypothesis allows the recursion. Easy to prove.
    have _h_size : e'.size.fst < e.size.fst := h.decreasing
    e'.reduce_η
  | .none => e
termination_by e.size.fst

theorem reduce_η_sound (heq : reduce_η A = B) : RedEtaReflTrans A B := by
  induction A using instWellFoundedEta.induction generalizing B with
  | h a ih =>
    unfold reduce_η at heq
    split at heq
    case h_1 h_red h_step_eq =>
      exact Relation.ReflTransGen.trans (.single h_red) (ih _ h_red heq)
    case h_2 => simp_all only [forall_eq']; exact .refl

theorem RedEta.complete' (h_red : RedEta A B) : step_η? A = .some ⟨B, ⟨h⟩⟩ := by
  induction h_red with
  | pi h_size hrt h_norm h ih =>
    have h := hrt.complete h_norm
    aesop
  | _ => simp

end Expr
