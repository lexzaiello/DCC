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

inductive RedAffEta : Expr → Expr → Prop
  /-
   pi rule might break things
  -/
  | pi       : Size env (m + 1)
    → RedAffTrans (DCC (f_α env)) α
    → IsNormAff α
    → RedAffEta (DCC (f_β env)) β
    → RedAffEta (DCC (Π(f_α, f_β) env)) (DCC (Π(`(⊤, α), `(⊤, β)) ∗))
  | idr      : RedAffEta (DCC (f ∘ Id(α))) f
  | fst      : RedAffEta (DCC (Fst(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨x, y⟩) x
  | snd      : RedAffEta (DCC (Snd(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨x, y⟩) y
  | snd'     : RedAffEta (DCC Λ(α, _b, x ∘ (Snd(_c) _env))) (DCC `(α, x))
  | beta     : RedAffEta
    (DCC ((App(_f_α, _f_β, _f_γ) _env) ∘ ⟦m, α, _b, γ⟧⟨Λ(_α, _β, x), y⟩))
    (DCC (x ∘ ⟦m, α, Fstc(Id(Sort m)), γ⟧⟨Id(α), y⟩))
  | ai       : RedAffEta (DCC Λ(α, β, (App(f_α, f_β, f_γ) env))) (DCC Id((Π(f_α, f_β) env)))
  | fsi      : RedAffEta (DCC ⟦m, a, b, c⟧⟨(Fst(_β) env), (Snd(_β) env)⟩) (DCC Id((Σ(_β) env)))
  | uncur    : RedAffEta (DCC Λ(α, β,
    (App(_f_α, _f_β, _f_γ) _env) ∘ ⟦_m, _a, _b, _c⟧⟨f ∘ (Fst(_x) _env₁), (Snd(_x₂) _env₁)⟩)) f

@[aesop safe apply, grind ., grind →, simp] theorem RedAffEta.decreasing (h : RedAffEta e e') : (size e').fst < (size e).fst := by
  induction h <;> (try grind)

def sn_eta (e : Expr) : Acc (fun b a => RedAffEta a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing
  exact e'.sn_eta)
termination_by e.size.fst

def RedEtaTrans     := Relation.TransGen RedAffEta
def RedEtaReflTrans := Relation.ReflTransGen RedAffEta

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
theorem RedAffEta.unique (h₁ : RedAffEta A B) (h₂ : RedAffEta A C) : B = C := by
  induction h₁ generalizing C with
  | pi _ h_r₁ h_norm₁ _ ih =>
    cases h₂ with
    | pi _ hr₂ h_norm₂ =>
      have ha := h_r₁.norm_unique h_norm₁ hr₂ h_norm₂
      have hb := ih (by assumption)
      simp_all
  | uncur | ai | fsi | beta | snd' | snd | fst | idr => cases h₂; rfl

instance instWellFoundedEta      : WellFounded (fun a b => RedAffEta b a) := ⟨sn_eta⟩
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

end Expr
