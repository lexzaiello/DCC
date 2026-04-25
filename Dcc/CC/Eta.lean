import Dcc.CC.Ast
import Dcc.CC.Step2

/-
App(f_α, f_β, f_γ) env = App(f_α env, f_β env, f_γ env)
-/

namespace Expr

/-
Only count β in size of Pi so we can normalize greedily.
-/

/-
Need eta rules to handle potential apps produced by Π

Λ(?, ?, Λ(α, β, `(?, y))) x → `(Coup(α, β, y))
-/

inductive RedEta : Expr → Expr → Prop
  | appl      : RedAffReflTrans (DCC (f_α env)) α
    → α.IsNormAff
    → RedEta (DCC (App(m, n, f_α, f_β) env)) (App'.type α f_α f_β env m)
  | quot_curr : RedEta (DCC Λ(α, β, `(_γ, x))) (DCC `(Coup(β), x))
  /-
   pi rule might break things
  -/
  | pi        : Size env (m + 1)
    → RedAffTrans (DCC (f_α env)) α
    → IsNormAff α
    → RedEta (DCC (f_β env)) β
    → RedEta (DCC (Π(f_α, f_β) env)) (DCC (Π(`(⊤, α), `(⊤, β)) ∗))
  | sig       : Size env (m + 1)
    → RedEta (DCC (f_β env)) β
    → RedEta (DCC (Σ(f_β) env)) (DCC (Σ(`(⊤, β)) ∗))
  | idr       : RedEta (DCC (f ∘ Id(α))) f
  | fst       : RedEta (DCC (Fst(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨x, y⟩) x
  | snd       : RedEta (DCC (Snd(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨x, y⟩) y
  | snd'      : RedEta (DCC Λ(α, _b, x ∘ (Snd(_c) _env))) (DCC `(α, x))
  | beta      : RedEta
    (DCC ((App'(_f_α, _f_β) _env) ∘ ⟦m, α, _b, γ⟧⟨Λ(_α, _β, x), y⟩))
    (DCC (x ∘ ⟦m, α, Fstc(Id(Sort m)), γ⟧⟨Id(α), y⟩))
  | ai        : RedEta (DCC Λ(α, β, (App'(f_α, f_β) env))) (DCC Id((Π(f_α, f_β) env)))
  | fsi       : RedEta (DCC ⟦m, a, b, c⟧⟨(Fst(_β) env), (Snd(_β₂) env₂)⟩) (DCC Id((Σ(_β) env)))
  | uncur     : RedEta (DCC Λ(α, β,
    (App'(_f_α, _f_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨f ∘ (Fst(_x) _env₁), (Snd(_x₂) _env₂)⟩)) f

@[aesop safe apply, grind ., grind →, simp] theorem RedEta.decreasing (h : RedEta e e') : (size e').fst < (size e).fst := by
  induction h <;> (simp_all; try grind)

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
  | sig _ h_red ih =>
    cases h₂ with
    | sig _ h_red₂ => simp [ih h_red₂] at *
  | appl h_r₁ h_norm₁ =>
    cases h₂ with
    | appl h_r₂ h_norm₂ =>
      have ha := h_r₁.norm_unique h_norm₁ h_r₂ h_norm₂
      simp_all
  | pi _ h_r₁ h_norm₁ _ ih =>
    cases h₂ with
    | pi _ hr₂ h_norm₂ =>
      have ha := h_r₁.norm_unique h_norm₁ hr₂ h_norm₂
      have hb := ih (by assumption)
      simp_all
  | quot_curr | uncur | ai | fsi | beta | snd' | snd | fst | idr => cases h₂; rfl

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
  | DCC (App(m, n, f_α, f_β) env) =>
    .some ⟨_, ⟨.appl (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | DCC Λ(α, β, `(_γ, x)) => .some ⟨_, ⟨.quot_curr⟩⟩
  | DCC (Σ(f_β) env) =>
    match env.size with
    | ⟨m + 1, ⟨h_size⟩⟩ =>
      match (DCC (f_β env)).step_η? with
      | .some ⟨β, ⟨h⟩⟩ =>
        .some ⟨_, ⟨.sig h_size h⟩⟩
      | _ => .none
    | _ => .none
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
  | (DCC ((App'(_f_α, _f_β) _env) ∘ ⟦m, α, _b, γ⟧⟨Λ(_α, _β, x), y⟩)) => .some ⟨_, ⟨.beta⟩⟩
  | (DCC Λ(α, β, (App'(f_α, f_β) env))) => .some ⟨_, ⟨.ai⟩⟩
  | (DCC ⟦m, a, b, c⟧⟨(Fst(_β) env), (Snd(_β₂) env₂)⟩) => .some ⟨_, ⟨.fsi⟩⟩
  | (DCC Λ(α, β,
    (App'(_f_α, _f_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨f ∘ (Fst(_x) _env₁), (Snd(_x₂) _env₂)⟩)) =>
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

theorem RedEta.complete (h_red : RedEta A B) : step_η? A = .some ⟨B, ⟨h_red⟩⟩ := by
  induction h_red with
  | appl hrt h_norm | pi h_size hrt h_norm h ih =>
    have h := hrt.complete h_norm
    aesop
  | _ => aesop

def IsNormEta (e : Expr) : Prop := ¬ ∃ e', RedEta e e'

def RedEtaTrans.next (h : RedEtaTrans A B) : ∃ h, RedEta A (A.step_η?.get h).fst := by
  induction h with
  | single h => exact ⟨_, (A.step_η?.get (by simp [h.complete])).snd.down⟩
  | tail _ _ ih => exact ih

def RedEtaReflTrans.next (h₁ : RedEtaReflTrans A B) (h₂ : RedEta B C) : ∃ h, RedEta A (A.step_η?.get h).fst := by
  change Relation.ReflTransGen _ _ _ at h₁
  rw [← Relation.reflGen_transGen] at h₁
  induction heq : h₁ with
  | refl => exact RedEtaTrans.next (.single h₂)
  | single h => exact RedEtaTrans.next h

theorem RedEta.norm_unique (h₁ : RedEta A B) (h_norm : IsNormEta B) (h_trans : RedEtaTrans A C) : B = C := by
  induction h_trans with
  | single h =>
    exact h₁.unique h
  | tail h ih heq => exact (h_norm ⟨_, heq ▸ ih⟩).elim


theorem RedEtaReflTrans.norm_same (h : RedEtaReflTrans A B) (h_norm : A.IsNormEta) : A = B := by
  induction h with
  | refl => rfl
  | tail hrt h_red heq =>
    rename_i b c
    exact (h_norm ⟨c, heq ▸ h_red⟩).elim

theorem RedEtaReflTrans.norm_unique (h₁ : RedEtaReflTrans A B) (h_norm₁ : IsNormEta B)
  (h₂ : RedEtaReflTrans A C) (h_norm₂ : IsNormEta C) : B = C := by
  induction A using instWellFoundedEta.induction generalizing B with
  | h _ ih =>
    match h₁.cases_head, h₂.cases_head with
    | .inl heq₁, .inl heq₂ => exact heq₁.symm.trans heq₂
    | .inr ⟨_, hra, hrc⟩, .inr ⟨_, hra', hrc'⟩ =>
      exact ih _ hra hrc h_norm₁ ((hra.unique hra') ▸ hrc')
    | .inl heq₁, .inr _ => exact ((heq₁ ▸ h₂).norm_same h_norm₁)
    | .inr _, .inl heq₁ => exact ((heq₁ ▸ h₁).norm_same h_norm₂).symm

theorem RedEtaTrans.norm_unique (h₁ : RedEtaTrans A B) (h_norm₁ : IsNormEta B)
  (h₂ : RedEtaTrans A C) (h_norm₂ : IsNormEta C) : B = C :=
  RedEtaReflTrans.norm_unique h₁.to_reflTransGen h_norm₁ h₂.to_reflTransGen h_norm₂

theorem RedEtaReflTrans.to_trans (h_red : RedEtaReflTrans A B) (heq : A ≠ B) : RedEtaTrans A B := by
  change Relation.ReflTransGen _ _ _ at h_red
  rw [← Relation.reflGen_transGen] at h_red
  induction h_red with
  | refl => simp_all
  | single h => exact h

theorem IsNormEta.complete (h : A.IsNormEta) : (step_η? A) = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨e', ⟨h₂⟩⟩ heq
  exact (h ⟨_, h₂⟩)

theorem IsNormEta.complete_reduce (h : A.IsNormEta) : reduce_η A = A := by
  unfold reduce_η
  rw [h.complete]

theorem step_η?_none : step_η? A = .none → A.IsNormEta := fun h_step ⟨e', h_red⟩ => by
  have h := h_red.complete
  simp_all

theorem reduce_η_norm (h : reduce_η A = B) : B.IsNormEta := by
  induction A using instWellFoundedEta.induction generalizing B with
  | h a ih =>
    unfold reduce_η at h
    split at h
    · rename_i hred heq
      have h := ih _ hred rfl
      simp_all
    · rename_i heq
      have h := step_η?_none heq
      simp_all

theorem RedEta.reduce_same (h : RedEta A B) : reduce_η A = reduce_η B := by
  apply RedEtaReflTrans.norm_unique
  · exact reduce_η_sound rfl
  · exact reduce_η_norm rfl
  · exact .trans (.single h) (reduce_η_sound rfl)
  · exact reduce_η_norm rfl

theorem RedEtaReflTrans.complete (h₁ : RedEtaReflTrans A B) (h_norm : B.IsNormEta) : reduce_η A = B := by
  match h₁.cases_head with
  | .inl h =>
    simp_all
    exact h_norm.complete_reduce
  | .inr ⟨c, h₁, h₂⟩ =>
    have _h : c.size.fst < A.size.fst := h₁.decreasing
    have h := RedEtaReflTrans.complete h₂ h_norm
    rw [h₁.reduce_same, h]
termination_by A.size.fst

instance : Decidable (RedEtaReflTrans A B ∧ B.IsNormEta) :=
  if h : reduce_η A = B then
    .isTrue (⟨reduce_η_sound h, reduce_η_norm h⟩)
  else
    .isFalse (fun ⟨h_red, heq⟩ => by simp [h_red.complete heq] at *)

instance : Decidable (∃ C, RedEtaReflTrans A C ∧ RedEtaReflTrans B C ∧ C.IsNormEta) :=
  if heq : reduce_η A = reduce_η B then .isTrue
    ⟨_, reduce_η_sound rfl, reduce_η_sound heq.symm, reduce_η_norm rfl⟩
  else
    .isFalse (fun ⟨C, h₁, h₂, h_norm⟩ => by
      have ha := h₁.complete h_norm
      have hb := h₂.complete h_norm
      simp_all)

end Expr
