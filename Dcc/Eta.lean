import Dcc.Ast
import Dcc.Step
import Dcc.Types

/-
(DCC Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1)) ∘
           Fstc((Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1)) Sort 1)))

need to reduce this
-/

/-
Π eta rule is very suspicious.

is wrong entirely.

should be just left and right components.
one rule for if there is an env, one for if not.

neither f_α nor f_β should be normalized, but f_β should be RedEta'd
This means we will need β in size.

this is problematic for App, but we can fix.

for app, final β =
`(Sort n, (f_β env) ∘ Snd'(t_f, α))


need to sum f_β, env, t_f, and α
Size(`(Sort n, (f_β env) ∘ Snd'(t_f, α)))
= (1 + (Size(f_β) + Size(env))) + Size(α) + 2

Size(App(m, n, f_α, f_β) env))
= Size(App(m, n, f_α, f_β)) + Size(env)
= (((Size(f_β) + Size(env)) + 1) + 2) + 1
= Size(f_β) + Size(env) + 4 + Size(Σ(`(⊤, `(..., (f_α env)))))

maybe we want to split Size up? Then put Appl inside the other Red?
Could work.
Putting Appl in main RedAff, make size of tys 0 in RedAff, then
make a TySize. Yep.
Will not help.
We will duplicate env anyway.
We need to make a separate RedTy.

If we keep the size of Π and all Ty's 0 in main Size,
then get rid of appl rule in RedEta, keep in RedAff,
we will be set.

so need f_α * 2

App(m, n, f_α, f_β) = (1 + ((Size(f_β) + Size(env)) + (Size((f_α env)))

env is not duplicated. Snd' type argument does not count.

Appty breaks confluence.

Why can't we just plug App into its own inductive?
-/

namespace Expr

inductive RedMeta : Expr → Expr → Prop
  | appl      : RedAffReflTrans (DCC (f_α env)) α
    → α.IsNormAff
    → RedMeta (DCC (App(m, n, f_α, f_β) env)) (App'.type α f_α f_β env m)

def IsNormMeta (e : Expr) : Prop := ¬ ∃ e', RedMeta e e'

theorem RedMeta.decreasing (h : RedMeta e e') : (size e').fst < (size e).fst := by
  cases h; grind

@[simp] def step_meta? (e : Expr) : Option ((e' : Expr) × (PLift (RedMeta e e'))) :=
  match e with
  | DCC (App(_m, _n, _f_α, _f_β) _env) => .some ⟨_, ⟨.appl (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | _ => .none

def RedMetaTrans     := Relation.TransGen RedMeta
def RedMetaReflTrans := Relation.ReflTransGen RedMeta

@[aesop safe apply, grind ., grind →, simp] theorem RedMetaTrans.decreasing : RedMetaTrans e e' → (size e').fst < (size e).fst := by
  intro h
  induction h with
  | single h => exact h.decreasing
  | tail h₁ hr ih =>
    have h := hr.decreasing
    grind

theorem RedMeta.complete (h_red : RedMeta A B) : step_meta? A = .some ⟨B, ⟨h_red⟩⟩ :=
  match h_red with
  | .appl hrt h_norm => by
    have h := hrt.complete h_norm
    aesop

def sn_meta (e : Expr) : Acc (fun b a => RedMeta a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing
  exact e'.sn_meta)
termination_by e.size.fst

instance instWellFoundedMeta : WellFounded (fun a b => RedMeta b a) := ⟨sn_meta⟩

def reduce_meta (e : Expr) : Expr :=
  match step_meta? e with
  | .some ⟨e', ⟨h⟩⟩ =>
    -- This hypothesis allows the recursion. Easy to prove.
    have _h_size : e'.size.fst < e.size.fst := h.decreasing
    e'.reduce_meta
  | .none => e
termination_by e.size.fst

theorem reduce_meta_sound (heq : reduce_meta A = B) : RedMetaReflTrans A B := by
  induction A using instWellFoundedMeta.induction generalizing B with
  | h a ih =>
    unfold reduce_meta at heq
    split at heq
    case h_1 h_red h_step_eq =>
      exact Relation.ReflTransGen.trans (.single h_red) (ih _ h_red heq)
    case h_2 => simp_all only [forall_eq']; exact .refl

theorem sn_meta_trans (e : Expr) : Acc (fun b a => RedMetaTrans a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing
  exact e'.sn_meta_trans)
termination_by e.size.fst

instance instWellFoundedMetaTrans : WellFounded (fun a b => RedMetaTrans b a) := ⟨sn_meta_trans⟩

theorem IsNormMeta.complete (h : IsNormMeta A) : (step_meta? A) = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨e', ⟨h₂⟩⟩ heq
  exact (h ⟨_, h₂⟩)

theorem IsNormMeta.complete_reduce (h : IsNormMeta A) : reduce_meta A = A := by
  unfold reduce_meta
  rw [h.complete]

theorem step_meta_none : step_meta? A = .none → A.IsNormMeta := fun h_step ⟨e', h_red⟩ => by
  have h := h_red.complete
  simp_all

theorem reduce_meta_norm (h : reduce_meta A = B) : B.IsNormMeta := by
  induction A using instWellFoundedMeta.induction generalizing B with
  | h a ih =>
    unfold reduce_meta at h
    split at h
    · rename_i hred heq
      have h := ih _ hred rfl
      simp_all
    · rename_i heq
      have h := step_meta_none heq
      simp_all

@[simp] theorem RedMeta.unique (h₁ : RedMeta A B) (h₂ : RedMeta A C) : B = C := by
  induction h₁ generalizing C with
  | appl hrt₁ hnorm₁ => cases h₂ with
    | appl hrt₂ hnorm₂ =>
      have h := hrt₁.norm_unique hnorm₁ hrt₂ hnorm₂
      simp_all

theorem RedMeta.norm_unique (h₁ : RedMeta A B) (h_norm : IsNormMeta B) (h_trans : RedMetaTrans A C) : B = C := by
  induction h_trans with
  | single h =>
    exact h₁.unique h
  | tail h ih heq => exact (h_norm ⟨_, heq ▸ ih⟩).elim

theorem RedMetaReflTrans.norm_same (h : RedMetaReflTrans A B) (h_norm : A.IsNormMeta) : A = B := by
  induction h with
  | refl => rfl
  | tail hrt h_red heq =>
    rename_i b c
    exact (h_norm ⟨c, heq ▸ h_red⟩).elim

theorem RedMetaReflTrans.norm_unique (h₁ : RedMetaReflTrans A B) (h_norm₁ : IsNormMeta B)
  (h₂ : RedMetaReflTrans A C) (h_norm₂ : IsNormMeta C) : B = C := by
  induction A using instWellFoundedMeta.induction generalizing B with
  | h _ ih =>
    match h₁.cases_head, h₂.cases_head with
    | .inl heq₁, .inl heq₂ => exact heq₁.symm.trans heq₂
    | .inr ⟨_, hra, hrc⟩, .inr ⟨_, hra', hrc'⟩ =>
      exact ih _ hra hrc h_norm₁ ((hra.unique hra') ▸ hrc')
    | .inl heq₁, .inr _ => exact ((heq₁ ▸ h₂).norm_same h_norm₁)
    | .inr _, .inl heq₁ => exact ((heq₁ ▸ h₁).norm_same h_norm₂).symm

theorem RedMeta.reduce_same (h : RedMeta A B) : reduce_meta A = reduce_meta B := by
  apply RedMetaReflTrans.norm_unique
  · exact reduce_meta_sound rfl
  · exact reduce_meta_norm rfl
  · exact .trans (.single h) (reduce_meta_sound rfl)
  · exact reduce_meta_norm rfl

theorem RedMetaReflTrans.complete (h₁ : RedMetaReflTrans A B) (h_norm : B.IsNormMeta) : reduce_meta A = B := by
  match h₁.cases_head with
  | .inl h =>
    simp_all
    exact h_norm.complete_reduce
  | .inr ⟨c, h₁, h₂⟩ =>
    have _h : c.size.fst < A.size.fst := h₁.decreasing
    have h := RedMetaReflTrans.complete h₂ h_norm
    rw [h₁.reduce_same, h]
termination_by A.size.fst

theorem EtaSize.sound (_h : Expr.eta_size e = ⟨n, ⟨h⟩⟩) : EtaSize e n := h

@[aesop safe destruct, grind =_, grind →, simp] theorem EtaSize.complete (h : EtaSize e n) : eta_size e = ⟨n, .up h⟩ := by
  induction h with
  | app' | tintro | bot | top | snd' | id | snd | fst | sort => rfl
  | comp _ _ ih₁ ih₂ | coup _ _ ih₁ ih₂ => rw [eta_size, ih₁, ih₂]
  | pi _ ih | sig _ ih | appl _ ih | quot _ ih | curr _ ih => rw [eta_size, ih]
  | subst _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ => rw [eta_size, ih₁, ih₂]

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

def IsNormEta (e : Expr) : Prop := ¬ ∃ e', RedEta e e'

@[simp] theorem size_lt_eta_size : (size e).fst < (eta_size e).fst := by
  induction e <;> grind

@[aesop safe apply, grind ., grind →, simp] theorem RedEta.decreasing (h : RedEta e e') : (eta_size e').fst < (eta_size e).fst := by
  induction h
  repeat (simp_all; try grind)

def sn_eta (e : Expr) : Acc (fun b a => RedEta a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing
  exact e'.sn_eta)
termination_by e.eta_size.fst

def RedEtaTrans     := Relation.TransGen RedEta
def RedEtaReflTrans := Relation.ReflTransGen RedEta

@[aesop safe apply, grind ., grind →, simp] theorem RedEtaTrans.decreasing : RedEtaTrans e e' → (eta_size e').fst < (eta_size e).fst := by
  intro h
  induction h with
  | single h => exact h.decreasing
  | tail h₁ hr ih =>
    have h := hr.decreasing
    grind

theorem sn_eta_trans (e : Expr) : Acc (fun b a => RedEtaTrans a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing
  exact e'.sn_eta_trans)
termination_by e.eta_size.fst

/-
η-reduction is deterministic
-/
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
    | snd' | ai | uncur => cases hr
  | ai | uncur | snd' =>
    cases h₂
    · rename_i h; cases h
    · rfl
  | curr_quot | snd | fst | idr | beta | fsi => cases h₂; rfl

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
  | DCC (Λ(α, _b, `(_c, x)) y) =>
    if heq : DCC (Λ(α, _b, `(_c, x)) y) = (DCC (Λ(α, Id(α), `(Coup(Id(α)), x)) y)) then
      heq ▸ .some ⟨_, ⟨.curr_quot⟩⟩
    else .none
  | DCC (Λ(_α, _β, _x ∘ Fstc(_β₂)) _y) => .some ⟨_, ⟨.curr_fst⟩⟩
  | DCC Σ(f_β) =>
    match f_β.step_η? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.sig' h⟩⟩
    | _ => .none
  | DCC (Σ(f_β) _env) =>
    match (DCC Σ(f_β)).step_η? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.sig h⟩⟩
    | _ => .none
  | DCC (Π(_f_α, f_β) _env) =>
    match (DCC Π(_f_α, f_β)).step_η? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi h⟩⟩
    | _ => .none
  | DCC (Π(_f_α, f_β)) =>
    match f_β with
    | DCC `(_β, x) =>
      match x.step_η? with
      | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi_quot h⟩⟩
      | _ => .none
    | x =>
      match x.step_η? with
      | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi' h⟩⟩
      | _ => .none
  | (DCC (_f ∘ Id(_α))) => .some ⟨_, ⟨.idr⟩⟩
  | (DCC (Fst(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨_x, _y⟩) => .some ⟨_, ⟨.fst⟩⟩
  | (DCC (Snd(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨_x, _y⟩) => .some ⟨_, ⟨.snd⟩⟩
  | DCC Λ(α, β, x) =>
    match x.step_η? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.curr h⟩⟩
    | .none =>
      match DCC Λ(α, β, x) with
      | (DCC Λ(_α, _b, _x ∘ (Snd(_c) _env))) => .some ⟨_, ⟨.snd'⟩⟩
      | (DCC Λ(_α, _β, (App'(_f_α, _f_β) _env))) => .some ⟨_, ⟨.ai⟩⟩
      | (DCC Λ(_α, _β,
        (App'(_f_α, _f_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨_f ∘ (Fst(_x) _env₁), (Snd(_x₂) _env₂)⟩)) =>
        .some ⟨_, ⟨.uncur⟩⟩
      | _ => .none
  | (DCC ((App'(_f_α, _f_β) _env) ∘ ⟦_m, _α, _b, _γ⟧⟨Λ(__α, __β, _x), _y⟩)) => .some ⟨_, ⟨.beta⟩⟩
  | (DCC ⟦_m, _a, _b, _c⟧⟨(Fst(_β) _env), (Snd(_β₂) _env₂)⟩) => .some ⟨_, ⟨.fsi⟩⟩
  | _ => .none

def reduce_η (e : Expr) : Expr :=
  match step_η? e with
  | .some ⟨e', ⟨h⟩⟩ =>
    -- This hypothesis allows the recursion. Easy to prove.
    have _h_size : e'.eta_size.fst < e.eta_size.fst := h.decreasing
    e'.reduce_η
  | .none => e
termination_by e.eta_size.fst

theorem reduce_η_sound (heq : reduce_η A = B) : RedEtaReflTrans A B := by
  induction A using instWellFoundedEta.induction generalizing B with
  | h a ih =>
    unfold reduce_η at heq
    split at heq
    case h_1 h_red h_step_eq =>
      exact Relation.ReflTransGen.trans (.single h_red) (ih _ h_red heq)
    case h_2 => simp_all only [forall_eq']; exact .refl

theorem RedEta.complete (h_red : RedEta A B) : step_η? A = .some ⟨B, ⟨h_red⟩⟩ := by
  induction h_red <;> (unfold step_η?; aesop)

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
    have _h : c.eta_size.fst < A.eta_size.fst := h₁.decreasing
    have h := RedEtaReflTrans.complete h₂ h_norm
    rw [h₁.reduce_same, h]
termination_by A.eta_size.fst

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
