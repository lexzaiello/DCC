import Dcc.Judge
import Dcc.Relation
import Dcc.Types
--import Dcc.Tactic.Reduce
import Dcc.Aff.Red
import Dcc.Eta.Red

namespace Expr

/-
Reduces (f x)
view (Reduces (f x)) B
=> .pi (Reduces x x')

match B to

-/

namespace Reduces

@[dcc_force_reduce, inline] abbrev red_aff (e : Expr) := (reduce RedAff e).fst
@[dcc_force_reduce, inline] abbrev red_eta (e : Expr) := (reduce RedEta e).fst

/-
if r A B, then reduce A = reduce B

Red A B

need some way to slot RedAff back into reduce
-/

@[dcc_force_reduce, grind =]
theorem reduce_aff_pi : (reduce RedAff (DCC (Π(f_α, f_β) env))).fst = (DCC (Π(f_α, f_β) #((reduce RedAff env).fst))) := by
  induction env using RedAff.instRedRel.wellFounded.induction with
  | h x a =>
    conv =>
      left
      dcc_simp (! ! !)
      rfl
    split
    case h_1 hr heq =>
      cases hr with
      | congrFun h => cases h
      | congrArg h =>
        have h := a _ h
        split at heq
        · contradiction
        · dcc_simp_all (! !)
          have ⟨ha, _⟩ := heq
          cases ha
          rfl
        · contradiction
    case h_2 heq =>
      split at heq
      · contradiction
      · contradiction
      case h_3 =>
        dcc_simp (! !)
        split
        case h_1 ih _ _ hr heq =>
          exact (ih _ hr heq).elim
        · rfl



inductive View : Expr → Expr → Expr → Prop
  | pi        : View
    (DCC (Π(f_α, f_β) env))
    (DCC (Π(f_α, f_β) #(red_aff env)))
    (red_eta (DCC (Π(f_α, f_β) #(red_aff env))))

def view (hR : Reduces A C) : Option ((B : Expr) × PLift (View A B C)) :=
  match A with
  | (DCC (Π(f_α, f_β) env)) =>
    .some ⟨(DCC (Π(f_α, f_β) #(red_aff env))), ⟨by
      have heq := hR.complete
      dcc_simp (! !) at heq
      rw [reduce_aff_pi] at heq
      have mk_heq : C = (red_eta (DCC (Π(f_α, f_β) #(red_aff env)))) := by
        dcc_simp_all (! !)
      rw [mk_heq]
      exact View.pi⟩⟩
  | _ => .none

end Reduces

end Expr

namespace Expr

namespace RedAff

theorem pi (h : RedAff (DCC (Π(f_α, f_β) env)) B) : ∃ env', B = (DCC (Π(f_α, f_β) env')) := by
  cases h with
  | congrFun h => cases h
  | congrArg h =>
    rename_i x'
    exact ⟨x', rfl⟩

@[dcc_reduce]
theorem no_red_pi_aff (h_r : RedAff (DCC (Π(f_α, f_β) env)) (DCC x = y)) : False := by
  cases h_r

inductive ProjectEq : Expr → Expr → Prop
  | fstc : ProjectEq (DCC (Fstc(f_β) ⟦β⟧(x = y, b))) (DCC (x = y))
  | sndc : ProjectEq (DCC (Sndc(f_β) ⟦β⟧(a, x = y))) (DCC (x = y))
  | quot : ProjectEq (DCC (`(β', x = y) ⟦β⟧(a, b)))  (DCC (x = y))

def project_eq (hr : RedAff (DCC (f ⟦β⟧(a, b))) (DCC x = y)) : ProjectEq (DCC (f ⟦β⟧(a, b))) (DCC x = y) := by
  cases hr with
  | quot => exact .quot
  | sndc => exact .sndc
  | fstc => exact .fstc

inductive RedEq : Expr → Expr → Prop
  | proj : RedAff.ProjectEq A (DCC (x = y)) → RedEq A (DCC (x = y))
  | id   : RedEq (DCC (Id(α) (x = y))) (DCC (x = y))
  | quot : RedEq (DCC (`(α, (x = y)) z)) (DCC (x = y))

theorem eq (h : RedEta A (DCC (x = y))) : ∃ f_α env, A = (DCC (Eql(f_α) env x)) := by
  cases h with
  | eql => exact ⟨_, _, rfl⟩

end RedAff

namespace RedEta

theorem eq_eql (h_step : RedEta A (DCC (x = y))) : ∃ f_α env, x = y ∧ A = (DCC (Eql(f_α) env x)) := by
  cases h_step with
  | eql => exact ⟨_, _, rfl, rfl⟩

@[dcc_reduce]
theorem eq_norm_refl (h_step : RedEta A (DCC (x = y))) (h : IsNorm RedEta (DCC (x = y))) : x = y := by
  cases h_step with
  | eql => rfl

@[dcc_reduce]
theorem no_coup (h : RedEta (DCC Coup(β)) B) : False := by
  cases h

@[dcc_reduce]
theorem no_pi_eq (h_r : RedEta (DCC (Π(f_α, f_β) env)) (DCC x = y)) : False := by
  cases h_r

inductive RedEq : Expr → Expr → Prop
  | eql : RedEq (DCC (Eql(f_α) env x)) (DCC x = x)

/-inductive Reduced.RedEq : Expr → Expr → Prop
  | curr : -/

def red_eq (hr : RedEta A (DCC (x = y))) : RedEta.RedEq A (DCC (x = y)) := by
  cases hr with
  | eql => exact .eql

end RedEta

def head (e : Expr) : Expr :=
  match e with
  | .app f _x => f.head
  | e => e

namespace RedAffReflTrans

@[dcc_reduce]
theorem no_coup_eq (h_r : RedAffReflTrans (DCC Coup(β)) (DCC x = y)) : False := by
  cases h_r.cases_head with
  | inl h => simp_all
  | inr h =>
    have ⟨C, h₁, h₂⟩ := h
    cases h₁ with
    | coup h =>
      have h_dec := RedAff.instRedRel.decreasing h
      exact no_coup_eq h₂
termination_by β.size

@[dcc_reduce]
theorem no_pi_eq (h_r : RedAffReflTrans (DCC (Π(f_α, f_β) env)) (DCC x = y)) : False := by
  cases h_r.cases_head with
  | inl h => simp_all
  | inr h =>
    have ⟨C, h₁, h₂⟩ := h
    cases h₁ with
    | congrFun h => cases h
    | congrArg h =>
      rename_i x'
      have h_dec := RedAff.instRedRel.decreasing h
      exact no_pi_eq h₂
termination_by env.size

theorem red_aff_pi' (h : RedAffReflTrans (DCC (Π(f_α, f_β) env)) B) : ∃ env', (B = (DCC (Π(f_α, f_β) env')) ∧ RedAffReflTrans env env') := by
  match h.cases_head with
  | .inl h => exact ⟨_, ⟨h.symm, .refl⟩⟩
  | .inr ⟨C, hr₁, hr⟩ =>
    have ⟨env', heq⟩ := hr₁.pi
    have h_dec : env'.size < env.size := by
      rw [heq] at hr₁
      cases hr₁ with
      | congrFun h => cases h
      | congrArg h =>
        exact RedAff.instRedRel.decreasing h
    have ⟨env', ⟨heq, hr⟩⟩ := red_aff_pi' (heq ▸ hr)
    exact ⟨env', heq, by
      cases hr₁ with
      | congrFun h => cases h
      | congrArg h =>
        cases heq
        exact .trans (.single h) (by assumption)⟩
termination_by env.size

theorem pi_norm
  (h : RedAffReflTrans (DCC (Π(f_α, f_β) env)) B)
  (hn : IsNorm RedAff B) :
    ∃ env', (B = (DCC (Π(f_α, f_β) env'))
      ∧ RedAffReflTrans env env'
      ∧ IsNorm RedAff env') := by
  match h.cases_head with
  | .inl h =>
    exact ⟨env, h.symm, .refl, (h ▸ hn).congrArg⟩
  | .inr ⟨C, h₁, h₂⟩ =>
    cases h₁ with
    | congrFun h => cases h
    | congrArg h =>
      rename_i x'
      have h_dec : x'.size < env.size := RedAff.instRedRel.decreasing h
      have ⟨env', heq, hrt, hn⟩ := pi_norm h₂ hn
      exact ⟨env', heq, .trans (.single h) hrt, hn⟩
termination_by env.size

open RedAff in
def red_eq (hr : RedAffReflTrans A (DCC (x = y))) : (∃ B,
  RedAffReflTrans A B ∧ RedAff B (DCC (x = y)) ∧ RedEq B (DCC (x = y))) ∨ (A = (DCC (x = y))) := by
  cases hr with
  | refl => exact .inr rfl
  | tail ih h => exact .inl ⟨_, ih, by assumption, red_eq⟩

end RedAffReflTrans

namespace RedEtaReflTrans

@[dcc_reduce]
theorem no_coup_eq (h_r : RedEtaReflTrans (DCC Coup(β)) (DCC x = y)) : False := by
  cases h_r.cases_head with
  | inl h => simp_all
  | inr h =>
    have ⟨C, h₁, h₂⟩ := h
    cases h₁

@[dcc_reduce]
theorem no_pi_eq (h_r : RedEtaReflTrans (DCC (Π(f_α, f_β) env)) (DCC x = y)) : False := by
  let f_β₀ := f_β
  cases h_r.cases_head with
  | inl h => simp_all
  | inr h =>
    have ⟨C, h₁, h₂⟩ := h
    cases heq₁ : h₁ with
    | pi h =>
      cases h with
      | pi_quot h=>
        rename_i p'
        have h_dec := RedEta.instRedRel.decreasing p'
        rename_i x x' β
        have _heq : (β.quot x').size < f_β₀.size := by
          grind
        exact no_pi_eq h₂
      | pi' h =>
        have h_dec := RedEta.instRedRel.decreasing h
        exact no_pi_eq h₂
termination_by f_β.size

end RedEtaReflTrans

inductive NfType : Expr → Prop
  | sort  : NfType (DCC Sort m)
  | eql   : NfType (DCC x = x)
  | fn    : NfType (DCC (Π(f_α, f_β) env))
  | top   : NfType (DCC ⊤)
  | coup  : NfType (DCC Coup(f_β))
  | sigma : NfType (DCC (Σ(f_α, f_β) env))


theorem RedEtaReflTrans.pi_norm
  (h : RedEtaReflTrans (DCC (Π(f_α, f_β) env)) B)
  (hn : IsNorm RedEta B) :
    ∃ f_β', B = (DCC (Π(f_α, f_β') env)) := by
  match h.cases_head with
  | .inl h => exact ⟨_, h.symm⟩
  | .inr ⟨c, h₁, h₂⟩ =>
    cases h₁ with
    | pi h =>
      cases h with
      | pi_quot hr =>
        rename_i x x' β
        have h_dec : (DCC `(β, x')).size < (DCC `(β, x)).size := by
          have h := RedEta.instRedRel.decreasing hr
          grind
        exact pi_norm h₂ hn
      | pi' hr =>
        rename_i β'
        have h_dec : β'.size < f_β.size := by
          exact RedEta.instRedRel.decreasing hr
        exact pi_norm h₂ hn
termination_by f_β.size

@[dcc_reduce]
def NfType.eq_elim (heq : τ = (DCC x = y)) (is_nf : NfType τ) : x = y := by
  cases heq; cases is_nf; rfl

--theorem IsNorm.coup_

@[dcc_reduce]
theorem RedEtaReflTrans.coup (h : RedEtaReflTrans (DCC Coup(β)) B) : (DCC Coup(β)) = B := by
  match h.cases_head with
  | .inl h => exact h
  | .inr ⟨C, h₁, h₂⟩ => cases h₁

theorem Reduces.coup (h : Reduces (DCC Coup(β)) B) : ∃ β', B = (DCC Coup(β')) :=
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ => by
    match hr₁.cases_head with
    | .inl h =>
      cases h
      match hr₂.cases_head with
      | .inl h => exact ⟨_, h.symm⟩
      | .inr ⟨_, h₁, h₂⟩ => cases h₁
    | .inr ⟨C, h₁, h₂⟩ =>
      have h_dec := RedAff.instRedRel.decreasing h₁
      cases h₁ with
      | coup hβ =>
        exact Reduces.coup ⟨h₂, hn₁, hr₂, hn₂⟩
termination_by (DCC Coup(β)).size

@[grind]
def type_size (τ : Expr) : ℕ :=
  match τ with
  | DCC ⊤ | DCC Sort _m => 0
  | DCC (Π(f_α, f_β)) =>
    (type_size f_α) + (type_size f_β) + 1
  | DCC (Π(f_α, f_β) env) =>
    (type_size f_α) + (type_size f_β) + (type_size env) + 1
  | DCC Coup(_f_β) => 1
  | DCC (_x = _y) => 0
  | DCC Id(_α) => 1
  | DCC (Id(_α) x) => x.type_size + 1
  | DCC (f _x) => f.type_size
  | _ => 0


theorem Reduces.pi_shape (h : Reduces (DCC (Π(f_α, f_β) env)) τ) : ∃ f_β' env', τ = (DCC (Π(f_α, f_β') env')) := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    have ⟨env', heq, hrt⟩ := hr₁.pi_norm hn₁
    cases heq
    have ⟨_, heq⟩ := hr₂.pi_norm hn₂
    exact ⟨_, _, heq⟩

def RedAff.red_eq (hr : RedAff A (DCC (x = y))) : RedEq A (DCC (x = y)) := by
  cases hr with
  | id => exact .id
  | fstc => exact .proj .fstc
  | sndc => exact .proj .sndc
  | quot => exact .quot

def RedEtaTrans.red_eq (hr : RedEtaTrans A (DCC (x = y))) :
  (∃ f_α env, A = (DCC (Eql(f_α) env x)) ∧ x = y) ∨ A = (DCC (x = y)) := by
  cases hr using Relation.TransGen.head_induction_on with
  | single h =>
    cases h
    exact .inl ⟨_, _, rfl, rfl⟩
  | head hr ih =>
    have h_dec := RedEta.instRedRel.decreasing hr
    have h := red_eq ih
    match h with
    | .inl ⟨f_α, env, heq₁, heq₂⟩ =>
      cases heq₁ ▸ hr with
      | pi =>
        have ⟨_, h⟩ := RedEtaReflTrans.pi_norm
          (.trans (.single hr) (.single (heq₁.symm ▸ RedEta.eql)))
          (fun ⟨_, h⟩ => by cases h)
        cases h
    | .inr h =>
      cases h
      cases hr with
      | eql =>
        exact .inl ⟨_, _, rfl, rfl⟩
termination_by A.size

/-def Relation.Reduced.red_aff_eq (hr : Reduced A (DCC (x = y)))
  : (∃ B,
  Relation.ReflTransGen RedAff A B ∧ RedAff B (DCC (x = y)) ∧ RedAff.RedEq B (DCC (x = y))) := by
  match hr with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    have h := refl_trans_eta_eq hr₂
    match h with
    | .inl ⟨f_α, env, heq₁, heq₂⟩ =>
      
      sorry
    | .inr h =>
      sorry
    rw [← Relation.reflGen_transGen] at hr₂
    /-
      if it is TransGen, then use lemma
      to extract that it is Eql
    -/
    sorry-/

/-theorem RedAff.project_eq (hr : RedAff (DCC (f ⟦β⟧(a, b))) (DCC x = y)) :
  (a = (DCC x = y) ∧ (∃ f_β, f = DCC (Fstc(f_β))))
    ∨ (b = (DCC x = y) ∧ (∃ f_β, f = DCC (Sndc(f_β))))
    ∨ (∃ β', f = (DCC `(β', (x = y)))) := by
  cases hr with
  | quot =>
    exact .inr (.inr ⟨_, rfl⟩)
  | sndc =>
    exact .inr (.inl ⟨rfl, _, rfl⟩)
  | fstc =>
    exact .inl ⟨rfl, _, rfl⟩-/

--theorem Reduced.

theorem Judge.norm_eta (ht : Judge e τ) : IsNorm RedEta τ := by
  cases ht
  any_goals (exact Reduces.norm_eta (by assumption))
  case tintro | bot | top | sort =>
    intro ⟨_, h⟩
    cases h
  case app => exact Reduced.norm_eta (by assumption)
  case eq =>
    intro ⟨_, h⟩
    cases h

theorem Judge.refl_canon (h : Judge e (DCC x = x)) : ∃ f_α env, Reduces e (DCC (refl(f_α) env x)) := by
  induction e generalizing x with
  | refl =>
    cases h with
    | refl ht_a hr =>
      have ⟨f_β', env', h⟩ := hr.pi_shape
      simp_all
  | app _ _ ih₁ ih₂ =>
    cases h with
    | app h_t_f h_t_x h_r_α h_r_τ =>
      match h_r_τ with
      | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
        have h := hr₂.red_eq
        
        /-match hr₂.cases_head with
        | .inl h =>
          cases h
          cases hr₁ using Relation.TransGen.head_induction_on with
          | single h => cases h
          | head h ih =>
            have h_eq_red := refl_trans_red_aff_eq ih.to_reflTransGen
            match h_eq_red with
            | .inl ⟨B, h₁, h₂⟩ =>
              
              sorry
            | .inr h =>
              sorry
            cases h with
            | curr =>
              
              cases ih using Relation.TransGen.head_induction_on with
              | single h =>
                match h.project_eq with
                | .inl ⟨heq₁, _, heq₂⟩ =>
                  cases heq₁; cases heq₂
                  cases h with
                  | fstc =>
                    cases h_t_f with
                    | app =>
                      
                      sorry
                | .inr (.inl h) =>
                  sorry
                | .inr (.inr h) =>
                  sorry
              | head h ih =>
                sorry-/

/-
An affine expression reduces to =(x, y)
-/

/-@[grind ., grind →]
theorem RedEta.maintains_type_size (hr : RedEta A B) : type_size B = type_size A := by
  induction A generalizing B
  any_goals (
    focus
    cases hr <;> grind
  )
  case app =>
    cases hr
    any_goals (grind)
    · 
      sorry

theorem RedAff.decreases_type_size (hr : RedAff A B) : type_size B < type_size A := by
  induction hr with
  | quot =>
    
    sorry-/

/-theorem Judge.pi_dom_id (ht : Judge f (DCC (Π(f_α, f_β) env))) : ∃ m, f_α = (DCC Id(Sort m)) := by
  cases ht with
  | app h_t_f h_r_α h_t_x h_r_τ =>
    have ⟨m, heq⟩ := h_t_f.pi_dom_id
    cases heq
    
    sorry

theorem Judge.pi_dom_id (ht : Judge f (DCC (Π(f_α, f_β) env))) : ∃ m, f_α = (DCC Id(Sort m)) := by
  induction f generalizing f_α f_β env with
  | app _ _ ih₁ ih₂ =>
    cases ht with
    | app h_t_f h_t_x h_r_α h_r_τ =>
      have ⟨m, h⟩ := ih₁ h_t_f
      cases h
      
      sorry-/

/-
Need to hook in the possible "operations" a type can do (kinda like parametricity):


-/

@[grind]
def is_canon_type (τ e : Expr) : Prop :=
  match τ with
  | DCC Sort m =>
    match e with
    | DCC Sort n => n + 1 = m
    | DCC _x = _y => m = 0
    -- might need more conditions. ∃, ...
    | DCC Coup(_β) => True
    | _ => False
  | DCC (x = y) => ∃ f_α env, x = y ∧ e = (DCC (refl(f_α) env x))
  | DCC ⊤ => e = DCC ∗
  | DCC Coup(f_β) =>
    ∃ x y t_y, e = DCC ⟦f_β⟧(x, y) ∧ Judge y t_y ∧ Reduces (DCC (f_β x)) t_y
  | DCC (Id(t_α) α) =>
    have h_dec : α.type_size < (DCC (Id(t_α) α)).type_size := by
      grind
    is_canon_type α e
  | DCC (Π(f_α, f_β) x_α) =>
    ∀ (x : Expr)
      (_h_size₁ : (DCC (f_α x_α)).type_size < (DCC (Π(f_α, f_β) x_α)).type_size)
      (_h_size₂ : (DCC (f_β x_α x)).type_size < (DCC (Π(f_α, f_β) x_α)).type_size)
      (_h_canon : is_canon_type (DCC (f_α x_α)) x), is_canon_type (DCC (f_β x_α x)) (DCC (e x))
  /-| DCC (Π(f_α, f_β) env) =>
    ∀ (x : Expr)
      (_h_size₁ : (DCC (f_α env)).type_size < (DCC (Π(f_α, f_β) env)).type_size)
      (_h_size₂ : (DCC (f_β env x)).type_size < (DCC (Π(f_α, f_β) env)).type_size)
      (_h_canon : is_canon_type (DCC (f_α env)) x), is_canon_type (DCC (f_β env x)) (DCC (e x))-/
  | _ => False
termination_by τ.type_size

theorem canon_elim_eq (ht : is_canon_type (DCC x = y) e) : x = y := by
  grind


theorem Judge.is_canon (ht : Judge e τ) : is_canon_type τ e := by
  induction ht with
  | sort | eq =>
    grind
  | app h_t_f h_r_α h_t_x h_r_τ h_canon_f h_canon_x =>
    rename_i f f_α f_β x_α α x τ
    simp [is_canon_type] at h_canon_f
    have h := h_canon_f x (by
      unfold type_size
      split
      any_goals (first | grind | simp_all)
      
      /-· grind
      · grind
      · simp_all
      · simp_all
        grind
      · simp_all
      · grind
      · simp_all
      · grind
      · simp_all
        rename_i heq
        have ⟨ha, hb⟩ := heq
        cases ha; cases hb
        grind
      · grind-/)
      (by
        simp [type_size]
        unfold type_size
        split <;> grind)
      (by sorry)
    
    sorry

/-def Judge.is_nf (ht : Judge e τ) : NfType τ := by
  cases ht with
  | eql _ hred
  | sigma _ _ hred
  | pair _ _ _ _ _ _ hred
  | sndc _ _ hred | fstc _ _ hred
  | quot _ _ hred | pi _ _ hred | curr _ _ _ _ _ hred | comp _ _ _ hred
  | comp' _ _ _ _ _ hred | id _ hred | refl _ hred | eq _ hred =>
    match hred with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      have ⟨env', heq, hr₁', hn₁'⟩ := red_aff_pi_norm hr₁ hn₁
      cases heq
      have ⟨a, τ_eq⟩ := red_eta_pi_norm hr₂ hn₂
      cases τ_eq
      exact .fn
  | bot | top | sort => exact NfType.sort
  | tintro => exact .top
  | coup _ _ hr =>
    match hr with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      match hr₁.cases_head with
      | .inl h =>
        cases h
        match hr₂.cases_head with
        | .inl h =>
          cases h
          exact .sort
        | .inr ⟨C, h₁, h₂⟩ => cases h₁
      | .inr ⟨C, h₁, h₂⟩ => cases h₁
  | mk h_t_x _ _ _ _ h =>
    rename_i x α y τ₂ _ _ _ _ _ _ _ _ _
    have ⟨β', τ_eq⟩ := h.coup
    cases τ_eq
    exact .coup
  | app h_t_f hr_f h_t_x hr_cod =>
    have h_nf_f := h_t_f.is_nf
    have h_nf_x := h_t_x.is_nf
    cases h_nf_f with
    | fn =>
      
      sorry-/

/-theorem refl_canon (ht : Judge e (DCC (=(f_α) env x x))) : Reduces e (DCC (refl(f_α) env x)) := by
  cases ht with
  | app _ _ _ hr =>
    
    sorry-/

inductive IsComb : Expr → Type
  | refl  : IsComb (DCC refl(f_α))
  | eql   : IsComb (DCC Eql(f_α))
  | id    : IsComb (DCC Id(α))
  | comp  : IsComb (DCC (f ∘ g))
  | comp' : IsComb (DCC (f ∘' g))
  | fstc  : IsComb (DCC Fstc(β))
  | sndc  : IsComb (DCC Fstc(β))
  | sigma : IsComb (DCC Σ(f_α, f_β))
  | quot  : IsComb (DCC `(β, x))
  | pair  : IsComb (DCC ⟨f, g⟩)
  | curr  : IsComb (DCC Λ(α, β, x))
  | pi    : IsComb (DCC (Π(f_α, f_β)))

/-
An expression that reduces to an equality.
This only includes equalities that can be introduced by
type formers.
-/
inductive EqlTerm : Expr → Prop
  

/-
A function that, when applied a single argument,
yields some =(f_α) env x y

the output type reduces to =(f_α) env x x
-/
inductive EqlFn : Expr → Prop
  | eql  : EqlFn (DCC (Eql(f_α) env))
  | quot : Reduces x (DCC (
    EqlFn (DCC `(

/-
def Judge.is_nf (ht : Judge e τ) : NfType τ := by
  cases ht with
  | eql _ hred | comp' _ _ _ _ _ hred | comp id _ _ hred | id _ hred | eq _ hred =>
    match hred with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      have ⟨env', heq, hr₁', hn₁'⟩ := red_aff_pi_norm hr₁ hn₁
      cases heq
      have ⟨a, τ_eq⟩ := red_eta_pi_norm hr₂ hn₂
      cases τ_eq
      exact .fn

def Judge.is_nf (ht : Judge e τ) : NfType τ := by
  cases ht with
  | eql _ hred | comp' _ _ _ _ _ hred | comp id _ _ hred | id _ hred | eq _ hred =>
    match hred with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      have ⟨env', heq, hr₁', hn₁'⟩ := red_aff_pi_norm hr₁ hn₁
      cases heq
      have ⟨a, τ_eq⟩ := red_eta_pi_norm hr₂ hn₂
      cases τ_eq
      exact .fn-/
  

/-
If it type-checks, it's either:
- the same equality
- a different equality, rejecting argument,
  but one that was ultimately created with refl
-/

/-
Type normal forms:

- Sort
- =(f_α) env x (y? should leave y or force x?)
- (Π(f_α, f_β) env)
- ⊤
- Coup(f_β)
- Σ(f_α, f_β) env

What can reduce to =(f_α) env x y?

Id(_) (=(f_α) env x y)

Fstc(_) (⟦_⟧((=(f_α) env x y), ...))

What is well-typed at =(f_α) env x y?

  - an app. that's it.

    What kind of app?

    - an app with LHS type:
    Π(f_α, 

How does this help us?

- =(f_α) is only a valid type under an app.
  - it is only valid under something that reduces to refl

Theorem: the only combinator that duplicates its spine is Eql
-/

/-theorem elim_eq (ht : Judge e (DCC (=(f_α) env x y))) : x = y := by
  have h := ht.norm_eta
  induction e with
  | refl =>
    cases ht with
    | refl _ hr =>
      match hr with
      | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
        have ⟨env', heq, hrt⟩ := red_aff_pi' hr₁
        cases heq
        exact (no_red_pi_eta_trans hr₂).elim
  | app =>
    cases ht with
    | app _ _ _ hr =>
      match hr with
      | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
        cases hr₂ with
        | refl =>
          
          sorry
        | tail hrt h =>
          have h := only_eql_reduces_eq h
          cases h; cases h; rfl

theorem elim_eq (ht : Judge e (DCC (=(f_α) env x y))) : x = y := by
  have h := ht.norm_eta
  cases ht with
  | eql _ h
  | sigma _ _ h
  | pair _ _ _ _ _ _ h
  | sndc _ _ h | fstc _ _ h
  | quot _ _ h | pi _ _ h | curr _ _ _ _ _ h | comp _ _ _ h
  | comp' _ _ _ _ _ h | id _ h | refl _ h | eq _ h =>
    match h with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      cases hr₂ with
      | refl => exact (no_red_pi_aff_trans hr₁).elim
      | tail a b => exact eq_norm_refl b hn₂
  | mk _ _ _ _ _ h =>
    match h with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      cases hr₂ with
      | refl =>
        exact (no_red_coup_aff_trans hr₁).elim
      | tail a b =>
        exact eq_norm_refl b hn₂
  | coup _ _ h =>
    match h with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      unfold Coup.type at *
      match hr₁.cases_head with
      | .inl a =>
        simp_all
        match hr₂.cases_head with
        | .inl a => simp_all
        | .inr ⟨_, h, _⟩ => cases a ▸ h
  | app h_t_f h_r_α h_t_x h =>
    have hn_a := h_t_f.norm_eta
    have hn_b := h_t_x.norm_eta
    match h with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      cases heq : hr₂ with
      | refl =>
        simp_all
        
        sorry
      | tail _ hr => exact eq_norm_refl hr hn₂
      /-cases hr₁.cases_head with
      | inl a =>
        simp_all
        match hr₂.cases_head with
        | .inl a =>
          cases a; cases a
          rename_i h _ _
          exact eq_norm_refl (by sorry) hn₂
        | .inr ⟨_, h, h_red_other⟩ =>
          cases a ▸ h
          cases h_red_other.cases_head with
          | inl h =>
            cases h; rfl
          | inr h =>
            have ⟨c, h₁, h₂⟩ := h
            rename_i h_eta
            have h := h_eta.norm_aff (by assumption)
            cases h₁
      | inr h =>
        have ⟨c, h₁, h₂⟩ := h
        cases h₁ with
        | curr =>
          
          sorry
        | congrFun h =>
          sorry
        | congrArg h =>
          sorry-/

open Reduces in theorem reflect (ht : Judge e (DCC (=(f_α) env x y))) : x = y := by
  cases ht with
  | eq ht hr =>
    have h := hr.complete
    dcc_simp (! !) at h
    rw [reduce_aff_pi] at h
  | refl ht hr =>
    let heq := hr.complete
    sorry
  | _ => sorry-/

/-inductive RedAff.CurrEq : Expr → Expr → Prop
  | mk  : ProjectEq (DCC (f ⟦β⟧(a, b))) (DCC (x = y))
    → CurrEq (DCC (Λ(_α, _β, f) a b)) (DCC (x = y))

theorem Reduced.curr_eq (hr : Relation.TransGen RedAff (DCC (Λ(_α, _β, x) y z)) (DCC (a = b))) : RedAff.CurrEq (DCC (x y z)) (DCC (a = b)) := by
  cases hr with
  | single h => cases h
  | tail h ih =>
    cases ih
    sorry
  /-cases hr using Relation.TransGen.head_induction_on with
  | single h => cases h
  | head h =>
    cases h with
    | curr =>
      
      sorry
    | congrFun h =>
      cases h with
      | congrFun h => cases h
      | congrArg h =>
        
        sorry-/

--theorem RedAff.curr_eq (hr : Relation.

theorem Reduced.curr_eq (hr : Reduced (DCC (x y z)) (DCC (a = b))) : RedAff.CurrEq (DCC (x y z)) (DCC (a = b)) := by
  match hr with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    cases hr₁ using Relation.TransGen.head_induction_on with
    | single h =>
      cases h with
      | curr =>
        cases hr₂ with
        | tail ih hr =>
          -- a = b. what? can we use this?
          have ⟨f_α, env, heq₁, heq₂⟩ := hr.eq_eql
          cases heq₁; cases heq₂
          
          sorry
        match hr₂.cases_head with
        | .inl h => cases h
        | .inr ⟨_, hr₁, hn₁⟩ =>
          
          
          have h := 
          sorry
        --have h := 
        --sorry
    | head h =>
      sorry-/

--open Reduces in theorem Judge.eq_fn (ht : Judge e (DCC (x = y)))
-- ((f_α.pi (α.curr β f_β.fstc)).app (x.eq y))

--theorem Reduced.mk_args_is_congr (hr : Reduced (DCC (x y z)) (DCC (x y z))

/-theorem Reduced.is_norm_aff_arg (h : Reduced A (DCC (f x))) : IsNorm RedAff x := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    have h := h.norm_eta
    
  sorry-/

open Reduces in theorem Judge.refl_eq (ht : Judge e (DCC (Π(f_α, f_β) (x = y)))) : ∃ f_env env, Reduces e (DCC (refl(f_env) env x)) := by
  induction e generalizing f_α f_β x y with
  | app =>
    cases ht with
    | app h_t_f _ _ h_red_τ =>
      cases h_t_f with
      | app =>
        rename_i ih h
        
        have h := ih (.app (by assumption) (by assumption) (by assumption) (by sorry))
        match h_r_τ with
        | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
          
          sorry

-- or try just x = y
open Reduces in theorem Judge.refl_eq (ht : Judge e (DCC (Π(f_α, Λ(α, β, Fstc(f_β))) (x = y)))) : ∃ f_env env, Reduces e (DCC (refl(f_env) env x)) := by
  cases ht with
  | refl _ =>
    
    sorry
  | app h_t_f h_r_α h_t_x h_r_τ =>
    match h_r_τ with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      
      sorry

open Reduces in theorem Judge.elim_eq (ht : Judge e (DCC (x = y))) : x = y := by
  cases ht with
  | refl h_t_f h_r_τ =>
    have ⟨_, _, heq⟩ := h_r_τ.pi_shape
    cases heq
  | app h_t_f h_r_α h_t_x h_r_τ =>
    match h_r_τ with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      match hr₂.cases_head with
      | .inl h =>
        cases h
        cases hr₁ with
        | single h =>
          have h := h.red_eq
          cases h with
          | proj h => cases h
        | tail ih h =>
          have h := h.red_eq
          cases h with
          | proj h =>
            cases h with
            | fstc =>
              cases h with
              | fstc =>
                cases ih with
                | single h =>
                  cases h with
                  | curr =>
                    cases h_t_f with
                    | refl =>
                      
                      sorry
                    | app =>
                      
                      sorry
                /-cases ih using Relation.TransGen.head_induction_on with
                | single h =>
                  sorry
                | head h =>
                  sorry-/
            | sndc =>
              sorry
            | quot =>
              sorry
          | id =>
            sorry
          | quot =>
            sorry
      | .inr h =>
        sorry

end Expr

/-
Need full reducer

reduce A = B

We need IsNorm for this.

but for this we need a proof of reduce A = B.
-/
