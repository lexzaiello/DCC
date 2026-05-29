import Dcc.Judge
import Dcc.Relation
import Dcc.Aff.Red

namespace Expr

inductive ProjectCurr : Expr → Expr → Prop
  | fstc : ProjectCurr (DCC (Fstc(f_β) ⟦β⟧(x, b))) x
  | sndc : ProjectCurr (DCC (Sndc(f_β) ⟦β⟧(a, x))) x
  | quot : ProjectCurr (DCC (`(β', x) y))  x

inductive Red' : Expr → Expr → Prop
  | quot     : Red' (DCC (`(β, x) y)) x
  | id       : Red' (DCC (Id(α) x)) x
  | project  : ProjectCurr (DCC (f ⟦β⟧(a, b))) x
    → Red' (DCC (f ⟦β⟧(a, b))) x
  | comp     : Red' (DCC ((x ∘ y) z)) (DCC (x (y z)))
  | comp'    : Red' (DCC ((x ∘' y) z)) (DCC (x (y z)))
  | curr     : Red' (DCC ((Λ(α, β, x) y z))) (DCC (x ⟦β⟧(y, z)))
  | congrFun : RedAff f e → Red' (DCC (f x)) (DCC (e x))
  | congrArg : RedAff x arg → Red' (DCC (f x)) (DCC (f arg))

namespace RedAff

theorem pi (h : RedAff (DCC (Π(f_α, f_β) env)) B) : ∃ env', B = (DCC (Π(f_α, f_β) env')) := by
  cases h with
  | congrFun h => cases h
  | congrArg h =>
    rename_i x'
    exact ⟨x', rfl⟩

theorem no_red_pi_aff (h_r : RedAff (DCC (Π(f_α, f_β) env)) (DCC x = y)) : False := by
  cases h_r

def project_eq (hr : RedAff (DCC (f ⟦β⟧(a, b))) (DCC x = y)) : ProjectCurr (DCC (f ⟦β⟧(a, b))) (DCC x = y) := by
  cases hr with
  | quot => exact .quot
  | sndc => exact .sndc
  | fstc => exact .fstc

/-
An expression that reduces to an equality.
-/
inductive RedEq : Expr → Expr → Prop
  | proj : ProjectCurr A (DCC (x = y)) → RedEq A (DCC (x = y))
  | id   : RedEq (DCC (Id(α) (x = y))) (DCC (x = y))
  | quot : RedEq (DCC (`(α, (x = y)) z)) (DCC (x = y))

def eq (hr : RedAff A (DCC (x = y))) : RedEq A (DCC (x = y)) := by
  cases hr with
  | id => exact .id
  | fstc => exact .proj .fstc
  | sndc => exact .proj .sndc
  | quot => exact .quot

def eql (hr : RedAff A (DCC (Eql(f_β) env x))) : Red' A (DCC (Eql(f_β) env x)) := by
  cases hr with
  | quot =>
    exact .quot
  | id => exact .id
  | fstc => exact .project .fstc
  | sndc => exact .project .sndc
  | comp => exact .comp
  | comp' => exact .comp'
  | curr => exact .curr
  | congrFun h => exact .congrFun h
  | congrArg h => exact .congrArg h

end RedAff

namespace RedEta

theorem eq' (h : RedEta A (DCC (x = y))) : ∃ f_α env, A = (DCC (Eql(f_α) env x)) := by
  cases h with
  | eql => exact ⟨_, _, rfl⟩

theorem eq_eql (h_step : RedEta A (DCC (x = y))) : ∃ f_α env, x = y ∧ A = (DCC (Eql(f_α) env x)) := by
  cases h_step with
  | eql => exact ⟨_, _, rfl, rfl⟩

theorem eq_norm_refl (h_step : RedEta A (DCC (x = y))) (h : IsNorm RedEta (DCC (x = y))) : x = y := by
  cases h_step with
  | eql => rfl

theorem no_coup (h : RedEta (DCC Coup(β)) B) : False := by
  cases h

theorem no_pi_eq (h_r : RedEta (DCC (Π(f_α, f_β) env)) (DCC x = y)) : False := by
  cases h_r

inductive RedEq : Expr → Expr → Prop
  | eql : RedEq (DCC (Eql(f_α) env x)) (DCC x = x)

def eq (hr : RedEta A (DCC (x = y))) : RedEta.RedEq A (DCC (x = y)) := by
  cases hr with
  | eql => exact .eql

end RedEta

def head (e : Expr) : Expr :=
  match e with
  | .app f _x => f.head
  | e => e

namespace RedAffReflTrans

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
def eq (hr : RedAffReflTrans A (DCC (x = y))) : (∃ B,
  RedAffReflTrans A B ∧ RedAff B (DCC (x = y)) ∧ RedEq B (DCC (x = y))) ∨ (A = (DCC (x = y))) := by
  cases hr with
  | refl => exact .inr rfl
  | tail ih h => exact .inl ⟨_, ih, by assumption, h.eq⟩

end RedAffReflTrans

namespace RedEtaReflTrans

theorem pi_norm
  (h : RedEtaReflTrans (DCC (Π(f_α, f_β) env)) B)
  (hn : IsNorm RedEta B) :
    ∃ f_β', (B = (DCC (Π(f_α, f_β') env)) ∧ RedEtaReflTrans f_β f_β' ∧ IsNorm RedEta f_β') := by
  match h.cases_head with
  | .inl h => exact ⟨_, h.symm, .refl, by
    cases h
    intro ⟨_, h⟩
    exact hn ⟨_, .pi (reduce_sound rfl) (reduce_norm rfl) (.pi' h)⟩⟩
  | .inr ⟨c, h₁, h₂⟩ =>
    cases h₁ with
    | pi _ _ h =>
      cases h with
      | pi' hr =>
        rename_i β'
        have h_dec : β'.size < f_β.size := by
          exact RedEta.instRedRel.decreasing hr
        have ⟨f_β', heq, h_r_β', h_n_β'⟩ := pi_norm h₂ hn
        exact ⟨_, heq, .trans (.single hr) h_r_β', h_n_β'⟩
termination_by f_β.size

theorem no_coup_eq (h_r : RedEtaReflTrans (DCC Coup(β)) (DCC x = y)) : False := by
  cases h_r.cases_head with
  | inl h => simp_all
  | inr h =>
    have ⟨C, h₁, h₂⟩ := h
    cases h₁

theorem coup (h : RedEtaReflTrans (DCC Coup(β)) B) : (DCC Coup(β)) = B := by
  match h.cases_head with
  | .inl h => exact h
  | .inr ⟨C, h₁, h₂⟩ => cases h₁

end RedEtaReflTrans

namespace RedAffTrans

theorem pi_norm (hr : RedAffTrans (DCC (Π(f_α, f_β) env)) τ') (hn : IsNorm RedAff τ') : ∃ env',
  RedAffTrans env env' ∧ IsNorm RedAff env' ∧ τ' = (DCC (Π(f_α, f_β) env')) := by
  cases hr using Relation.TransGen.head_induction_on with
  | single h =>
    have ⟨env', heq⟩ := h.pi
    cases heq
    exact ⟨env', by
      cases h with
      | congrFun h => cases h
      | congrArg h => exact (.single h), hn.congrArg, rfl⟩
  | head h ih =>
    have ⟨env', heq⟩ := h.pi
    cases heq
    cases h with
    | congrFun h => cases h
    | congrArg h =>
      have h_dec := RedAff.instRedRel.decreasing h
      have ⟨env'', h_env', hn_env', heq'⟩ := RedAffTrans.pi_norm ih hn
      exact ⟨_, .trans (.single h) h_env', hn_env', heq'⟩
termination_by env.size

end RedAffTrans

namespace RedEtaTrans

def eq (hr : RedEtaTrans A (DCC (x = y))) :
  (∃ f_α env, A = (DCC (Eql(f_α) env x)) ∧ x = y) ∨ A = (DCC (x = y)) := by
  cases hr using Relation.TransGen.head_induction_on with
  | single h =>
    cases h
    exact .inl ⟨_, _, rfl, rfl⟩
  | head hr ih =>
    have h_dec := RedEta.instRedRel.decreasing hr
    have h := eq ih
    match h with
    | .inl ⟨f_α, env, heq₁, heq₂⟩ =>
      cases heq₁ ▸ hr with
      | pi =>
        have ⟨_, h, h_r_β, h_n_β⟩ := RedEtaReflTrans.pi_norm
          (.trans (.single hr) (.single (heq₁.symm ▸ RedEta.eql)))
          (fun ⟨_, h⟩ => by cases h)
        cases h
    | .inr h =>
      cases h
      cases hr with
      | eql =>
        exact .inl ⟨_, _, rfl, rfl⟩
termination_by A.size

end RedEtaTrans

namespace RedEtaReflTrans

def eq (hr : RedEtaReflTrans A (DCC (x = y))) :
  (∃ f_α env, A = (DCC (Eql(f_α) env x)) ∧ x = y) ∨ A = (DCC (x = y)) := by
  unfold RedEtaReflTrans at hr
  rw [← Relation.reflGen_transGen] at hr
  match heq : hr with
  | .refl => exact .inr rfl
  | .single hr =>
    rename_i heq'
    change RedEtaTrans _ _ at hr
    cases heq'.symm
    exact hr.eq

end RedEtaReflTrans

namespace Reduces

theorem pi_shape (h : Reduces (DCC (Π(f_α, f_β) env)) τ) : ∃ f_β' env', τ = (DCC (Π(f_α, f_β') env')) := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    have ⟨env', heq, hrt⟩ := hr₁.pi_norm hn₁
    cases heq
    have ⟨_, heq, _, _⟩ := hr₂.pi_norm hn₂
    exact ⟨_, _, heq⟩

abbrev red_aff (e : Expr) := (reduce RedAff e).fst
abbrev red_eta (e : Expr) := (reduce RedEta e).fst

/-
if r A B, then reduce A = reduce B

Red A B

need some way to slot RedAff back into reduce
-/

theorem pi (h : Reduces (DCC (Π(f_α, f_β) env)) τ) : ∃ f_β' env',
  RedEtaReflTrans f_β f_β' ∧ IsNorm RedEta f_β'
    ∧ RedAffReflTrans env env' ∧ IsNorm RedAff env'
    ∧ τ = (DCC (Π(f_α, f_β') env')) := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    have ⟨env', heq, hrt_env, h_norm_env'⟩ := hr₁.pi_norm hn₁
    have ⟨f_β', heq', h_r_f_β, h_n_f_β⟩ := (heq ▸ hr₂).pi_norm hn₂
    cases heq
    cases heq'
    refine ⟨f_β', env', ?_⟩
    exact ⟨h_r_f_β, h_n_f_β, hrt_env, h_norm_env', rfl⟩


end Reduces

namespace Reduced

theorem pi (h : Reduced (DCC (Π(f_α, f_β) env)) τ) : ∃ f_β' env',
  RedEtaReflTrans f_β f_β' ∧ IsNorm RedEta f_β'
    ∧ RedAffTrans env env' ∧ IsNorm RedAff env'
    ∧ τ = (DCC (Π(f_α, f_β') env')) := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    have ⟨env', hrt_env, h_norm_env', heq⟩ := hr₁.pi_norm hn₁
    have ⟨f_β', heq', h_r_f_β, h_n_f_β⟩ := (heq ▸ hr₂).pi_norm hn₂
    cases heq
    cases heq'
    refine ⟨f_β', env', ?_⟩
    refine ⟨h_r_f_β, h_n_f_β, hrt_env, h_norm_env', rfl⟩

end Reduced

namespace Reduces

theorem elim_norm (h : Reduces A B) (hn : IsNorm RedAff A) : RedEtaReflTrans A B := by
  match h with
  | ⟨ha, hb, hc, hd⟩ =>
    match ha.cases_head with
    | .inl h => cases h; assumption
    | .inr ⟨_, h₁, h₂⟩ => exact (hn ⟨_, h₁⟩).elim

theorem sort (he : Reduces (DCC Sort o) B) : B = (DCC Sort o) := by
  match he with
  | ⟨ha, hb, hc, hd⟩ =>
    match ha.cases_head with
    | .inl h =>
      cases h
      match hc.cases_head with
      | .inl h =>
        exact h.symm
      | .inr ⟨_, h₁, h₂⟩ => cases h₁
    | .inr ⟨_, h₁, h₂⟩ => cases h₁

theorem congrFun (h : RedAff f f') (he : Reduces (DCC (f x)) B) : Reduces (DCC (f' x)) B := by
  match he with
  | ⟨ha, hb, hc, hd⟩ =>
    have h₂ : (DCC (f x)).RedAffReflTrans (DCC (f' x)) := .single (.congrFun h)
    have ⟨D, h₁, h₂⟩ := RedAff.instRedRel.globally_confluent.conf ha h₂
    have h := hb.unique_refl h₁
    cases h
    exact ⟨h₂, hb, hc, hd⟩

theorem id (h : Reduces (DCC (Id(α) x)) B) : Reduces x B := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    match hr₁.cases_head with
    | .inl h =>
      cases h
      exact (hn₁ ⟨_, .id⟩).elim
    | .inr ⟨_, h₁, h₂⟩ =>
      cases h₁ with
      | id => exact ⟨h₂, hn₁, hr₂, hn₂⟩
      | congrFun h => cases h
      | congrArg hr =>
        have h_dec := RedAff.instRedRel.decreasing hr
        have h := id ⟨h₂, hn₁, hr₂, hn₂⟩
        match h with
        | ⟨ha, hb, hc, hd⟩ =>
          exact ⟨.trans (.single hr) ha, hb, hc, hd⟩
termination_by x.size

theorem curr (h : Reduces (DCC (Λ(α, β, x) y z)) B) : Reduces (DCC (x ⟦β⟧(y, z))) B := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    match hr₁.cases_head with
    | .inl h =>
      cases h
      exact (hn₁ ⟨_, .curr⟩).elim
    | .inr ⟨_, h₁, h₂⟩ =>
      cases h₁ with
      | curr => exact ⟨h₂, hn₁, hr₂, hn₂⟩
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg hr =>
          have h_dec := RedAff.instRedRel.decreasing hr
          have h := curr ⟨h₂, hn₁, hr₂, hn₂⟩
          match h with
          | ⟨ha, hb, hc, hd⟩ =>
            exact ⟨.trans (.single (.congrArg (.sigl hr))) ha, hb, hc, hd⟩
      | congrArg hr =>
        have h_dec := RedAff.instRedRel.decreasing hr
        have h := curr ⟨h₂, hn₁, hr₂, hn₂⟩
        match h with
        | ⟨ha, hb, hc, hd⟩ =>
          exact ⟨.trans (.single (.congrArg (.sigr hr))) ha, hb, hc, hd⟩
termination_by (y.size + z.size)

theorem quot₁ (h : Reduces (DCC (`(α, x') x)) B) : Reduces x' B := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    match hr₁.cases_head with
    | .inl h =>
      cases h
      exact (hn₁ ⟨_, .quot⟩).elim
    | .inr ⟨_, h₁, h₂⟩ =>
      cases h₁ with
      | quot => exact ⟨h₂, hn₁, hr₂, hn₂⟩
      | congrFun h => cases h
      | congrArg hr =>
        have h_dec := RedAff.instRedRel.decreasing hr
        exact quot₁ ⟨h₂, hn₁, hr₂, hn₂⟩
termination_by x.size

theorem head_trans' (h : Reduces B C) (hr : RedAff A B) : Reduces A C := by
  match h with
  | ⟨ha, hb, hc, hd⟩ =>
    exact ⟨.trans (.single hr) ha, hb, hc, hd⟩

theorem head_trans (h : Reduces A C) (hr : RedAff A B) : Reduces B C := by
  match h with
  | ⟨ha, hb, hc, hd⟩ =>
    have h₂ : A.RedAffReflTrans B := .single hr
    have ⟨D, h₁, h₂⟩ := RedAff.instRedRel.globally_confluent.conf ha h₂
    have h := hb.unique_refl h₁
    cases h
    exact ⟨h₂, hb, hc, hd⟩

-- might need to strengthen this
theorem eql (h : Reduces (DCC (Eql(f_α) env x)) B) : ∃ x', (B = (DCC (x' = x'))) := by
  match h with
  | ⟨ha, hb, hc, hd⟩ =>
    match ha.cases_head with
    | .inl h =>
      cases h
      match hc.cases_head with
      | .inl h =>
        cases h
        exact (hd ⟨_, .eql⟩).elim
      | .inr ⟨_, h₁, h₂⟩ =>
        cases h₁ with
        | eql =>
          match h₂.cases_head with
          | .inl h =>
            cases h; exact ⟨_, rfl⟩
          | .inr ⟨_, h₁, h₂⟩ => cases h₁
    | .inr ⟨_, h₁, h₂⟩ =>
      cases h₁ with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h =>
          rename_i x'
          have h_dec := RedAff.instRedRel.decreasing h
          have h_dec' : (DCC (Eql(f_α) x' x)).size < (DCC (Eql(f_α) env x)).size := by
            grind
          exact eql ⟨h₂, hb, hc, hd⟩
      | congrArg h =>
        rename_i x'
        have h_dec := RedAff.instRedRel.decreasing h
        have h_dec' : (DCC (Eql(f_α) env x')).size < (DCC (Eql(f_α) env x)).size := by
          grind
        exact eql ⟨h₂, hb, hc, hd⟩
termination_by (DCC (Eql(f_α) env x)).size

theorem quot (h : Reduces (DCC (`(α, x') x y)) B) : Reduces (DCC (x' y)) B := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    match hr₁.cases_head with
    | .inl h =>
      cases h
      exact (hn₁ ⟨_, .congrFun .quot⟩).elim
    | .inr ⟨C, h₁, h₂⟩ =>
      cases h₁ with
      | congrFun h =>
        cases h with
        | quot => exact ⟨h₂, hn₁, hr₂, hn₂⟩
        | congrFun h => cases h
        | congrArg h =>
          have h_dec := RedAff.instRedRel.decreasing h
          exact quot ⟨h₂, hn₁, hr₂, hn₂⟩
      | congrArg hr =>
        have h_dec := RedAff.instRedRel.decreasing hr
        have h := quot ⟨h₂, hn₁, hr₂, hn₂⟩
        match h with
        | ⟨ha, hb, hc, hd⟩ =>
          exact ⟨.trans (.single (.congrArg hr)) ha, hb, hc, hd⟩
termination_by (x.size + y.size)

theorem eql_comp_id (h : Reduces (DCC (Eql(f_α) ∘' Id(α₂))) B) : B = (DCC (Eql(f_α) ∘' Id(α₂))) := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    match hr₁.cases_head with
    | .inl h =>
      cases h
      match hr₂.cases_head with
      | .inl h => cases h; rfl
      | .inr ⟨_, h₁, h₂⟩ => cases h₁
    | .inr ⟨_, h₁, h₂⟩ => cases h₁

end Reduces

namespace RedEtaReflTrans

theorem pi (h : RedEtaReflTrans (DCC (Π(f_α, f_β))) B) : ∃ f_β', (B = (DCC Π(f_α, f_β')) ∧ RedEtaReflTrans f_β f_β') := by
  cases h.cases_head with
  | inl h =>
    cases h
    exact ⟨_, rfl, .refl⟩
  | inr h =>
    have ⟨C, h₁, h₂⟩ := h
    cases h₁ with
    | pi' h =>
      have h_dec := RedEta.instRedRel.decreasing h
      have ⟨x', hrt, heq⟩ := pi h₂
      exact ⟨_, hrt, .trans (.single h) heq⟩
termination_by f_β.size

theorem quot (h : RedEtaReflTrans (DCC `(α, x)) B) : B = (DCC `(α, x)) := by
  match h.cases_head with
  | .inl h => cases h; rfl
  | .inr ⟨_, h₁, h₂⟩ => cases h₁

end RedEtaReflTrans

namespace RedAffReflTrans

theorem elim_norm (hn : IsNorm RedAff A) (h : RedAffReflTrans A B) : A = B :=
  match h.cases_head with
  | .inl h => h
  | .inr ⟨_, hr, _⟩ => (hn ⟨_, hr⟩).elim

end RedAffReflTrans

namespace RedEtaReflTrans

theorem curr (h : RedEtaReflTrans (DCC Λ(α, β, x)) B) : B = (DCC Λ(α, β, x)) := by
  match h.cases_head with
  | .inl h => cases h; rfl
  | .inr ⟨_, h₁, h₂⟩ => cases h₁

theorem curr_quot (h : RedEtaReflTrans (DCC (Λ(α, _a, `(_b, x)) y)) B)
  : (RedEtaReflTrans (DCC `(y, x)) B ∨ B = (DCC (Λ(α, _a, `(_b, x)) y))) := by
  match h.cases_head with
  | .inl h =>
    exact .inr h.symm
  | .inr ⟨_, h₁, h₂⟩ =>
    cases h₁ with
    | curr_quot =>
      exact .inl h₂

theorem aff_norm (h : RedEtaReflTrans B C) (head_r : RedEta A B) (hn_head : IsNorm RedAff A) : IsNorm RedAff B := by
  induction h with
  | refl =>
    exact head_r.norm_aff (by assumption)
  | tail ih h =>
    have h := h.norm_aff
    simp_all

theorem aff_norm' (h : RedEtaReflTrans B C) (head_r : RedEta A B) (hn_head : IsNorm RedAff A) : IsNorm RedAff C := by
  induction h with
  | refl =>
    exact head_r.norm_aff (by assumption)
  | tail ih h =>
    have h := h.norm_aff
    simp_all

theorem elim_norm (hn : IsNorm RedEta A) (h : RedEtaReflTrans A B) : A = B :=
  match h.cases_head with
  | .inl h => h
  | .inr ⟨_, hr, _⟩ => (hn ⟨_, hr⟩).elim

theorem arrow (h : RedEtaReflTrans (DCC (α : Sort m) → β) B) : ∃ β', B = (DCC ((α : Sort m) → β')) ∧ RedEtaReflTrans β β' := by
  induction β using RedEta.instRedRel.wellFounded.induction with
  | h β ih =>
    match h.cases_head with
    | .inl h =>
      cases h
      exact ⟨_, rfl, .refl⟩
    | .inr ⟨_, h₁, h₂⟩ =>
      cases h₁ with
      | pi =>
        rename_i hr _
        cases hr with
        | pi' h => cases h

end RedEtaReflTrans

namespace RedAffReflTrans

theorem arrow (h : RedAffReflTrans (DCC (α : Sort m) → β) B) : ∃ α', B = (DCC ((α' : Sort m) → β)) ∧ RedAffReflTrans α α' := by
  induction α using RedAff.instRedRel.wellFounded.induction with
  | h α ih =>
    match h.cases_head with
    | .inl h =>
      cases h
      exact ⟨_, rfl, .refl⟩
    | .inr ⟨_, h₁, h₂⟩ =>
      cases h₁ with
      | congrFun h => cases h
      | congrArg h =>
        have ⟨_, heq, hrt⟩ := ih _ h h₂
        exact ⟨_, heq, .trans (.single h) hrt⟩

theorem comp (h : RedAffReflTrans (DCC ((f ∘ g) x)) B) (hn : IsNorm RedAff B) : RedAffReflTrans (DCC (f (g x))) B := by
  match h.cases_head with
  | .inl h =>
    cases h
    exact (hn ⟨_, .comp⟩).elim
  | .inr ⟨_, h₁, h₂⟩ =>
    cases h₁ with
    | comp =>
      assumption
    | congrFun h => cases h
    | congrArg hr =>
      have h_dec := RedAff.instRedRel.decreasing hr
      have h := comp h₂ (by assumption)
      exact .trans (.single (.congrArg (.congrArg hr))) h
termination_by x.size

theorem comp' (h : RedAffReflTrans (DCC ((f ∘' g) x)) B) (hn : IsNorm RedAff B) : RedAffReflTrans (DCC (f (g x))) B := by
  match h.cases_head with
  | .inl h =>
    cases h
    exact (hn ⟨_, .comp'⟩).elim
  | .inr ⟨_, h₁, h₂⟩ =>
    cases h₁ with
    | comp' =>
      assumption
    | congrFun h => cases h
    | congrArg hr =>
      have h_dec := RedAff.instRedRel.decreasing hr
      have h := comp' h₂ (by assumption)
      exact .trans (.single (.congrArg (.congrArg hr))) h
termination_by x.size

open Congruent in
theorem congr_arg (h : RedAffReflTrans (DCC (f x)) B) (hn : IsNorm RedAff B) (hr : RedAff x x') : RedAffReflTrans (DCC (f x')) B := by
  have h_r := RedAff.instCongruent.congrArg' hr (f := f)
  have ⟨_, h₁, h₂⟩ := RedAff.instRedRel.globally_confluent.conf h (.single h_r)
  cases hn.unique_refl h₁
  assumption

end RedAffReflTrans

namespace Reduces

theorem norm_aff (h : Reduces A B) : IsNorm RedAff B := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    match hr₁.cases_head with
    | .inl h =>
      match hr₂.cases_head with
      | .inl h => simp_all
      | .inr ⟨_, h₁, h₂⟩ =>
        cases h
        change RedEtaReflTrans _ _ at h₂
        have h := h₁.norm_aff (by assumption)
        exact h₂.aff_norm' h₁ (by assumption)
    | .inr ⟨_, h₁, h₂⟩ =>
      have h_dec := RedAff.instRedRel.decreasing h₁
      exact norm_aff ⟨h₂, by assumption, by assumption, by assumption⟩
termination_by A.size

theorem arrow (h : Reduces (DCC (α : Sort m) → β) B) : ∃ α' β', B = (DCC ((α' : Sort m) → β'))
  ∧ RedAffReflTrans α α'
  ∧ RedEtaReflTrans β β' := by
  induction β using RedEta.instRedRel.wellFounded.induction generalizing α m B with
  | h β ih =>
    match h with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      have ⟨α', heq₁, hrt₁⟩ := hr₁.arrow
      cases heq₁
      have ⟨β', heq₂, hrt₂⟩ := hr₂.arrow
      cases heq₂
      exact ⟨_, _, rfl, hrt₁, hrt₂⟩

--theorem conf (h₁ : Reduces A B) (h₂ : Reduces A C)

@[grind ., grind <=, dcc_reduce]
theorem trans (h₁ : Reduces A B) (h₂ : Reduces B C) : B = C := by
  match h₁, h₂ with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩, ⟨hr₃, hn₃, hr₄, hn₄⟩ =>
    have h := h₁.norm_aff
    have h := h₁.norm_eta
    have heq₁ := hr₃.elim_norm (by assumption)
    have heq₂ := hr₄.elim_norm (by cases heq₁; assumption)
    cases heq₁; cases heq₂
    rfl

/-theorem trans (h₁ : Reduces A B) (h₂ : Reduces B C) : B = C := by
  match h₁, h₂ with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩, ⟨hr₃, hn₃, hr₄, hn₄⟩ =>
    have h := h₁.norm_eta
    have h := hr₄.elim_norm (by sorry)
    sorry

theorem trans (h₁ : Reduces A B) (h₂ : Reduces B C) : B = C := by
  match h₁, h₂ with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩, ⟨hr₃, hn₃, hr₄, hn₄⟩ =>
    induction hr₄ with
    | refl =>
      induction hr₂ with
      | refl =>
        
        sorry
    | tail ih h =>
      sorry

theorem trans (h₁ : Reduces A B) (h₂ : Reduces B C) : B = C := by
  match h₁, h₂ with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩, ⟨hr₃, hn₃, hr₄, hn₄⟩ =>
    match hr₁.cases_head with
    | .inl h =>
      cases h
      match hr₂.cases_head with
      | .inl h =>
        cases h
        match hr₃.cases_head with
        | .inl h =>
          cases h
          match hr₄.cases_head with
          | .inl h =>
            cases h; rfl
          | .inr ⟨_, h₁, h₂⟩ =>
            change RedEtaReflTrans _ _ at h₂
            exact hr₄.elim_norm hn₂
      | .inr ⟨_, h₁, h₂⟩ =>
        have h := h₁.norm_aff (by assumption)
        change RedEtaReflTrans _ _ at h₂
        
        have h := hr₃.elim_norm (by sorry)
        sorry
    | .inr h =>
      sorry-/

/-theorem reduce_reduce (h₁ : Reduces A B) (h₂ : Reduces B C) : B = C := by
  match h₁, h₂ with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩, ⟨hr₃, hn₃, hr₄, hn₄⟩ =>
    match hr₁.cases_head with
    | .inl h =>
      cases h
      match hr₂.cases_head with
      | .inl h =>
        cases h
        match hr₃.cases_head with
        | .inl h =>
          cases h
          match hr₄.cases_head with
          | .inl h =>
            cases h; rfl
          | .inr ⟨_, h₁, h₂⟩ =>
            change RedEtaReflTrans _ _ at h₂
            exact hr₄.elim_norm hn₂
      | .inr ⟨_, h₁, h₂⟩ =>
        have h := h₁.norm_aff (by assumption)
        change RedEtaReflTrans _ _ at h₂
        
        have h := hr₃.elim_norm (by sorry)
        sorry
    | .inr h =>
      sorry-/

theorem push_head (h : Reduces A B) (hr : RedAffReflTrans A₀ A) : Reduces A₀ B :=
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    ⟨hr.trans hr₁, hn₁, hr₂, hn₂⟩

/-
Better Pi lemma?

reduces Π(f_α, f_β) env B

parameterize it by RedAffReflTrans env
and RedEtaRefltrans f_β

combine with trans to get B equality
-/

theorem cases_head (h : Reduces A B) : RedEtaReflTrans A B ∨ (∃ C D, RedAff A C
  ∧ RedAffReflTrans C D ∧ RedEtaReflTrans D B ∧ IsNorm RedAff D) := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    match hr₁.cases_head with
    | .inl h => cases h; exact .inl (by assumption)
    | .inr ⟨x, h₁, h₂⟩ =>
      exact .inr ⟨_, _, h₁, h₂, by assumption, by assumption⟩

theorem pop_head (h : Reduces A B) : RedEtaReflTrans A B ∨ (∃ C, RedAff A C ∧ Reduces C B) := by
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    match hr₁.cases_head with
    | .inl h =>
      cases h
      exact .inl (by assumption)
    | .inr ⟨_, h₁, h₂⟩ =>
      exact .inr ⟨_, h₁, ⟨by assumption, by assumption, by assumption, by assumption⟩⟩

theorem norm_head (h : IsNorm RedAff A) (hr : Reduces A B) : RedEtaReflTrans A B := by
  match hr with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    cases h.unique_refl hr₁
    exact hr₂

/-open Congruent in
theorem congr_fun (hr : Reduces (DCC (f x)) B) (hrf : Reduces f f') : Reduces (DCC (f' x)) B := by
  match hr, hrf with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩, ⟨hr₃, hn₃, hr₄, hn4⟩ =>
    have h := Congruent.reflTrans.congrFun' (r := RedAffReflTrans) (h := hr₃) (f := f) (x := x)
    have ⟨D, h₁, h₂⟩ := RedAff.instRedRel.globally_confluent.conf h hr₁
    have heq := hn₁.unique_refl h₂
    rw [← heq] at h₁
    have h : IsNorm RedAff f' := hrf.norm_aff
    exact ⟨h.trans h₁, by sorry, by sorry, by sorry⟩

open Congruent in
theorem congr_fun (hr : Reduces (DCC (f x)) B) (h : Reduces f f') : Reduces (DCC (f' x)) B := by
  match hr, h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩, ⟨hr₃, hn₃, hr₄, hn4⟩ =>
    
    have hn := h.norm_aff
    have ⟨_, h₁, h₂⟩ := RedAff.instRedRel.globally_confluent.conf hr₁ (congrFun' hr₃)
    cases hn₁.unique_refl h₁
    
    exact ⟨by sorry, by sorry, by assumption, by assumption⟩-/

theorem deterministic (h₁ : Reduces A B) (h₂ : Reduces A C) : B = C := by
  match h₁, h₂ with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩, ⟨hr₃, hn₃, hr₄, hn₄⟩ =>
    cases norm_unique hr₁ hn₁ hr₃ hn₃
    cases norm_unique hr₂ hn₂ hr₄ hn₄
    rfl

/-theorem 

open Congruent in
theorem congr_fun (hr : Reduces (DCC (f x)) B) (h : Reduces f f') : Reduces (DCC (f' x)) B := by
  
  sorry-/

end Reduces

namespace RedEtaReflTrans

theorem mk_pi_β (h : RedEtaReflTrans f_β f_β') (hn_env : IsNorm RedAff env) : RedEtaReflTrans (DCC (Π(f_α, f_β) env)) (DCC (Π(f_α, f_β') env)) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.pi (.refl) (by assumption) (.pi' h)))

open RedAff Congruent in
theorem pi_extract (h_t_f_α : RedEtaReflTrans f_β f_β') (hn₁ : IsNorm RedEta f_β') (h_t_env : RedAffReflTrans env env') (hn₂ : IsNorm RedAff env') : Reduces (DCC (Π(f_α, f_β) env)) (DCC (Π(f_α, f_β') env')) :=
  ⟨congrArg' (hR := RedAff.instCongruent.reflTrans) (by assumption), fun ⟨_, h⟩ => by
    cases h with
    | congrFun h => cases h
    | congrArg h =>
      exact hn₂ ⟨_, h⟩
  , mk_pi_β h_t_f_α hn₂, fun ⟨_, h⟩ => by
    cases h with
    | pi _ _ h_pi => cases h_pi with | pi' =>
      exact (hn₁ ⟨_, by assumption⟩)⟩

end RedEtaReflTrans

end Expr
