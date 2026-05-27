import Dcc.Judge

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
    intro ⟨_, hr⟩
    exact (hn ⟨_, .pi (.pi' hr)⟩).elim⟩
  | .inr ⟨c, h₁, h₂⟩ =>
    cases h₁ with
    | pi h =>
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

theorem no_pi_eq (h_r : RedEtaReflTrans (DCC (Π(f_α, f_β) env)) (DCC x = y)) : False := by
  let f_β₀ := f_β
  cases h_r.cases_head with
  | inl h => simp_all
  | inr h =>
    have ⟨C, h₁, h₂⟩ := h
    cases heq₁ : h₁ with
    | pi h =>
      cases h with
      | pi' h =>
        have h_dec := RedEta.instRedRel.decreasing h
        exact no_pi_eq h₂
termination_by f_β.size

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

theorem quot (h : RedEtaReflTrans (DCC `(α, x)) B) : ∃ x', RedEtaReflTrans x x' ∧ B = (DCC `(α, x')) := by
  cases h.cases_head with
  | inl h => cases h; exact ⟨_, .refl, rfl⟩
  | inr h =>
    have ⟨C, h₁, h₂⟩ := h
    cases h₁ with
    | quot h =>
      have h_dec := RedEta.instRedRel.decreasing h
      have ⟨x', hrt, heq⟩ := quot h₂
      exact ⟨x', .trans (.single h) hrt, heq⟩
termination_by x.size

end RedEtaReflTrans

end Expr
