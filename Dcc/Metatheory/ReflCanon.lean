import Dcc.Ast
import Dcc.Judge
import Dcc.Tactic.Reduce
import Dcc.Metatheory.Congr
import Dcc.Metatheory.Preservation

/-
Want to automate IsNorm, but sounds hard.
-/

namespace Expr

abbrev Arity := ℕ

-- Combinators that can make a step with their well-typed arguments
inductive IsRedComb : Expr → Arity → Type
  -- Eql(f_α) env x -> (x = x)
  | eql   : IsRedComb (DCC Eql(f_α)) 2
  -- Id(α) x
  | id    : IsRedComb (DCC Id(α)) 1
  -- (f ∘ g) x
  | comp  : IsRedComb (DCC (f ∘ g)) 1
  | comp' : IsRedComb (DCC (f ∘' g)) 1
  -- Fstc(..) (x, y) -> x
  | fstc  : IsRedComb (DCC Fstc(β)) 1
  | sndc  : IsRedComb (DCC Sndc(β)) 1
  -- Σ(f_α, f_β) env -> Coup(...)
  | sigma : IsRedComb (DCC Σ(f_α, f_β)) 1
  -- `(β, x) y
  | quot  : IsRedComb (DCC `(β, x)) 1
  -- ⟨f, g⟩ x
  | pair  : IsRedComb (DCC ⟨f, g⟩) 1
  -- Λ(α, β, x) y z
  | curr  : IsRedComb (DCC Λ(α, β, x)) 2

inductive IsRedCombApp : Expr → Arity → Type
  -- Eql(f_α) env x -> (x = x)
  | eql   : IsRedCombApp (DCC Eql(f_α)) 2
  -- Id(α) x
  | id    : IsRedCombApp (DCC Id(α)) 1
  -- (f ∘ g) x
  | comp  : IsRedCombApp (DCC (f ∘ g)) 1
  | comp' : IsRedCombApp (DCC (f ∘' g)) 1
  -- Fstc(..) (x, y) -> x
  | fstc  : IsRedCombApp (DCC Fstc(β)) 1
  | sndc  : IsRedCombApp (DCC Sndc(β)) 1
  -- Σ(f_α, f_β) env -> Coup(...)
  | sigma : IsRedCombApp (DCC Σ(f_α, f_β)) 1
  -- `(β, x) y
  | quot  : IsRedCombApp (DCC `(β, x)) 1
  -- ⟨f, g⟩ x
  | pair  : IsRedCombApp (DCC ⟨f, g⟩) 1
  -- Λ(α, β, x) y z
  | curr  : IsRedCombApp (DCC Λ(α, β, x)) 2
  | app   : IsRedCombApp f (m + 1) → IsRedCombApp (DCC (f x)) m

namespace Reduced

theorem head (hr : Reduced A D) : ∃ B C, RedEtaReflTrans C D ∧ RedAff A B ∧ (B = C ∨ RedAffTrans B C) ∧ IsNorm RedAff C ∧ IsNorm RedEta D := by
  match hr with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    cases hr₁ using Relation.TransGen.head_induction_on with
    | single h => exact ⟨_, _, hr₂, h, .inl rfl, hn₁, hn₂⟩
    | head h ih => exact ⟨_, _, hr₂, h, .inr ih, hn₁, hn₂⟩

/-theorem Reduced.step_comb₁ (h_f : IsRedComb f 1) (h_r : Reduced (DCC (f x))) : ∃ e' e'',
  RedAff (DCC (f x)) e' ∧ RedAffReflTrans -/

end Reduced

/-
A normal form is either:
- a combinator with fewer than its arity arguments applied
  - and all arguments are values

- Π(f_α, f_β)
  - if f_β is a value
- Π(f_α, f_β) env
  - if f_β and env are values
- refl(f_α) env
  - if env is a value
- refl(f_α) env x
  - if env and x are values
- Coup(f_β)
- x = y

- a Sort m
- ⊤
- ⊥
- ∗
-/

inductive Value : Expr → Prop
  | pi₁    : Value f_β → Value (DCC Π(f_α, f_β))
  | pi₂    : Value f_β → Value env → Value (DCC (Π(f_α, f_β) env))
  | refl₁  : Value env → Value (DCC (refl(f_α) env))
  | refl₂  : Value env → Value x → Value (DCC (refl(f_α) env x))
  | coup   : Value (DCC Coup(f_β))
  | eq     : Value (DCC x = y)
  | comb   : IsRedComb c m → Value c
  | app    : IsRedCombApp (DCC (f x)) (m + 1) → Value f → Value x → Value (DCC (f x))
  | top    : Value (DCC ⊤)
  | bot    : Value (DCC ⊥)
  | tintro : Value (DCC ∗)
  | sort   : Value (DCC Sort m)

theorem Value.is_norm_aff (h : Value e) : IsNorm RedAff e := by
  sorry

theorem Value.is_norm_eta (h : Value e) : IsNorm RedEta e := by
  sorry

/-inductive IsComb : Expr → Arity → Type
  -- env x
  | refl  : IsComb (DCC refl(f_α)) 2
  -- Eql(f_α) env x
  | eql   : IsComb (DCC Eql(f_α)) 2
  -- Id(α) x
  | id    : IsComb (DCC Id(α)) 1
  -- (f ∘ g) x
  | comp  : IsComb (DCC (f ∘ g)) 1
  | comp' : IsComb (DCC (f ∘' g)) 1
  -- Fstc(..) (x, y)
  | fstc  : IsComb (DCC Fstc(β)) 1
  | sndc  : IsComb (DCC Sndc(β)) 1
  -- Σ(f_α, f_β) env
  | sigma : IsComb (DCC Σ(f_α, f_β)) 1
  -- `(β, x) y
  | quot  : IsComb (DCC `(β, x)) 1
  -- ⟨f, g⟩ x
  | pair  : IsComb (DCC ⟨f, g⟩) 1
  -- Λ(α, β, x) y z
  | curr  : IsComb (DCC Λ(α, β, x)) 2
  -- Π(f_α, f_β) env x
  | pi    : IsComb (DCC (Π(f_α, f_β)))-/

namespace Judge

/-
Substitution lemma...

adding a 
-/

-- Probably somewhat easy to prove
theorem eq_val_is_refl (ht : Judge e (DCC (x = y)))
  (hv : Value e) : ∃ f_α env, e = (DCC (refl(f_α) env x)) ∧ env.Value ∧ x.Value := by
  induction hv with
  | pi₁ =>
    cases ht with
    | pi h_t_f_α h_t_f_β hr =>
      have h := hr.pi
      simp_all
  | pi₂ =>
    cases ht with
    | app h_t_f h_r_α h_t_x h_r_τ =>
      cases h_t_f with
      | pi h₁ h₂ hr =>
        have ⟨_, _, ha, hb, hc, hd, he⟩ := hr.pi
        cases he
        match ha.cases_head with
        | .inl h =>
          cases h
          
          sorry
        | .inr ⟨_, h₁, h₂⟩ =>
          
          sorry

/-
Progress might be important for this too since we can establish what normal forms are.
If e : (x = y), then either e is a normal form (e.g., refl), or it reduces to (what?)
-/

theorem preservation (ht : Judge A t) (hr : RedAff A B) : Judge B t := by
  sorry

theorem progress (ht : Judge e τ) : Value e ∨ (∃ e', RedAff e e') := by
  sorry

theorem refl_ty_heq (h_t : Judge (DCC (refl(f_α) env x₀)) (DCC x = y)) : x = y := by
  obtain ⟨a, b, c, d, h_t_refl_env, f, g, ⟨hr₁, hn₁, hr₂, hn₂⟩⟩ := h_t.invert rfl
  obtain ⟨i, j, k, l, m, o, p, q⟩ := h_t_refl_env.invert rfl
  cases m with
  | refl h_t_f_α h_r_refl_ty =>
    unfold refl.type at h_r_refl_ty
    obtain ⟨_, _, h₄, h₅, h₆, h₇, h₈⟩ := h_r_refl_ty.pi
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h₈
    have ⟨x', hrt, heq⟩ := h₄.quot
    cases heq
    have hr_env := q.to_reduces.quot
    have ⟨f_β', h_x'_eq, hrtx'⟩ := hrt.pi
    cases h_x'_eq
    have ⟨a, b, c, d, e, f, heq'⟩ := hr_env.pi
    match hrtx'.cases_head with
    | .inl heq'' =>
      cases heq''
      simp_all
      match c.cases_head with
      | .inl heq''' =>
        cases heq'''
        simp_all
        cases hr₁ using Relation.TransGen.head_induction_on with
        | single h =>
          cases h with
          | congrFun h =>
            match hr₂.eq with
            | .inl ⟨_, _, h₁, h₂⟩ => exact h₂
            | .inr h => simp_all
          | congrArg h =>
            have h_dec := RedAff.instRedRel.decreasing h
            have h_t' := h_t.preservation (.congrArg h)
            exact refl_ty_heq h_t'
        | head h ih =>
          cases h with
          | congrFun h =>
            match hr₂.eq with
            | .inl ⟨_, _, h₁, h₂⟩ => exact h₂
            | .inr h =>
              cases h
              cases h with
              | comp =>
                change RedAffTrans _ _ at ih
                cases ih using Relation.TransGen.head_induction_on with
                | single h => cases h
                | head h ih =>
                  cases h with
                  | congrFun h =>
                    cases h with
                    | congrFun h => cases h
                    | congrArg h =>
                      cases h with
                      | id =>
                        cases ih using Relation.TransGen.head_induction_on with
                        | single h => cases h
                        | head h ih =>
                          cases h with
                          | congrFun h =>
                            cases h with
                            | congrFun h => cases h
                            | congrArg h => exact (f ⟨_, h⟩).elim
                          | congrArg h =>
                            have h_dec := RedAff.instRedRel.decreasing h
                            have h_t' := h_t.preservation (.congrArg h)
                            exact refl_ty_heq h_t'
                      | congrFun h => cases h
                      | congrArg h => exact (f ⟨_, h⟩).elim
                  | congrArg h =>
                    have h_dec := RedAff.instRedRel.decreasing h
                    have h_t' := h_t.preservation (.congrArg h)
                    exact refl_ty_heq h_t'
              | congrFun h => cases h
              | congrArg h => exact (f ⟨_, h⟩).elim
          | congrArg h =>
            have h_dec := RedAff.instRedRel.decreasing h
            have h_t' := h_t.preservation (.congrArg h)
            exact refl_ty_heq h_t'
      | .inr ⟨_, h, _⟩ => cases h
    | .inr ⟨_, h, _⟩ => cases h
termination_by x₀.size

/-
induction using Expr.instWellFounded?

Due to progress
-/
theorem eq_is_refl (h_t : Judge e (DCC (x = y))) :
  ∃ f_α env, Reduces e (DCC (refl(f_α) env x)) := by
  induction e using RedAff.instRedRel.wellFounded.induction with
  | h e ih =>
    match h_t.progress with
    | .inl h_val =>
      have ⟨f_α, env, heq⟩ := h_t.eq_val_is_refl h_val
      simp_all
      exact ⟨f_α, env, ⟨.refl, h_val.is_norm_aff, .refl, h_val.is_norm_eta⟩⟩
    | .inr ⟨e', hr⟩ =>
      match ih _ hr (h_t.preservation hr) with
      | ⟨f_α, env, ⟨hr₁, hn₁, hr₂, hn₂⟩⟩ =>
        exact ⟨f_α, env, ⟨.trans (.single hr) hr₁, hn₁, hr₂, hn₂⟩⟩

theorem elim_eq (h : Judge e (DCC (x = y))) : x = y := by
  have ⟨f_α, env, h_r⟩ := eq_is_refl h
  have ht' := h.preservation' h_r
  exact refl_ty_heq ht'

end Judge

end Expr
