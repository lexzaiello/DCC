import Dcc.Ast
import Dcc.Judge
import Dcc.Metatheory.Value
import Dcc.Metatheory.Congr
--import Dcc.Metatheory.Preservation
import Dcc.Metatheory.Judge
--import Dcc.Tactic.Reduce

/-
Want to automate IsNorm, but sounds hard.
-/

namespace Expr

namespace Judge

/-
Substitution lemma...

adding a
-/

/-
Progress might be important for this too since we can establish what normal forms are.
If e : (x = y), then either e is a normal form (e.g., refl), or it reduces to (what?)
-/

theorem Expr.Judge.preservation_id {f_α f_β x_α α x τ : Expr}
  (h_r_α : (f_α.app x_α).Reduces α) (h_t_x : x.Judge α)
  (h_r_τ : ((f_β.app x_α).app x).Reduces τ) (ih₂ : ∀ {B : Expr}, x.RedAff B → B.Judge α) {α_id : Expr}
  (ht : α_id.id.Judge ((f_α.pi f_β).app x_α))
  (ih₁ : ∀ {B : Expr}, α_id.RedAff B → B.Judge ((f_α.pi f_β).app x_α)) :
  x.Judge τ := by
  match ht with
  | .id h_t_α h_r_α h_r_id_ty =>
    simp [id.type] at h_r_id_ty
    have ⟨f_β', env', h_r_β', hn_β', h_r_α, hn, heq⟩ := h_r_id_ty.pi
    simp_all
    have ⟨⟨ha, hb⟩, hc⟩ := heq
    simp_all
    cases ha; cases hb; cases hc
    rename_i hrτ
    match hrτ with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      match hr₁.cases_head with
      | .inl h =>
        cases h
        match hr₂.cases_head with
        | .inl h =>
          cases h with
          | refl => exact (hn₁ ⟨_, .id⟩).elim
        | .inr ⟨_, h₁, h₂⟩ => cases h₁
      | .inr ⟨_, h₁, h₂⟩ =>
        have h := hrτ.id
        cases h₁ with
        | id =>
          match h_r_τ.cases_head with
          | .inl h =>
            cases h
            
            sorry
          | .inr h =>
            sorry
        | congrFun h =>
          sorry
        | congrArg h =>
          sorry
        /-rename_i hrid _
        have h := hrid.id
        have h_x_α_α₁ := h.elim_norm (by assumption)
        cases h₁ with
        | curr =>
          have h := h.elim_norm (by assumption)
          have h := hrτ.curr
          match h with
          | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
            match hr₁.cases_head with
            | .inl h =>
              cases h
              cases h_r_β' with
              | tail ih h =>
                cases h with
                | curr h =>
                  rename_i h_τ₂ _
                  clear hrτ hr₁ h hr_ty
                  match hr₂.cases_head with
                  | .inl h =>
                    cases h
                    sorry
              | refl => exact (hn₁ ⟨_, .quot⟩).elim
            | .inr h =>
              sorry
        | congrFun h =>
          
          sorry
        | congrArg h =>
          sorry-/

theorem preservation (ht : Judge A t) (hr : RedAff A B) : Judge B t := by
  induction ht generalizing B
  any_goals (
    focus
    cases hr
    done)
  case coup ih =>
    cases hr with
    | coup h => exact Judge.coup (ih h) (by assumption) (by assumption)
  case mk ih₁ ih₂ ih₃ =>
    cases hr with
    | sigl h =>
      rename_i βx_red _ _
      exact Judge.mk (ih₁ h) (by assumption) (by assumption)
        (by assumption) (βx_red.head_trans (.congrArg h)) (by assumption)
    | sigr h =>
      rename_i βx_red _ _
      exact Judge.mk (by assumption) (ih₂ h) (by assumption)
        (by assumption) (by assumption) (by assumption)
  case app hr_α ih₁ ih₂ =>
    cases hr with
    | congrFun h =>
      exact Judge.app (ih₁ h) (by assumption) (by assumption) (by assumption) (by assumption)
    | congrArg h =>
      have ha := hr_α.head_trans (.congrArg h)
      exact Judge.app (by assumption) (by assumption) (ih₂ h) (by assumption) (by assumption)
    | quot =>
      rename_i ht
      cases ht with
      | quot h_t_B _ hr_ty =>
        have ⟨α', β', heq, hrt₁, hrt₂⟩ := hr_ty.arrow
        cases heq
        rename_i hr
        have h := hr_α.curr.quot₁
        exact (h_t_B.red_eta_refl_trans (by assumption)).reduces (by assumption)
    | id =>
      rename_i ht
      cases ht with
      | id h_t_α h_r_α' hr_ty =>
        rename_i h_t_x _ _ _
        simp [id.type] at hr_ty
        have ⟨f_β', env', h_r_β', hn_β', h_r_α, hn, heq⟩ := hr_ty.pi
        simp_all
        have ⟨⟨ha, hb⟩, hc⟩ := heq
        simp_all
        rename_i h_r_env' _
        have h := h_r_env'.id
        have h_uniq₁ := h_t_x.unique h
        have h := h_r_β'.curr
        simp_all
        have h := hr_α.curr.quot₁
        have h := h_r_α'.trans h
        simp_all
        have h := h_r_α'.norm_aff.unique_refl h_r_α
        rename_i h_ _ _ heq
        simp_all
        rename_i h_t_x _ h_norm
        have h_env_norm := h_norm.norm_aff
        have h_eq := h_.unique h_norm
        simp_all

theorem preservation_eta (ht : Judge A t) (hr : RedEta A B) : Judge B t := by
  sorry

theorem progress (ht : Judge e τ) : Value e ∨ (∃ e', RedAff e e') := by
  sorry

theorem preservation' (ht : Judge A t) (hr : Reduces A B) : Judge B t := by
  match hr with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    sorry

theorem refl_ty_heq (h_t : Judge (DCC (refl(f_α) env x₀)) (DCC x = y)) : x = y := by
  obtain ⟨a, b, c, d, e, h_t_refl_env, f, g, _, ⟨hr₁, hn₁, hr₂, hn₂⟩⟩ := h_t.invert rfl
  obtain ⟨i, j, k, l, n, m, o, p, r, q⟩ := h_t_refl_env.invert rfl
  cases m with
  | refl h_t_f_α h_r_refl_ty =>
    unfold refl.type at h_r_refl_ty
    obtain ⟨_, _, h₄, h₅, h₆, h₇, h₈⟩ := h_r_refl_ty.pi
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h₈
    have heq := h₄.quot
    cases heq
    have hr_env := q.quot
    --have ⟨f_β', h_x'_eq, hrtx'⟩ := hrt.pi
    --cases h_x'_eq
    have ⟨a, b, c, d, e, f, heq'⟩ := hr_env.pi
    cases heq'
    match c.cases_head with
    | .inl heq''' =>
      cases heq'''
      cases hr₁ using Relation.ReflTransGen.head_induction_on with
      | refl => exact (hn₁ ⟨_, (.congrFun .comp)⟩).elim
      | head h ih =>
        cases h with
        | congrFun h =>
          match hr₂.eq with
          | .inl ⟨_, _, h₁, h₂⟩ => exact h₂
          | .inr h =>
            cases h
            cases h with
            | comp =>
              change RedAffReflTrans _ _ at ih
              cases ih using Relation.ReflTransGen.head_induction_on with
              | head h ih =>
                cases h with
                | congrFun h =>
                  cases h with
                  | congrFun h => cases h
                  | congrArg h =>
                    cases h with
                    | id =>
                      cases ih using Relation.ReflTransGen.head_induction_on with
                      | head h ih =>
                        cases h with
                        | congrFun h =>
                          cases h with
                          | congrFun h => cases h
                          | congrArg h =>
                            rename_i h_r _ _ _ _ _ _ _ _
                            exact (h_r.norm_aff ⟨_, h⟩).elim
                        | congrArg h =>
                          have h_dec := RedAff.instRedRel.decreasing h
                          have h_t' := h_t.preservation (.congrArg h)
                          exact refl_ty_heq h_t'
                    | congrFun h => cases h
                    | congrArg h =>
                      rename_i h_r _ _ _ _ _ _ _
                      exact (h_r.norm_aff ⟨_, h⟩).elim
                | congrArg h =>
                  have h_dec := RedAff.instRedRel.decreasing h
                  have h_t' := h_t.preservation (.congrArg h)
                  exact refl_ty_heq h_t'
            | congrFun h => cases h
            | congrArg h =>
              rename_i h_r _ _ _ _ _ _
              exact (h_r.norm_aff ⟨_, h⟩).elim
        | congrArg h =>
          have h_dec := RedAff.instRedRel.decreasing h
          have h_t' := h_t.preservation (.congrArg h)
          exact refl_ty_heq h_t'
    | .inr ⟨_, h, _⟩ => cases h
termination_by x₀.size

theorem comb_ty_not_eq (ht : Judge c (DCC (x = y))) (hv : IsRedComb c n) : False := by
  induction hv with
  | eql =>
    cases ht with
    | eql ht hr =>
      unfold eql.type at hr
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hr.pi
      cases hd
  | curr =>
    cases ht with
    | curr ha hb hc hd he hf =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hf.pi
      cases hd
  | pair =>
    cases ht with
    | pair ha hb hc hd he hf hg =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hg.pi
      cases hd
  | quot =>
    cases ht with
    | quot ha hb hc =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hc.pi
      cases hd
  | id =>
    cases ht with
    | id ha _ hb =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hb.pi
      cases hd
  | sigma =>
    cases ht with
    | sigma ha hb hc =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hc.pi
      cases hd
  | sndc =>
    cases ht with
    | sndc ha hb hc  =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hc.pi
      cases hd
  | fstc =>
    cases ht with
    | fstc ha hb hc  =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hc.pi
      cases hd
  | comp' =>
    cases ht with
    | comp' ha hb hc hd he hf =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hf.pi
      cases hd
  | comp =>
    cases ht with
    | comp ha hb hc hd  =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hd.pi
      cases hd

-- Probably somewhat easy to prove
open Congruent in
theorem eq_val_is_refl (ht : Judge e (DCC (x = y)))
  (hv : Value e) : ∃ f_α env x' env'' x'', e = (DCC (refl(f_α) env x'))
    ∧ Reduces e (DCC (refl(f_α) env'' x'')) := by
  induction hv with
  | c_app h_c_f h_v_f h_v_x ih₁ ih₂ =>
    cases h_c_f with
    | eql =>
      cases ht with
      | app h_t_f hb h_t_x _ h_r_τ =>
        cases h_t_f with
        | eql _ hr =>
          have ⟨a, b, c, d, e, f, g⟩ := hr.pi
          cases g
          have h' := hb.id
          obtain heq := c.quot
          cases heq
          have ⟨_, _, _, _, _, _, heq⟩ := h_r_τ.quot.pi
          simp_all
    | curr =>
      cases ht with
      | app h_t_f hb h_t_x _ h_r_τ =>
        cases h_t_f with
        | curr a b c d e f =>
          have ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁⟩ := f.pi
          cases g₁
          have h := hb.id
          have heq := c₁.quot
          cases heq
          cases c
          have ⟨_, _, _, _, _, _, heq⟩ := h_r_τ.quot.pi
          simp_all
  | tintro | top | eq | bot => cases ht
  | comb => exact (ht.comb_ty_not_eq (by assumption)).elim
  | pi₁ =>
    cases ht with
    | pi h_t_f_α h_t_f_β hr =>
      have h := hr.pi
      simp_all
  | pi₂ =>
    cases ht with
    | app h_t_f h_r_α h_t_x _ h_r_τ =>
      cases h_t_f with
      | pi h₁ h₂ hr =>
        have ⟨_, _, ha, hb, hc, hd, he⟩ := hr.pi
        cases he
        match ha.cases_head with
        | .inl h =>
          cases h
          have h := h_r_τ.curr
          have h := h.quot₁
          match h with
          | ⟨ha, hb, hc, hd⟩ =>
            match ha.cases_head with
            | .inl h =>
              cases h
              match hc.cases_head with
              | .inl h => simp_all
              | .inr ⟨_, h₁, h₂⟩ => cases h₁
            | .inr ⟨_, h₁, h₂⟩ => cases h₁
        | .inr ⟨_, h₁, h₂⟩ => cases h₁
  | coup =>
    cases ht with
    | coup _ _ hr =>
      have h := hr.sort
      contradiction
  | sort => cases ht
  | refl₁ =>
    cases ht with
    | app h_t_f h_r_α h_t_x _ h_r_τ =>
      cases h_t_f with
      | refl h₁ hr =>
        have ⟨_, _, ha, hb, hc, hd, he⟩ := hr.pi
        cases he
        match ha.cases_head with
        | .inl h =>
          cases h
          have h := h_r_α.id
          have h := h_r_τ.quot.pi
          simp_all
        | .inr ⟨_, h₁, h₂⟩ =>
          cases h₁
  | refl₂ h_val_env h_val_x =>
    have h_norm_env := h_val_env.is_norm_aff
    have h_norm_x   := h_val_x.is_norm_aff
    have h_eq_refl  := ht.refl_ty_heq
    cases ht with
    | app h_t_f h_r_α h_t_x _ h_r_τ =>
      cases h_t_f with
      | app h_t_f' h_r_α' h_t_x' _ h_r_τ' =>
        cases h_t_f' with
        | refl h₁ hr =>
          have ⟨_, _, ha, hb, hc, hd, he⟩ := hr.pi
          cases he
          match ha.cases_head with
          | .inl h =>
            cases h
            have h := h_r_α'.id
            have ⟨_, _, h₁, h₂, h₃, h₄, h₅⟩ := h_r_τ'.quot.pi
            cases h₅
            match h₁.cases_head with
            | .inl h =>
              cases h
              have h := h_r_τ.congrFun .comp
              have ⟨_, heq⟩ := h.eql
              cases heq
              match h with
              | ⟨ha₁, hb₁, hc₁, hd₁⟩ =>
                match ha₁.cases_head with
                | .inl h =>
                  cases h
                  match hc₁.eq with
                  | .inl ⟨_, _, heq₁, heq₂⟩ =>
                    cases heq₁; cases heq₂
                    exact ⟨_, _, _, _, _, rfl, ⟨.refl, fun ⟨_, h⟩ => by
                      cases h with
                      | congrFun h =>
                        cases h with
                        | congrFun h => cases h
                        | congrArg h => exact h_norm_env ⟨_, h⟩
                      | congrArg h =>
                        exact h_norm_x ⟨_, h⟩, .refl, fun ⟨_, h⟩ => by cases h⟩⟩
                  | .inr h => simp_all
                | .inr ⟨_, h₁, h₂⟩ =>
                  cases h₁ with
                  | congrFun h =>
                    cases h with
                    | congrFun h => cases h
                    | congrArg hr =>
                      rename_i env₀ x₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                      cases hr with
                      | id =>
                        exact ⟨_, env₀, x₀, _, _, rfl, ⟨.refl, fun ⟨_, h⟩ => by
                          cases h with
                          | congrFun h =>
                            cases h with
                            | congrFun h => cases h
                            | congrArg h  =>
                              exact h_norm_env ⟨_, h⟩
                          | congrArg h =>
                            exact h_norm_x ⟨_, h⟩, .refl, fun ⟨_, h⟩ => by cases h⟩⟩
                      | congrFun h => cases h
                      | congrArg hr =>
                        exact ⟨_, env₀, x₀, _, _, rfl, ⟨.refl, fun ⟨_, h⟩ => by
                          cases h with
                          | congrFun h =>
                            cases h with
                            | congrFun h => cases h
                            | congrArg h  =>
                              exact h_norm_env ⟨_, h⟩
                          | congrArg h =>
                            exact h_norm_x ⟨_, h⟩, .refl, fun ⟨_, h⟩ => by cases h⟩⟩
                  | congrArg h =>
                    rename_i env₀ x₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    exact ⟨_, env₀, x₀, _, _, rfl, ⟨.refl, fun ⟨_, h⟩ => by
                          cases h with
                          | congrFun h =>
                            cases h with
                            | congrFun h => cases h
                            | congrArg h  =>
                              exact h_norm_env ⟨_, h⟩
                          | congrArg h =>
                            exact h_norm_x ⟨_, h⟩, .refl, fun ⟨_, h⟩ => by cases h⟩⟩
            | .inr ⟨_, h₁, h₂⟩ => cases h₁
          | .inr ⟨_, h₁, h₂⟩ => cases h₁

/-
induction using Expr.instWellFounded?

Due to progress
-/
theorem eq_is_refl (h_t : Judge e (DCC (x = y))) :
  ∃ f_α env x₀, Reduces e (DCC (refl(f_α) env x₀)) := by
  induction e using RedAff.instRedRel.wellFounded.induction with
  | h e ih =>
    match h_t.progress with
    | .inl h_val =>
      have ⟨f_α, env, x', env'', x'', heq, hred⟩ := h_t.eq_val_is_refl h_val
      simp_all
      exact ⟨f_α, _, _, hred⟩
    | .inr ⟨e', hr⟩ =>
      match ih _ hr (h_t.preservation hr) with
      | ⟨f_α, env, _, ⟨hr₁, hn₁, hr₂, hn₂⟩⟩ =>
        exact ⟨f_α, env, _, ⟨.trans (.single hr) hr₁, hn₁, hr₂, hn₂⟩⟩

theorem elim_eq (h : Judge e (DCC (x = y))) : x = y := by
  have ⟨f_α, env, _, h_r⟩ := eq_is_refl h
  have ht' := h.preservation' h_r
  exact refl_ty_heq ht'

end Judge

end Expr
