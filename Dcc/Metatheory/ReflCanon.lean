import Dcc.Ast
import Dcc.Judge
import Dcc.Metatheory.Value
import Dcc.Metatheory.Congr
import Dcc.Metatheory.Preservation
import Dcc.Metatheory.Judge
--import Dcc.Tactic.Reduce

/-
Want to automate IsNorm, but sounds hard.
-/

namespace Expr

namespace Judge

/-
I lowkey want the compiler to work.

Want an RAII-style thing comparable to pair.

Have this in some form already with lazy pair.

λ x => M N ≈ Λ(Eval ∘ ⟨M, N⟩) ∗

First of all, need to add back Eval.
Second of all, want Eval to work with the RAII thing.


-/

/-
Substitution lemma...

adding a
-/

/-
Progress might be important for this too since we can establish what normal forms are.
If e : (x = y), then either e is a normal form (e.g., refl), or it reduces to (what?)
-/

theorem preservation (ht : Judge A t) (hr : RedAff A B) : Judge B t := by
  sorry

/-theorem preservation (ht : Judge A t) (hr : RedAff A B) : Judge B t := by
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
      exact Judge.mk (ih₁ h) (by assumption) (by assumption) (βx_red.head_trans (.congrArg h)) (by assumption)
    | sigr h =>
      rename_i βx_red _ _
      exact Judge.mk (by assumption) (by assumption) (by assumption) (by assumption) (ih₃ h)
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
      | quot h_t_B _ _ hr_ty =>
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
    | fstc =>
      rename_i hrc hrcoup
      cases hrc with
      | fstc _ hrα hrt  =>
        cases hrcoup with
        | mk =>
          
          sorry
        /-have ⟨f_β', env', h_r_β', hn_β', h_r_α, hn, heq⟩ := hrt.pi
        simp_all
        have ⟨⟨ha, hb⟩, hc⟩ := heq
        simp_all
        rename_i h_r_env' _ _ _
        have h := h_r_env'.id
        cases hrcoup with
        | mk h_t_B h_t_β h_r_βx h_t_y h_r_β =>
          have h := h_r_β'.curr
          simp_all
          have heq₂ := hr_α.curr.quot₁
          cases hb; cases h
          rename_i h_env'' _ _ _ _ _ _ _
          have h := h.unique h_env''
          simp_all
          cases h
          cases (h_env''.elim_norm (by assumption)) with
          | refl =>
            
            sorry
          | tail ih h => cases h-/
          --match hr_α
          /-rename_i h_r_env₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          have h_uniq₁ := h_r_env₀.unique h
          have h := h_r_β'.curr
          simp_all
          have h := hr_α.curr.quot₁
          rename_i h_env_norm_tgt _ _ _ _ _ _
          have h := h_env_norm_tgt.norm_head (by assumption)
          rename_i h_r_β'' _ _ _ _ _ _ _
          have h_norm_β' := h_r_β''.norm_aff
          have h_env'_eq := h_r_α.elim_norm (fun ⟨_, h⟩ => by
            cases h with
            | coup h =>
              exact h_norm_β' ⟨_, h⟩)
          simp_all
          rename_i h_f_β_app _ _ _ _ _ _ _  _
          rename_i h_β_coup _ _
          rename_i heq_f_β' _
          cases heq_f_β'
          match h_β_coup with
          | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
            match hr₁.cases_head with
            | .inl h =>
              simp_all
              
              sorry
            | .inr ⟨_, h₁, h₂⟩ =>
              cases h₁ with
              | coup h =>
                
                sorry-/
          /-match h_f_β_app with
          | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
            cases hr₂ with
            | refl =>
              
              sorry
            | tail ih h =>
              cases h
              sorry-/
    | sndc => sorry
    | comp' => sorry
    | comp => sorry
    | curr => sorry
    | sigma => sorry

theorem preservation_eta (ht : Judge A t) (hr : RedEta A B) : Judge B t := by
  sorry-/

theorem progress (ht : Judge e τ) : Value e ∨ (∃ e', RedAff e e') := by
  /-induction ht with
  | app h_t_f h_r_α h_t_x h_r_x_α h_r_τ ih₁ ih₂ =>
    match ih₁ with
    | .inl h₁ =>
      match ih₂ with
      | .inl h₂ =>
        cases h₁ with
        | c_app =>
           exact .inl <| .c_app (by sorry) (by sorry) (by sorry)
        | pi₁ => exact .inl (.pi₂ (by assumption) (by assumption))
        | tintro | bot | top | sort => cases h_t_f
        exact .inr ⟨_, .congrArg (by assumption)⟩
    | .inr ⟨_, h⟩ =>
      exact .inr ⟨_, .congrFun (by assumption)⟩
  | eq =>
    
    sorry-/
  sorry

theorem preservation' (ht : Judge A t) (hr : Reduces A B) : Judge B t := by
  sorry

theorem refl_ty_heq (h_t : Judge (DCC (refl(f_α) env x₀)) (DCC x = y)) : x = y := by
  obtain ⟨a, b, c, d, e, h_t_refl_env, f, g, _, ⟨hr₁, hn₁, hr₂, hn₂⟩⟩ := h_t.invert rfl
  obtain ⟨i, j, k, l, n, m, o, p, r, q⟩ := h_t_refl_env.invert rfl
  cases m with
  | refl h_t_f_α _ h_r_refl_ty =>
    unfold refl.type at h_r_refl_ty
    obtain ⟨_, _, h₄, h₅, h₆, h₇, h₈⟩ := h_r_refl_ty.pi
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h₈
    cases o.id.unique (by assumption)
    cases h₄.quot
    have ⟨_, _, hr, _, _, _, heq⟩ := q.quot.pi
    cases hr.elim_norm (fun ⟨_, h⟩ => by cases h)
    cases heq
    rename_i h_r_e _ _ _ _ _ _ _ _ _
    have h := (hr₁.congr_fun (.single .comp) (by assumption))
    match hr₂.eq with
    | .inl ⟨_, _, heq₁, heq₂⟩ => cases heq₁; cases heq₂; rfl
    | .inr h =>
      cases h
      exact h.no_eql_eq.elim

theorem comb_ty_not_eq (ht : Judge c (DCC (x = y))) (hv : IsRedComb c n) : False := by
  induction hv with
  | eql =>
    cases ht with
    | eql ht _ hr =>
      unfold eql.type at hr
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hr.pi
      cases hd
  | curr =>
    cases ht with
    | curr ha hb hc hd he _ hf =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hf.pi
      cases hd
  | pair =>
    cases ht with
    | pair ha hb hc hd he hf _ hg =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hg.pi
      cases hd
  | quot =>
    cases ht with
    | quot ha hb _ hc =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hc.pi
      cases hd
  | id =>
    cases ht with
    | id ha _ hb =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hb.pi
      cases hd
  | sigma =>
    cases ht with
    | sigma ha hb _ hc =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hc.pi
      cases hd
  | sndc =>
    cases ht with
    | sndc ha hb _ hc  =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hc.pi
      cases hd
  | fstc =>
    cases ht with
    | fstc ha hb _ hc =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hc.pi
      cases hd
  | comp' =>
    cases ht with
    | comp' ha hb hc hd he _ hf =>
      have ⟨_, _, ha, hb, hc, hn, hd⟩ := hf.pi
      cases hd
  | comp =>
    cases ht with
    | comp ha hb hc _ hd  =>
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
        | eql _ _ hr =>
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
        | curr a b c d e _ f =>
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
    | pi h_t_f_α h_t_f_β _ hr =>
      have h := hr.pi
      simp_all
  | pi₂ =>
    cases ht with
    | app h_t_f h_r_α h_t_x _ h_r_τ =>
      cases h_t_f with
      | pi h₁ h₂ _ hr =>
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
      | refl h₁ _ hr =>
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
        | refl h₁ _ hr =>
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
                      rename_i env₀ x₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
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
                    rename_i env₀ x₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
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
In app case:
- Invoke progress:
  - if there is a next step, use inductive hypothesis
  - if it is a Value, use eq_val_is_refl

Progress might not actually need preservation.
I guess preservation is required :(
-/

theorem elim_eq (h : Judge e (DCC (x = y))) : x = y := by
  induction e using RedAff.instRedRel.wellFounded.induction with
  | h e ih =>
    match heq₂ : h with
    | .curr' _ _ _ _ _ _ h | .map _ _ h | .fmap _ _ h | .unbox _ h | .eval _ _ _ _ _ h
    | .eql _ _ h | .sigma _ _   _ h | .quot _ _ _ h | .pi _ _ _ h | .comp _ _ _ _ h
    | .pair _ _ _ _ _ _ _ h | .comp' _ _ _ _ _ _ h | .curr _ _ _ _ _ _ h
    | .sndc _ _ _ h | .fstc _ _ _ h | .id _ _ h | .refl _ _ h =>
      exact h.no_pi_eq.elim
    | app h_t_f h_r_α h_t_x h_r_x_α ih₂ =>
      rename_i f f_α f_β x_α α x x_α'
      match h.progress with
      | .inl v =>
        have ⟨f_α, env, x', env'', x'', heq, hr⟩ := h.eq_val_is_refl v
        cases heq
        exact h.refl_ty_heq
      | .inr ⟨e', hr⟩ =>
        simp_all
        exact ih _ hr ((x_α' ▸ h).preservation (by assumption))
    | coup _ _ h =>
      match h with
      | ⟨h₁, h₂, h₃, h₄⟩ =>
        match h₁.cases_head with
        | .inl h =>
          cases h
          match h₃.cases_head with
          | .inl h => cases h
          | .inr ⟨_, h₁, h₂⟩ => cases h₁
        | .inr ⟨_, h₁, h₂⟩ => cases h₁

end Judge

end Expr
