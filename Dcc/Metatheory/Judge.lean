import Dcc.Judge
import Dcc.Metatheory.Congr
import Dcc.Metatheory.Decidability

namespace Expr

namespace Judge

syntax "⊢" gen_dcc ":" gen_dcc    : term

macro_rules
  | `(term| ⊢ $e:gen_dcc : $τ:gen_dcc) => `(term| Expr.Judge (DCC $e:gen_dcc) (DCC $τ:gen_dcc))

@[dcc_judge, grind ., grind <=]
theorem unique (h₁ : ⊢ e : τ₁) (h₂ : ⊢ e : τ₂) : τ₁ = τ₂ := by
  have ha := h₁.complete
  have hf := h₂.complete
  simp_all

theorem invert (ht : ⊢ e : τ) (heq : e = (DCC (f x))) : ∃ f_α f_β env α env',
  (Judge f (DCC (Π(f_α, f_β) env)) ∧ Reduces (DCC (f_α env)) α
    ∧ Judge x α ∧ Reduces env env' ∧ Reduces (DCC (f_β env' x)) τ) := by
  induction ht with
  | app h_t_f h_r_α h_t_x h_r_env h_r_τ =>
    cases heq
    exact ⟨_, _, _, _, _, h_t_f, h_r_α, h_t_x, h_r_env, h_r_τ⟩
  | _ => grind

theorem norm_eta (ht : Judge e τ) : IsNorm RedEta τ := by
  induction ht
  any_goals (focus
    first
    | exact Reduces.norm_eta (by assumption)
    | intro ⟨_, h⟩; cases h
    done)
  case mk hrβ hrβx _ _ _ _ =>
    have h := hrβ.norm_eta
    intro ⟨_, h⟩
    cases h with
    | coup hr =>
      exact h ⟨_, hr⟩

theorem norm_aff (ht : Judge e τ) : IsNorm RedAff τ := by
  induction ht
  any_goals (
    focus
    first
    | exact Reduces.norm_aff (by assumption)
    | intro ⟨_, h⟩; cases h
    done)
  case mk h =>
    intro ⟨_, h⟩
    cases h with
    | coup h =>
      rename_i hrβ _ _ _ _ _ _
      have hn := hrβ.norm_aff
      exact hn ⟨_, h⟩
  case box hn =>
    intro ⟨_, h⟩
    cases h with
    | bang hr =>
      exact hn ⟨_, hr⟩

theorem red_eta (ht : Judge e τ) (hr : RedEta τ τ' ) : Judge e τ' := by
  have h₁ := ht.norm_aff
  have h₂ := ht.norm_eta
  exact (h₂ ⟨_, (by assumption)⟩).elim

theorem red_eta_refl_trans (ht : Judge e τ) (hr : RedEtaReflTrans τ τ') : Judge e τ' := by
  have h₁ := ht.norm_aff
  have h₂ := ht.norm_eta
  match hr.cases_head with
  | .inl h => cases h; assumption
  | .inr ⟨_, h₁, h₂⟩ =>
    have h := ht.red_eta h₁
    have h_dec := RedEta.instRedRel.decreasing h₁
    exact h.red_eta_refl_trans h₂
termination_by τ.size

theorem red_aff (ht : Judge e τ) (hr : RedAff τ τ' ) : Judge e τ' := by
  have h₁ := ht.norm_aff
  have h₂ := ht.norm_eta
  exact (h₁ ⟨_, (by assumption)⟩).elim

theorem red_aff_refl_trans (ht : Judge e τ) (hr : RedAffReflTrans τ τ') : Judge e τ' := by
  have h₁ := ht.norm_aff
  have h₂ := ht.norm_eta
  match hr.cases_head with
  | .inl h => cases h; assumption
  | .inr ⟨_, h₁, h₂⟩ =>
    have h := ht.red_aff h₁
    have h_dec := RedAff.instRedRel.decreasing h₁
    exact h.red_aff_refl_trans h₂
termination_by τ.size

theorem reduces (ht : Judge e τ) (hr : Reduces τ τ') : Judge e τ' := by
  have h₁ := ht.norm_aff
  have h₂ := ht.norm_eta
  match hr with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    match hr₁.cases_head with
    | .inl h =>
      cases h
      have h := hr₂.elim_norm (by assumption)
      simp_all
    | .inr ⟨_, ha, hb⟩ => exact (h₁ ⟨_, ha⟩).elim

end Judge

end Expr
