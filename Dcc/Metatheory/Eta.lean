import Dcc.Judge2
import Dcc.Aff.Red
import Dcc.Eta.Reduce
import Dcc.Value

namespace GenericExpr

theorem transport_eq_eta (h_contains₁ : ¬ (contains_hole A)) (h_contains₂ : ¬ (contains_hole B)) (h : A = B) : (eta_to_expr A h_contains₁) = (eta_to_expr B h_contains₂) := by sorry

namespace Domain

theorem unique.{u} {τ_c : Type u} [DecidableEq τ_c] {e τ₁ τ₂ : GenericExpr (@EtaConst τ_c)} (ht₁ : Domain e τ₁) (ht₂ : Domain e τ₂) : τ₁ = τ₂ := by
  have ha := ht₁.complete
  have ha := ht₂.complete
  simp_all

theorem preservation (ht : Domain e τ) (hr : RedAff e e') : Domain e' τ := by sorry

end Domain

namespace IsNorm

theorem transport_eta (hn : IsNorm RedAff A) : IsNorm RedAff (expr_to_eta A) := hn.to_eta

end IsNorm

namespace RedAffReflTrans

theorem transport_to_eta (hr : RedAffReflTrans A B) : RedAffReflTrans A.expr_to_eta B.expr_to_eta := by sorry

theorem domain_preservation (hr : RedAffReflTrans A B) (ht : Domain A τ) : Domain B τ := by sorry

end RedAffReflTrans

namespace TmEtaReduces₂

theorem reduce_self.{u} {τ_c : Type u} [DecidableEq τ_c] {f f' f'' : GenericExpr (@EtaConst τ_c)} (hn : IsNorm RedAff f) (hr₁ : TmEtaReduces₂ level f f')
  (hr₂ : TmEtaReduces₂ level f' f'') : f' = f'' := by
  sorry

theorem preservation_arity.{u} {τ_c : Type u} [DecidableEq τ_c] {f f' : GenericExpr (@EtaConst τ_c)} (hn : IsNorm RedAff f) (hr : TmEtaReduces₂ level f f') : tm_arity f = tm_arity f' := by
  sorry

end TmEtaReduces₂

namespace TmEtaReduces

theorem reduce_self.{u} {τ_c : Type u} [DecidableEq τ_c] {f f' f'' : GenericExpr (@EtaConst τ_c)} (hn : IsNorm RedAff f) (hr₁ : TmEtaReduces level f f')
  (hr₂ : TmEtaReduces level f' f'') : f' = f'' := by
  sorry

theorem preservation_arity.{u} {τ_c : Type u} [DecidableEq τ_c] {f f' : GenericExpr (@EtaConst τ_c)} (hn : IsNorm RedAff f) (hr : TmEtaReduces level f f') : tm_arity f = tm_arity f' := by
  sorry

end TmEtaReduces

namespace FnEtaReduces

theorem reduce_self.{u} {τ_c : Type u} [DecidableEq τ_c] {f f' f'' : GenericExpr (@EtaConst τ_c)} (hn : IsNorm RedAff f) (hr₁ : FnEtaReduces level f f')
  (hr₂ : FnEtaReduces level f' f'') : f' = f'' := by
  induction hr₁ generalizing f'' with
  | pi hr₃ hr₄ ih₁ ih₂ =>
    cases hr₂ with
    | pi hr₅ hr₆ =>
      have ha := ih₁ hn.pil (by assumption)
      have hb := ih₂ hn.pir (by assumption)
      simp_all
    | tm₂ | tm₁ | tm'₂ => grind
  | tm₁ h_arity hr₃ =>
    rename_i f₀ f'₀
    have h := hr₃.preservation_arity (by assumption)
    induction heq₀ : hr₂ generalizing f f₀ with
    | tm₂ | tm'₂ | pi hr₅ hr₆ ih₁ ih₂ => grind
    | tm₁ h_arity₂ hr₅ => exact hr₃.reduce_self (by assumption) (by assumption)
  | tm₂ h_arity hr₃ =>
    rename_i f₀ f'₀
    have h := hr₃.preservation_arity (by assumption)
    induction heq₀ : hr₂ generalizing f f₀ with
    | pi | tm'₂ | tm₁ => grind
    | tm₂ => exact hr₃.reduce_self (by assumption) (by assumption)
  | tm'₂ =>
    rename_i level f₀ h_arity hn₂
    induction hr₂ with
    | tm₂ | tm₁ | pi => grind
    | tm'₂ => rfl

end FnEtaReduces

namespace RedEta?

def preservation_is_tm.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' : GenericExpr τ_c} (hr : RedEta? e e') (h_tm : IsEtaTm e) : IsEtaTm e' := by
  sorry

theorem reduce_self.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' e'' : GenericExpr τ_c} (hn : IsNorm RedAff e) (hr₁ : RedEta? e e') (hr₂ : RedEta? e' e'') : e' = e'' := by
  sorry

end RedEta?

namespace RedEta??

def preservation_is_tm.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' : GenericExpr τ_c} (hr : RedEta?? e e') (h_tm : IsEtaTm e) : IsEtaTm e' := by
  sorry

theorem preservation_domain.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' : GenericExpr τ_c} {τ : GenericExpr (@EtaConst τ_c)} (h_dom : Domain e.expr_to_eta τ) (hr : RedEta?? e e') : Domain e'.expr_to_eta τ := by sorry

theorem reduce_self.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' e'' : GenericExpr τ_c} (hn : IsNorm RedAff e) (hr₁ : RedEta?? e e') (hr₂ : RedEta?? e' e'') : e' = e'' := by
  induction hr₁ generalizing e'' with
  | pi₁ =>
    cases hr₂ with
    | pi₁ =>
      rename_i hr₁ h_dom₁ h_contains₁ hr₂ hrt₁ hn₁ hr₃ ih₁ ih₂ ih₃ f_α' δ env' f_β_env f_β' h_contains₂ hn₃ hr₄ hr₅ h_dom₂ hr₆ hrt₂
      have ha := ih₁ hn.congrFun.pil hr₅
      have hb := ih₂ hn.congrArg hr₆
      have hc := (hr₁.preservation_domain h_dom₁).unique h_dom₂
      simp [ha, hb, hc]
      try (
        replace hrt₂ := hrt₂.push_head (by assumption) .quot
        have hd := hrt₂.elim_head_norm (hr₃.is_norm_aff hn₁)
        have he := ih₃ hn₁ (hd ▸ hr₄)
        exact he)
    | tm₂ | tm₁ h_eta_tm => aesop (rule_sets := [DccRel, DccForceReduce])
  | pi₂ hr₃ hr₄ ih₁ ih₂ =>
    cases hr₂ with
    | tm₂ | tm₁ => aesop (rule_sets := [DccRel, DccForceReduce])
    | pi₂ =>
      have ha := ih₁ hn.pil (by assumption)
      have hb := ih₂ hn.pir (by assumption)
      simp [ha, hb]
  | tm₁ h_eta_tm₁ hr₃ =>
    have h := hr₃.preservation_is_tm h_eta_tm₁
    cases hr₂ with
    | coup | bang | pi₃ | pi₂ | pi₁ => aesop (rule_sets := [DccRel, DccForceReduce])
    | tm₁ h_eta_tm₂ hr₄ => exact hr₃.reduce_self (by assumption) hr₄
    | tm₂ => rfl
  | tm₂ h_eta_tm₁ hn₂ hrt₁ hn₃ =>
    have h := hr₂.preservation_is_tm h_eta_tm₁
    cases hr₂ with
    | coup | bang | pi₃ | pi₂ | pi₁ => aesop (rule_sets := [DccRel, DccForceReduce])
    | tm₁ h_eta_tm₂ hr₄ => aesop (rule_sets := [DccRel, DccForceReduce])
    | tm₂ => rfl
  | coup hr₃ ih =>
    cases hr₂ with
    | tm₂ | tm₁ => aesop (rule_sets := [DccRel, DccForceReduce])
    | coup hr₄ => simp [ih hn.coup hr₄]
  | bang hr₃ ih =>
    cases hr₂ with
    | tm₂ | tm₁ => aesop (rule_sets := [DccRel, DccForceReduce])
    | bang hr₄ => simp [ih (fun ⟨_, h⟩ => by
      exact hn ⟨_, .bang (by assumption)⟩) hr₄]
  | pi₃ =>
    rename_i hrt₁ hn₁ hr₁ hrt₂ hn₂ hr₃ ih₁ ih₂
    --have ha := ih₁ (fun ⟨_, h⟩ => by cases h) (by sorry)
    cases hr₂ with
    | pi₂ =>
      have ha := ih₁ (fun ⟨_, h⟩ => by cases h) (by assumption)
      have hb := ih₂ (fun ⟨_, h⟩ => by cases h) (by assumption)
      simp_all
    | tm₂ => grind
    | tm₁ h_eta_tm hr₃ =>
      have heq := h_eta_tm.complete
      grind

end RedEta??

namespace RedEta₂

theorem reduce_self.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' e'' : GenericExpr τ_c} (hn : IsNorm RedAff e) (hr₁ : RedEta₂ e e') (hr₂ : RedEta₂ e' e'') : e' = e'' := by
  induction hr₁ with
  | refl hn =>
    cases hr₂ with
    | refl => rfl
    | step => exact (hn ⟨_, by assumption⟩).elim
  | step =>
    cases hr₂ with
    | refl => rfl
    | step =>
      rename_i hr₁ hr₂
      exact hr₁.reduce_self hn hr₂

end RedEta₂

end GenericExpr
