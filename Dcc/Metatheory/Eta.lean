import Dcc.Judge2
import Dcc.Aff.Red
import Dcc.Eta.Reduce
import Dcc.Value

namespace GenericExpr

/-
Valid outs:
- `(dom, out)

-/

inductive IsNormTmηReduces.{u} {τ_c : Type u} [DecidableEq τ_c] : (level : ℕ) → (f : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Prop
  | 

namespace TmEtaReduces

end TmEtaReduces

namespace RedEta??

/-
- RedEta??IsNorm
  - (Π(f_α, f_β) env)
    - IsNormη (f_β env).reduce'
    - IsNorm f_α
  - Coup(β)
    - IsNormη β
  - !(β)
    - IsNorm β
  - Π(f_α, f_β)
    - IsNorm f_α
    - IsNorm f_β
  - Π(f_α, f_β) ∘' g
    - IsNorm (#(f_α.reduce') ∘' g)
    - IsNorm (#(f_β.reduce') ∘' g)
  - Doesn't match shapes above ^ (IsEtaTm e)
    
    
-/

end RedEta??

namespace RedEta₂

/-
An η reduction is normal if:

- there is no RedEta?? (RedEta₂.refl)
- step
  - IsNormη?? e
-/

end RedEta₂

namespace IsNorm

theorem mkc (h : IsNorm RedAff (DCC? (f ⟦β⟧(x, y)))) : IsNorm RedAff (DCC? (f ⟦β₂⟧(x, y))) :=
  fun ⟨_, h⟩ => by
    cases h
    any_goals (
      focus
      apply h
      constructor
      constructor
      done)
    case congrFun hr =>
      exact h.congrFun ⟨_, hr⟩
    case congrArg hr =>
      cases hr with
      | sigl hr => exact h.congrArg.sigl ⟨_, hr⟩
      | sigr hr => exact h.congrArg.sigr ⟨_, hr⟩

theorem mkc' (h : IsNorm RedAff (DCC? ⟦β⟧(x, y))) : IsNorm RedAff (DCC? ⟦β₂⟧(x, y)) :=
  fun ⟨_, h⟩ => by
    cases h with
    | sigl hr => exact h.sigl ⟨_, hr⟩
    | sigr hr => exact h.sigr ⟨_, hr⟩

end IsNorm

namespace EtaMap₂

/-theorem reduce_self.{u} {τ_c : Type u} [DecidableEq τ_c] {dom dom₂ out hole₁ hole₂ f f' f'' : GenericExpr (@EtaConst τ_c)} (hn : IsNorm RedAff f)
  (hr₁ : EtaMap₂ dom dom₂ out hole₁ hole₂ f')
  (hr₂ : TmEtaReduces level f' f'') : f' = f'' := by-/

end EtaMap₂

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

/-theorem reduce_self.{u} {τ_c : Type u} [DecidableEq τ_c] {f f' f'' : GenericExpr (@EtaConst τ_c)} (hn : IsNorm RedAff f)
  (hr₁ : TmEtaReduces level f f')
  (hr₂ : TmEtaReduces level f' f'') : f' = f'' := by
  have ha := hr₁.is_norm_aff
  have hb := hr₂.is_norm_aff
  induction hr₂ generalizing f with
  | coupl hrt₁ hn₂ h_dom hrt₂ hn₃ h_res =>
    induction hr₁ generalizing f'' with
    | coupl hrt₃ hn₄ h_dom₂ hrt₅ hn₆ h_res₂ =>
      cases hrt₃.elim_head_norm hn
      cases hrt₁.elim_head_norm ha
      cases h_res₂ with
      | map h_contains h_map =>
        cases h_map with
        | id =>
          cases (hrt₂.push_head (by assumption) .id).elim_head_norm (fun ⟨_, h⟩ => by
            cases h with
            | sigl h => cases h
            | sigr h => cases h)
          cases h_dom with
          | id =>
            cases h_res with
            | map h_contains h =>
              cases h with
              | id => rfl
            | quot h_contains => grind
        | sndc =>
          cases (hrt₂.push_head (by assumption) .sndc).elim_head_norm (fun ⟨_, h⟩ => by
            cases h)
          cases h_dom with
          | sndc =>
            cases h_res with
            | map h_contains h =>
              cases h with
              | sndc => rfl
            | quot h_contains => grind
        | fstc =>
          cases (hrt₂.push_head (by assumption) .fstc).elim_head_norm (fun ⟨_, h⟩ => by
            cases h)
          cases h_dom with
          | fstc =>
            cases h_res with
            | map h_contains h =>
              cases h with
              | fstc => rfl
            | quot h_contains => grind
        | par =>
          cases hrt₂.elim_head_norm hn₆.mkc
          cases h_res with
          | map h_contains' =>
            rename_i h_map
            cases h_map with
            | par =>
              
              sorry-/

theorem reduce_self.{u} {τ_c : Type u} [DecidableEq τ_c] {f f' f'' : GenericExpr (@EtaConst τ_c)} (hn : IsNorm RedAff f)
  (hr₁ : TmEtaReduces level f f')
  (hr₂ : TmEtaReduces level f' f'') : f' = f'' := by
  induction hr₁ generalizing f'' with
  | coupl hrt₁ hn₂ h_dom hrt₂ hn₃ h_res =>
    induction hr₂ generalizing f with
    | coupl hrt₃ hn₄ h_dom₂ hrt₅ hn₆ h_res₂ =>
      cases h_res with
      | map h_contains h_res =>
        cases h_res₂ with
        | map h_contains₂ h_res₂ =>
          cases h_res with
          | id =>
            have h := hrt₃.elim_head_norm (fun ⟨_, h⟩ => by cases h)
            cases h
            have h := (hrt₅.push_head hn₆ .id).elim_head_norm (fun ⟨_, h⟩ => by
                cases h with
                | sigl h => cases h
                | sigr h => cases h)
            cases h_dom₂
            simp_all
            cases h.symm
            cases h_res₂ with
            | id => rfl
          | sndc =>
            have h := hrt₃.elim_head_norm (fun ⟨_, h⟩ => by cases h)
            cases h
            have h := (hrt₅.push_head hn₆ .sndc).elim_head_norm (fun ⟨_, h⟩ => by cases h)
            cases h_dom₂
            simp_all
            cases h.symm
            cases h_res₂ with
            | sndc => rfl
          | fstc =>
            have h := hrt₃.elim_head_norm (fun ⟨_, h⟩ => by cases h)
            cases h
            have h := (hrt₅.push_head hn₆ .fstc).elim_head_norm (fun ⟨_, h⟩ => by cases h)
            cases h_dom₂
            simp_all
            cases h.symm
            cases h_res₂ with
            | fstc => rfl
          | par =>
            cases hrt₁.elim_head_norm hn
            cases hrt₃.elim_head_norm (hn₃.congrFun)
            cases hrt₅.elim_head_norm hn₃.mkc
            cases h_res₂ with
            | par => rfl
        | quot h_contains' =>
          cases h_res with
          | id =>
            cases hrt₃.elim_head_norm (fun ⟨_, h⟩ => by cases h)
            cases (hrt₅.push_head hn₆ .id).elim_head_norm (fun ⟨_, h⟩ => by
                cases h with
                | sigl h => cases h
                | sigr h => cases h)
            cases h_dom₂ with
            | id => grind
          | sndc =>
            cases hrt₃.elim_head_norm (fun ⟨_, h⟩ => by cases h)
            cases (hrt₅.push_head hn₆ .sndc).elim_head_norm (fun ⟨_, h⟩ => by cases h)
            cases h_dom₂ with
            | sndc => grind
          | fstc =>
            cases hrt₃.elim_head_norm (fun ⟨_, h⟩ => by cases h)
            cases (hrt₅.push_head hn₆ .fstc).elim_head_norm (fun ⟨_, h⟩ => by cases h)
            cases h_dom₂ with
            | fstc => grind
          | par =>
            cases hrt₃.elim_head_norm hn₃.congrFun
            cases hrt₅.elim_head_norm hn₃.mkc
            grind
      | quot h_contains' =>
        cases hrt₃.elim_head_norm (fun ⟨_, h⟩ => by cases h)
        cases h_dom₂
        cases (hrt₅.push_head (by assumption) .quot).elim_head_norm hn₃
        cases h_res₂ with
        | map h_contains'' h_map => cases h_map <;> grind
        | quot => grind
    | bang₁ =>
      rename_i f f' β level e' f'' hrt' hn' h_dom' hrt'' hn'' h_res''
      cases hrt'.elim_head_norm (h_res.is_norm_aff (by assumption))
      cases hrt₁.elim_head_norm (by assumption)
      cases h_res with
      | map h_contains''' h =>
        cases h with
        | id =>
          cases (hrt''.push_head (by assumption) .id).elim_head_norm (fun ⟨_, h⟩ => by cases h)
          cases h_dom'
        | fstc =>
          cases hrt''.elim_head_norm (fun ⟨_, h⟩ => by
            cases h with
            | congrFun h => cases h
            | congrArg h => cases h)
          cases h_dom'
        | sndc =>
          cases hrt''.elim_head_norm (fun ⟨_, h⟩ => by
            cases h with
            | congrFun h => cases h
            | congrArg h => cases h)
          cases h_dom'
        | par =>
          cases h_res'' with
          | map h_contains'' h_map'' =>
            have h := h_map''.is_norm_aff (by assumption)
            cases h_map'' with
            | fstc' | sndc' =>
              grind
            | id =>
              cases h_dom'
              · match hrt''.cases_head with
                | .inl h => grind
                | .inr ⟨_, h₁, h₂⟩ =>
                  cases h₁ with
                  | congrFun h => cases h
                  | congrArg h => cases h
              · match hrt''.cases_head with
                | .inl h => grind
                | .inr ⟨_, h₁, h₂⟩ =>
                  cases h₁ with
                  | eql =>
                    match h₂.cases_head with
                    | .inl h => cases h
                    | .inr ⟨_, h₁, h₂⟩ =>
                      cases h₁ with
                      | eql' h =>
                        cases h

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
