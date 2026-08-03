import Dcc.Eta.Ast

namespace GenericExpr

@[dcc_reduce]
def to_from_eta_eq {e : GenericExpr τ} {hn : ¬ (expr_to_eta e).contains_hole} : eta_to_expr (expr_to_eta e) hn = e := by
  have heq : hn = to_eta_no_hole := by
    constructor
  simp_all [to_eta_left_inv]

namespace RedAff

def cast_red_eta {A B : GenericExpr τ_c} (hr : RedAff A B)
  : RedAff A.expr_to_eta B.expr_to_eta := by
  induction hr <;> (simp_all [expr_to_eta]; constructor <;> simp_all)

def tail_no_hole (hr : RedAff A B) (hn : ¬ A.contains_hole) : ¬ B.contains_hole := by
  induction hr <;> grind

def reflect_eta {A B : GenericExpr (@EtaConst τ_c)} (hr : RedAff A B)
  (hn : ¬ A.contains_hole) : RedAff (A.eta_to_expr hn) (B.eta_to_expr (tail_no_hole hr hn)) := by
  induction hr <;> (
    focus
    rename_i ih
    simp [eta_to_expr]
    first
    | (constructor; exact (ih (by simp_all [contains_hole])))
    | (constructor))

end RedAff

namespace RedAffReflTrans

def cast_eta {A B : GenericExpr τ_c} (hr : RedAffReflTrans A B) : RedAffReflTrans A.expr_to_eta B.expr_to_eta := by
  induction hr with
  | refl =>
    exact .refl
  | tail ih h =>
    exact .trans (by assumption) (.single (RedAff.cast_red_eta (by assumption)))

end RedAffReflTrans

namespace IsNorm

@[aesop safe apply (rule_sets := [DccRel])]
def to_eta {e : GenericExpr τ_c} (hn : GenericExpr.IsNorm RedAff e) : GenericExpr.IsNorm GenericExpr.RedAff
  (e.expr_to_eta (τ_c := τ_c)) := fun ⟨_, h⟩ =>
  hn ⟨_, to_eta_left_inv ▸ (h.reflect_eta GenericExpr.to_eta_no_hole)⟩

def from_eta {e : GenericExpr (@EtaConst τ_c)} (hn₁ : GenericExpr.IsNorm RedAff e) (hn₂ : ¬ e.contains_hole) : GenericExpr.IsNorm GenericExpr.RedAff
  (e.eta_to_expr hn₂) := fun ⟨_, h⟩ =>
  hn₁ ⟨_, to_eta_right_inv hn₂ ▸ h.cast_red_eta⟩

end IsNorm

def arity_from_eta (heq₁ : f₁ = expr_to_eta f₂) (heq₂ : arity f₁ = n) : arity f₂ = n := by
  induction f₂ generalizing f₁ n
  any_goals (
    subst_vars
    grind)
  case id =>
    subst_vars
    expose_names
    simp [expr_to_eta]
    unfold arity
    split
    any_goals (grind)
    · expose_names
      cases heq
      split
      any_goals (grind)
      expose_names
      have heq : a.expr_to_eta = (_α.pi _β).app _x_α := by grind
      have ha := a_ih heq.symm (by simp [arity]; rfl)
      have hn := heq ▸ to_eta_no_hole (e := a)
      unfold expr_to_eta at heq
      simp at heq
      split at heq
      any_goals (grind)
      have hb := h (eta_to_expr _α (by grind)) (eta_to_expr _β (by grind)) (eta_to_expr _x_α (by grind)) (by
        unfold expr_to_eta at heq
        simp at heq
        split at heq
        any_goals (grind))
      exact hb.elim
  case quot =>
    subst_vars
    expose_names
    simp [expr_to_eta]
    unfold arity
    split
    any_goals (grind)
    · expose_names
      cases heq
      split
      any_goals (grind)
      expose_names
      unfold expr_to_eta at heq
      simp at heq
      split at heq
      any_goals (grind)

def arity_from_eta' (heq : arity (expr_to_eta f) = n) : arity f = n :=
  arity_from_eta (f₁ := (expr_to_eta f)) rfl heq

def arity_eta {f₁ : @GenericExpr τ_c} (heq₁ : f₂ = GenericExpr.expr_to_eta f₁) (heq : arity f₁ = n) : arity f₂ = n := by
  induction f₁ generalizing f₂ n
  any_goals (simp_all [GenericExpr.expr_to_eta]; subst_vars; grind)
  case id =>
    expose_names
    subst_vars
    simp [expr_to_eta]
    unfold arity
    split
    any_goals (grind)
    · expose_names
      split
      any_goals (grind)
      expose_names
      have heq : a.expr_to_eta = (_α.pi _β).app _x_α := by grind
      cases heq_1
      have h := arity_from_eta heq.symm rfl
      expose_names
      have ha := a_ih heq.symm h
      have hn := heq ▸ to_eta_no_hole (e := a)
      unfold expr_to_eta at heq
      simp at heq
      split at heq
      any_goals (grind)
      expose_names
      have hb := h_1 (eta_to_expr _α (by grind)) (eta_to_expr _β (by grind)) (eta_to_expr _x_α (by grind)) (by
        unfold expr_to_eta at heq
        simp at heq
        split at heq
        any_goals (grind))
      exact hb.elim
  case quot =>
    subst_vars
    expose_names
    simp [expr_to_eta]
    unfold arity
    split
    any_goals (grind)
    · expose_names
      split
      any_goals (grind)
      expose_names
      unfold expr_to_eta at heq
      simp at heq
      split at heq
      any_goals (grind)

def arity_eta' {f₁ : @GenericExpr τ_c} (heq : arity f₁ = n) : arity (expr_to_eta f₁) = n :=
  arity_eta (f₁ := f₁) rfl (n := n) heq

end GenericExpr

namespace NormExpr

def arity_eta (heq : arity ⟨f, hn⟩ = n) : arity ⟨(GenericExpr.expr_to_eta f), hn.to_eta⟩ = n := by
  induction f generalizing n
  any_goals (grind)
  any_goals (
    focus
    try (
      expose_names
      simp_all [GenericExpr.expr_to_eta, arity, raw]
      have h := GenericExpr.arity_eta' heq
      grind))

open GenericExpr in
def to_eta (e : @NormExpr τ_c RedAff) : (@NormExpr (@EtaConst τ_c) (RedAff (τ := (@EtaConst τ_c)))) :=
  match e with
  | ⟨e, hn⟩ => ⟨e.expr_to_eta, hn.to_eta⟩

end NormExpr

namespace GenericExpr

open GenericExpr in
@[aesop safe apply (rule_sets := [DccRel])]
def RedAffNorm.to_eta (h : RedAffNorm A B) : RedAffNorm A.expr_to_eta ⟨B.raw.expr_to_eta, B.is_norm.to_eta⟩ :=
  match h with
  | ⟨hr, hn⟩ => ⟨hr.cast_eta, hn.to_eta⟩

end GenericExpr
