import Dcc.Eta.Ast

namespace GenericExpr

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

namespace IsNorm

def to_eta {e : GenericExpr τ_c} (hn : GenericExpr.IsNorm RedAff e) : GenericExpr.IsNorm GenericExpr.RedAff
  (e.expr_to_eta (τ_c := τ_c)) := fun ⟨_, h⟩ =>
  hn ⟨_, to_eta_left_inv ▸ (h.reflect_eta GenericExpr.to_eta_no_hole)⟩

def from_eta {e : GenericExpr (@EtaConst τ_c)} (hn₁ : GenericExpr.IsNorm RedAff e) (hn₂ : ¬ e.contains_hole) : GenericExpr.IsNorm GenericExpr.RedAff
  (e.eta_to_expr hn₂) := fun ⟨_, h⟩ =>
  hn₁ ⟨_, to_eta_right_inv hn₂ ▸ h.cast_red_eta⟩

end IsNorm

end GenericExpr
