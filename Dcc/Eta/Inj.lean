import Dcc.Eta.Ast

namespace GenericExpr

set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
set_option maxHeartbeats 100000000000 in
def eta_to_expr_inj {hn1 : ¬ f1.contains_hole} {hn2 : ¬ f2.contains_hole} :
  eta_to_expr f1 hn1 = eta_to_expr f2 hn2 → f1 = f2 := by
  intro h
  unfold eta_to_expr at h
  simp at h
  split at h
  any_goals (grind)
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_1 x y hn_contains_1) = x_1.eta_to_expr (eta_to_expr._proof_1 x_1 y_1 hn_contains_3) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_2 x y hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_2 x_1 y_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : (x.eta_to_expr (eta_to_expr._proof_3 x hn_contains_1)) = (x_1.eta_to_expr (eta_to_expr._proof_3 x_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : (x.eta_to_expr (eta_to_expr._proof_4 x hn_contains_1)) = (x_1.eta_to_expr (eta_to_expr._proof_4 x_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_1 x y hn_contains_1) = x_1.eta_to_expr (eta_to_expr._proof_1 x_1 y_1 hn_contains_3) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_2 x y hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_2 x_1 y_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_1 x y hn_contains_1) = x_1.eta_to_expr (eta_to_expr._proof_1 x_1 y_1 hn_contains_3) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_2 x y hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_2 x_1 y_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : (x.eta_to_expr (eta_to_expr._proof_9 x y z hn_contains_1)) = (x_1.eta_to_expr (eta_to_expr._proof_9 x_1 y_1 z_1 hn_contains_3)) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_10 x y z hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_10 x_1 y_1 z_1 hn_contains_3)) := by grind
      have heq₃ : (z.eta_to_expr (eta_to_expr._proof_11 x y z hn_contains_1)) = (z_1.eta_to_expr (eta_to_expr._proof_11 x_1 y_1 z_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      have hc := eta_to_expr_inj heq₃
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_12 x hn_contains_1) = (x_1.eta_to_expr (eta_to_expr._proof_12 x_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_12 x hn_contains_1) = (x_1.eta_to_expr (eta_to_expr._proof_12 x_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_12 x hn_contains_1) = (x_1.eta_to_expr (eta_to_expr._proof_12 x_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_12 x hn_contains_1) = (x_1.eta_to_expr (eta_to_expr._proof_12 x_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_1 x y hn_contains_1) = x_1.eta_to_expr (eta_to_expr._proof_1 x_1 y_1 hn_contains_3) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_2 x y hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_2 x_1 y_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_1 x y hn_contains_1) = x_1.eta_to_expr (eta_to_expr._proof_1 x_1 y_1 hn_contains_3) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_2 x y hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_2 x_1 y_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_1 x y hn_contains_1) = x_1.eta_to_expr (eta_to_expr._proof_1 x_1 y_1 hn_contains_3) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_2 x y hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_2 x_1 y_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_1 x y hn_contains_1) = x_1.eta_to_expr (eta_to_expr._proof_1 x_1 y_1 hn_contains_3) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_2 x y hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_2 x_1 y_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : (x.eta_to_expr (eta_to_expr._proof_9 x y z hn_contains_1)) = (x_1.eta_to_expr (eta_to_expr._proof_9 x_1 y_1 z_1 hn_contains_3)) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_10 x y z hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_10 x_1 y_1 z_1 hn_contains_3)) := by grind
      have heq₃ : (z.eta_to_expr (eta_to_expr._proof_11 x y z hn_contains_1)) = (z_1.eta_to_expr (eta_to_expr._proof_11 x_1 y_1 z_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      have hc := eta_to_expr_inj heq₃
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : (x.eta_to_expr (eta_to_expr._proof_9 x y z hn_contains_1)) = (x_1.eta_to_expr (eta_to_expr._proof_9 x_1 y_1 z_1 hn_contains_3)) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_10 x y z hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_10 x_1 y_1 z_1 hn_contains_3)) := by grind
      have heq₃ : (z.eta_to_expr (eta_to_expr._proof_11 x y z hn_contains_1)) = (z_1.eta_to_expr (eta_to_expr._proof_11 x_1 y_1 z_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      have hc := eta_to_expr_inj heq₃
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : (x.eta_to_expr (eta_to_expr._proof_9 x y z hn_contains_1)) = (x_1.eta_to_expr (eta_to_expr._proof_9 x_1 y_1 z_1 hn_contains_3)) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_10 x y z hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_10 x_1 y_1 z_1 hn_contains_3)) := by grind
      have heq₃ : (z.eta_to_expr (eta_to_expr._proof_11 x y z hn_contains_1)) = (z_1.eta_to_expr (eta_to_expr._proof_11 x_1 y_1 z_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      have hc := eta_to_expr_inj heq₃
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : (x.eta_to_expr (eta_to_expr._proof_9 x y z hn_contains_1)) = (x_1.eta_to_expr (eta_to_expr._proof_9 x_1 y_1 z_1 hn_contains_3)) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_10 x y z hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_10 x_1 y_1 z_1 hn_contains_3)) := by grind
      have heq₃ : (z.eta_to_expr (eta_to_expr._proof_11 x y z hn_contains_1)) = (z_1.eta_to_expr (eta_to_expr._proof_11 x_1 y_1 z_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      have hc := eta_to_expr_inj heq₃
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_12 x hn_contains_1) = (x_1.eta_to_expr (eta_to_expr._proof_12 x_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_12 x hn_contains_1) = (x_1.eta_to_expr (eta_to_expr._proof_12 x_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_12 x hn_contains_1) = (x_1.eta_to_expr (eta_to_expr._proof_12 x_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_12 x hn_contains_1) = (x_1.eta_to_expr (eta_to_expr._proof_12 x_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_12 x hn_contains_1) = (x_1.eta_to_expr (eta_to_expr._proof_12 x_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : x.eta_to_expr (eta_to_expr._proof_12 x hn_contains_1) = (x_1.eta_to_expr (eta_to_expr._proof_12 x_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      grind
  · split at h
    any_goals (grind)
    · expose_names
      have heq₁ : (x.eta_to_expr (eta_to_expr._proof_42 x y hn_contains_1)) = (x_1.eta_to_expr (eta_to_expr._proof_42 x_1 y_1 hn_contains_3)) := by grind
      have heq₂ : (y.eta_to_expr (eta_to_expr._proof_43 x y hn_contains_1)) = (y_1.eta_to_expr (eta_to_expr._proof_43 x_1 y_1 hn_contains_3)) := by grind
      have ha := eta_to_expr_inj heq₁
      have hb := eta_to_expr_inj heq₂
      grind

@[grind ., grind <=, dcc_rel]
theorem eta_to_expr_inj' {hn1 : ¬ f1.contains_hole} {hn2 : ¬ f2.contains_hole} :
  eta_to_expr f1 hn1 = eta_to_expr f2 hn2 → f1 = f2 := eta_to_expr_inj

end GenericExpr
