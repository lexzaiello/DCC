import Dcc.Judge2

namespace GenericExpr

set_option maxHeartbeats 1000000000000 in
theorem Judge₂.complete {e : GenericExpr τ_c} [DecidableEq τ_c] [BEq τ_c] (h : Judge₂ e t) : infer₂ e = .ok ⟨t, ⟨h⟩⟩ := by
  induction h
  any_goals (
    focus
    dsimp only [infer₂]; try dcc_aesop!; try grind)

instance {e : GenericExpr τ_c} [DecidableEq τ_c] [BEq τ_c] : Decidable (Judge₂ e t) :=
  match heq : infer₂ e with
   | .ok ⟨τ, ⟨h⟩⟩ =>
     if heq₂ : τ = t then .isTrue (heq₂ ▸ h)
     else .isFalse (fun h => by
       have h := h.complete
       simp_all)
   | .error _e => .isFalse (fun h => by
     have hn := h.complete
     grind)

end GenericExpr
