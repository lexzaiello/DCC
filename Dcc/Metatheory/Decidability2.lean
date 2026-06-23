import Dcc.Judge2

namespace GenericExpr

theorem Judge₂.complete {e : GenericExpr τ_c} [DecidableEq τ_c] [BEq τ_c] (h : Judge₂ e t) : infer₂ e = .some ⟨t, ⟨h⟩⟩ := by
  induction h <;> (dsimp only [infer₂]; try dcc_aesop!; try grind)

instance {e : GenericExpr τ_c} [DecidableEq τ_c] [BEq τ_c] : Decidable (Judge₂ e t) :=
  if h : (infer₂ e).isSome then
    if heq : ((infer₂ e).get h).fst = t then
      .isTrue (heq ▸ ((infer₂ e).get h).snd.down)
    else
      isFalse (fun h => by simp [h.complete] at *)
  else
    isFalse (fun h => by simp [h.complete] at *)

end GenericExpr
