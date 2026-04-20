import Dcc.CC.Judge2
import Dcc.CC.Ast

namespace Expr

@[simp] theorem with_arr_arr : with_arr (.some ⟨arrow α β m, h⟩) = .some ⟨arrow α β m, α, β, m, h, ⟨rfl⟩⟩ := by
  simp [arrow, with_arr, match_arrow]
  aesop

theorem Judge.complete (h : Judge e t) : infer e = .some ⟨t, ⟨h⟩⟩ := by
  induction h
  case sort => dsimp only [infer]
  case id h_r ih
    | comp h_r ih₁ ih₂ | fst h_r ih
    | snd h_r ih | snd' h_r ih₁ ih₂
    | quot h_r ih₁ ih₂
    | appl h_r ih₁ ih₂ | pi h_r ih₁ ih₂ =>
    have h := h_r.complete
    dsimp only [infer]
    aesop
  case sigma ih =>
    dsimp only [infer]
    aesop
  case curr h_r₁ h_r₂ ih₁ ih₂ | coup h_r₁ h_r₂ ih₁ ih₂ ih₃
    | app h_r₁ _ h_r₂ ih₁ ih₂ =>
    have ha := h_r₁.complete
    have hb := h_r₂.complete
    dsimp only [infer]
    aesop
  case pair h_r₁ ih h_r₂ h_r₃ ih₃ ih₄ =>
    have ha := h_r₁.complete
    have hb := h_r₂.complete
    have hc := h_r₃.complete
    dsimp only [infer]
    aesop

instance : Decidable (Judge e t) :=
  if h : (infer e).isSome then
    if heq : ((infer e).get h).fst = t then
      .isTrue (heq ▸ ((infer e).get h).snd.down)
    else
      isFalse (fun h => by simp [h.complete] at *)
  else
    isFalse (fun h => by simp [h.complete] at *)

end Expr
