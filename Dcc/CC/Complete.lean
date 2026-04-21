import Dcc.CC.Judge2
import Dcc.CC.Ast

namespace Expr

@[simp] theorem match_arrow : arrow.matcher (DCC (α : Sort m) → β) = .some ⟨α, β, m, ⟨rfl⟩⟩ := by
  simp [arrow.matcher, arrow]

@[simp] theorem match_f_β : fst.f_β.type.matcher (fst.f_β.type α δ m n o) = .some ⟨α, δ, m, n, o, ⟨rfl⟩⟩ := by
  simp [fst.f_β.type.matcher, fst.f_β.type]

@[simp] theorem match_pair_β : pair.β.type.matcher (pair.β.type α m n) = .some ⟨α, m, n, ⟨rfl⟩⟩ := by
  simp [pair.β.type.matcher, pair.β.type]
  split
  rfl

@[simp] theorem match_curr_β_type : curr.β.type.matcher (curr.β.type m n) = .some ⟨m, n, ⟨rfl⟩⟩ := by
  simp [curr.β.type.matcher, curr.β.type, coup.type, arrow]

@[simp 500] theorem match_coup : Coup.matcher (DCC Coup(m, α, β)) = .some ⟨m, α, β, ⟨rfl⟩⟩ := by
  simp [Coup.matcher, coup.type]

@[simp 500] theorem match_coup' : Coup.matcher (coup.type α β m) = .some ⟨m, α, β, ⟨rfl⟩⟩ := by
  simp [Coup.matcher, coup.type]

@[simp] theorem with_arr_arr : with_arr (.some ⟨arrow α β m, h⟩) = .some ⟨arrow α β m, α, β, m, h, ⟨rfl⟩⟩ := by
  simp [arrow, with_arr, arrow.matcher]

@[simp] theorem with_fst_fβ_fβ : with_fst_fβ_type (.some ⟨fst.f_β.type α δ m n o, h⟩) = .some ⟨fst.f_β.type α δ m n o, α, δ, m, n, o, h, ⟨rfl⟩⟩ := by
  simp [with_fst_fβ_type, fst.f_β.type.matcher, fst.f_β.type, arrow, arrow.matcher]

@[simp] theorem with_pair_β_pair_β_type : with_pair_β_type (.some ⟨pair.β.type α m n, h⟩) = .some ⟨pair.β.type α m n, α, m, n, h, ⟨rfl⟩⟩ := by
  simp [with_pair_β_type]

@[simp] theorem with_curr_β_type_curr_β_type : with_curr_β_type (.some ⟨curr.β.type m n, h⟩) = .some ⟨curr.β.type m n, m, n, h, ⟨rfl⟩⟩ := by
  simp [with_curr_β_type]

theorem Judge.complete (h : Judge e t) : infer e = .some ⟨t, ⟨h⟩⟩ := by
  induction h
  case sort => dsimp only [infer]
  case app | appl | pair | quot | fst | snd | snd' | coup | comp | id | sigma =>
    dsimp only [infer]
    aesop
  case pi h_r ih₁ ih₂ =>
    have ha := h_r.complete
    dsimp only [infer]
    simp [ih₁, ih₂, Pi.f_β.type, ha]
    aesop
  case curr h_r₁ h_r₂ h_r₃ ih₁ ih₂ =>
    have ha := h_r₁.complete
    have hb := h_r₂.complete
    have hc := h_r₃.complete
    dsimp only [infer]
    simp [ih₁, ih₂, hc, ha ▸ hb]
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
