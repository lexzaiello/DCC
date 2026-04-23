import Dcc.CC.Judge2
import Dcc.CC.Ast

namespace Expr

@[simp] theorem match_arrow : arrow.matcher (DCC (α : Sort m) → β) = .some ⟨α, β, m, ⟨rfl⟩⟩ := by
  simp [arrow.matcher, arrow]

@[simp] theorem match_f_β : fst.f_β.type.matcher (fst.f_β.type α δ m n o) = .some ⟨α, δ, m, n, o, ⟨rfl⟩⟩ := by
  simp [fst.f_β.type.matcher, fst.f_β.type]

@[simp] theorem match_pair_β : pair.β.type.matcher (pair.β.type m n) = .some ⟨m, n, ⟨rfl⟩⟩ := by
  simp [pair.β.type.matcher, pair.β.type, coup.type, arrow]

@[simp] theorem match_curr_β_type : curr.β.type.matcher (curr.β.type α m n) = .some ⟨α, m, n, ⟨rfl⟩⟩ := by
  simp [curr.β.type.matcher, curr.β.type]

@[simp] theorem with_arr_arr : with_arr (.some ⟨arrow α β m, h⟩) = .some ⟨arrow α β m, α, β, m, h, ⟨rfl⟩⟩ := by
  simp [arrow, with_arr, arrow.matcher]

@[simp] theorem with_fst_fβ_fβ : with_fst_fβ_type (.some ⟨fst.f_β.type α δ m n o, h⟩) = .some ⟨fst.f_β.type α δ m n o, α, δ, m, n, o, h, ⟨rfl⟩⟩ := by
  simp [with_fst_fβ_type, fst.f_β.type.matcher, fst.f_β.type, arrow, arrow.matcher]

@[simp] theorem with_pair_β_pair_β_type : with_pair_β_type (.some ⟨pair.β.type m n, h⟩) = .some ⟨pair.β.type m n, m, n, h, ⟨rfl⟩⟩ := by
  simp [with_pair_β_type]

@[simp] theorem with_curr_β_type_curr_β_type : with_curr_β_type (.some ⟨curr.β.type α m n, h⟩) = .some ⟨curr.β.type α m n, α, m, n, h, ⟨rfl⟩⟩ := by
  simp [with_curr_β_type]

theorem Judge.complete (h : Judge e t) : infer e = .some ⟨t, ⟨h⟩⟩ := by
  induction h
  case top | bot | tintro | sort => dsimp only [infer]
  case subst₁ | pi | app | pair | quot | fst | snd | snd' | coup | comp | id | sigma =>
    dsimp only [infer]
    aesop
  case appl h_r₁ h_r₂ h_r₃ ih₁ ih₂ ih₃ =>
    have ha := h_r₁.complete
    have hb := h_r₂.complete
    have hc := h_r₃.complete
    dsimp only [infer]
    rw [ih₁, ih₂, ih₃, with_arr, match_arrow]
    cases hc
    cases ha
    dsimp
    split
    case isTrue heqa =>
      cases heqa
      dsimp only [with_app_γ_ty, App.type.t_γ.matcher]
      have h₁ := h_r₁.complete
      have h₂ := h_r₂.complete
      split
      case h_1 =>
        dsimp
        split
        case isTrue =>
          cases h₁
          dsimp [App.type.t_γ, mk_app_env, coup.type]
          dsimp only [App.type.t_γ, mk_app_env, coup.type] at hb
          
          sorry
      case h_2 =>
        sorry
  case subst₂ h_r₁ ih₁ =>
    dsimp only [infer]
    rw [ih₁]
    dsimp only [Subst₂.x.type, App.type.t_f, mk_app_env, coup.type]
    aesop
  case curr h_r₁ h_r₂ h_r₃ ih₁ ih₂ =>
    have ha := h_r₁.complete
    have hb := h_r₂.complete
    have hc := h_r₃.complete
    dsimp only [infer]
    simp [ih₁, ih₂]
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
