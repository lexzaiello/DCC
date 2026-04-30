import Dcc.Judge
import Dcc.Ast
import Dcc.Relation

namespace Expr

@[dcc_judge] theorem match_arrow : arrow.matcher (DCC (α : Sort m) → β) = .some ⟨α, β, m, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem match_f_β : fst.f_β.type.matcher (fst.f_β.type α δ m n o) = .some ⟨α, δ, m, n, o, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem match_pair_β : pair.β.type.matcher (pair.β.type α m n) α m = .some ⟨n, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem match_curr_β_type : curr.β.type.matcher (curr.β.type α m n) = .some ⟨α, m, n, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem with_arr_arr : with_arr (.some ⟨arrow α β m, h⟩) = .some ⟨arrow α β m, α, β, m, h, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem with_fst_fβ_fβ : with_fst_fβ_type (.some ⟨fst.f_β.type α δ m n o, h⟩) = .some ⟨fst.f_β.type α δ m n o, α, δ, m, n, o, h, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem with_pair_β_pair_β_type : with_pair_β_type (.some ⟨pair.β.type α m n, h⟩) α m = .some ⟨pair.β.type α m n, n, h, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem with_curr_β_type_curr_β_type : with_curr_β_type (.some ⟨curr.β.type α m n, h⟩) = .some ⟨curr.β.type α m n, α, m, n, h, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

theorem Judge.complete (h : Judge e t) : infer e = .some ⟨t, ⟨h⟩⟩ := by
  induction h <;> (dsimp only [infer]; try (simp_all [dcc_judge, dcc_reduce]; aesop (rule_sets := [DccReduce])))

instance Judge.instComplete : Complete (m := Option) (hR := Judge.instRel) := ⟨fun h _ => h.complete⟩

instance : Decidable (Judge e t) :=
  if h : (infer e).isSome then
    if heq : ((infer e).get h).fst = t then
      .isTrue (heq ▸ ((infer e).get h).snd.down)
    else
      isFalse (fun h => by simp [h.complete] at *)
  else
    isFalse (fun h => by simp [h.complete] at *)

end Expr
