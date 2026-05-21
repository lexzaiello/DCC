import Dcc.Judge
import Dcc.Ast
import Dcc.Relation
import Lean
import Qq

namespace Expr

@[dcc_judge] theorem match_arrow : arrow.matcher (DCC (α : Sort m) → β) = .some ⟨α, β, m, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem match_f_β : fst.f_β.type.matcher (fst.f_β.type α δ m n o) = .some ⟨α, δ, m, n, o, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem match_pair_β : pair.β.type.matcher (pair.β.type α m n) α m = .some ⟨n, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem match_curr_β_type : curr.β.type.matcher (curr.β.type f_α x_α m n) = .some ⟨f_α, x_α, m, n, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem with_arr_arr : with_arr (.some ⟨arrow α β m, h⟩) = .some ⟨arrow α β m, α, β, m, h, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem with_fst_fβ_fβ : with_fst_fβ_type (.some ⟨fst.f_β.type α δ m n o, h⟩) = .some ⟨fst.f_β.type α δ m n o, α, δ, m, n, o, h, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem with_pair_β_pair_β_type : with_pair_β_type (.some ⟨pair.β.type α m n, h⟩) α m = .some ⟨pair.β.type α m n, n, h, ⟨rfl⟩⟩ := by
  simp [dcc_judge]

@[dcc_judge] theorem with_curr_β_type_curr_β_type : with_curr_β_type (.some ⟨curr.β.type f_α x_α m n, h⟩) = .some ⟨curr.β.type f_α x_α m n, f_α, x_α, m, n, h, ⟨rfl⟩⟩ := by
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

attribute [dcc_force_reduce] reduce_all.eq_def reduce'.eq_def reduce.eq_def

syntax "dcc_reduce" name : tactic

/-open Qq Lean Elab Tactic Meta in elab "dcc_reduce" idt:name : tactic => do
  let lctx ← getLCtx
  let some decl ← (pure <| lctx.findFromUserName? idt.getName) | throwError "could not find goal"
  let ty := decl.type
  let ty' ← checkTypeQ (ty := q(Prop)) ty
  match ty' with
  | Q(
  --let some decl ← 
  let goal := 
  sorry-/

theorem canon_refl (h : Judge e (DCC (=(f_α) env x y))) : x = y := by
  match h with
  | .eq ht ⟨a, b, c, d⟩ =>
    have hc₁ := reduce_complete a b
    have hc₂ := reduce_complete c d
    simp [dcc_force_reduce] at *
    simp [dcc_reduce, dcc_force_reduce, RedRel.toRel.eq_def] at hc₁
    split at hc₁
    case h_1 ha heq =>
      split at heq
      case h_1 =>
        contradiction
      case h_2 heq' _ =>
        simp [dcc_force_reduce] at *
        have ⟨a, b⟩ := heq
        cases a
        cases b
        simp_all
        have ⟨a, b⟩ := hc₁
        cases a
        simp [RedRel.toRel.eq_def, RedEta.instRedRel] at hc₂
        simp_all
        split at hc₂
        case h_1 ha hb =>
          simp_all
          simp [RedAff.instRedRel, step?] at hb
          obtain ⟨hnf, -⟩ := hc₂
          
          sorry
          --simp [RedEta.instRedRel] at hc₂
        case h_2 =>
          sorry
  | _ => sorry

end Expr
