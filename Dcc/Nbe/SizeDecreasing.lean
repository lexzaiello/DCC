import Dcc.Nbe.Value
import Dcc.Nbe.Size

namespace Semantic

mutual

@[grind ., grind! .]
theorem Val.measure_pos_tm : 0 < Val.measure Val(neutral(tm(x))) := by
  cases x
  any_goals (grind)

@[grind ., grind! .]
theorem Val.measure_pos_lam : 0 < Val.measure Val(λ env n => bdy) := by
  unfold Val.measure
  split
  · grind
  · grind

@[grind ., grind! .]
theorem Val.measure_pos_pi : 0 < Val.measure Val(Π (f_α) n env, f_β) := by
  grind

@[grind ., grind! .]
theorem Val.measure_pos_not_var (hn_var : ¬ ∃ (v : ℕ) (τ : Val), e ≠ Val(neutral(var((v) : τ)))) : 0 < Val.measure e := by
  cases e
  any_goals (grind)
  case neut nv =>
    cases nv with
    | var _ τ =>
      dcc_simp_all
      rename_i idx
      have h := hn_var idx.succ Val(neutral(Coup(τ)))
      omega
    | tm tm =>
      grind

/-@[grind ., grind! .]
theorem NeutralTm.size_pos : 0 < NeutralTm.size x := by
  cases x
  any_goals (grind)
  case app f v =>
    unfold NeutralTm.size
    cases f
    case var => simp
    case tm tm =>
      have h := tm.size_pos
      grind
  case quot β x =>
    simp [NeutralTm.size]
    
    sorry

@[grind ., grind! .]
theorem Val.size_pos (_h_neq : ¬ ∃ n τ, x = Val(neutral(var((n) : τ)))) : 0 < Val.size x := by
  cases x
  any_goals (grind)
  case neut n =>
    unfold Val.size
    cases n with
    | var =>
      simp_all
    | tm tm =>
      have h := tm.size_pos
      grind

@[grind ., grind! .]
theorem Val.measure_pos (_h_neq : ¬ ∃ n τ, x = Val(neutral(var((n) : τ)))) : 0 < Val.size x := by
  cases x
  any_goals (grind)
  case neut nv =>
    cases nv
    · simp_all
    · grind-/

end

@[grind ., grind! ., dcc_size]
theorem Val.size_le_measure : Val.size x ≤ Val.measure x := by
  cases x
  any_goals (grind)
  case pi env arity f_α f_β =>
    have ha := f_α.size_le_measure
    have hb := f_β.size_le_measure
    grind

@[grind ., grind! .]
theorem Val.neut_measure_eq_size : Neutral(v).size = Val(neutral(v)).measure := by
  grind

@[grind ., grind! .]
theorem Neutral.app_x_measure_lt : x.measure < Neutral(f x).size := by
  cases f with
  | var =>
    unfold Neutral.size
    unfold NeutralTm.size
    grind
  | tm tm =>
    unfold Neutral.size
    unfold NeutralTm.size
    grind

@[grind ., grind! .]
theorem Neutral.app_f_size_lt : f.size < Neutral(f x).size := by
  conv =>
    right
    unfold Neutral.size
    unfold NeutralTm.size
    rfl
  cases f with
  | var => grind
  | tm tm =>
    grind

@[grind ., grind! .]
theorem Neutral.var_zero_size : Neutral(var((_v) : τ)).size = 0 := by
  grind

@[grind ., grind! .]
theorem Val.var_zero_size : Val(neutral(var((_v) : τ))).size = 0 := by
  grind

@[grind ., grind! .]
theorem Val.var_measure_zero : Val(neutral(var((_v) : τ))).measure = 0 := by
  grind

@[grind ., grind! .]
theorem Val.var_zero_measure : Val(neutral(var((_v) : τ))).measure = 0 := by
  grind

/-
f_α.measure + 3 + 1 + (env.measure + env.measure + env.measure + 2 + 1) + 1 +
        (x.measure + x.measure + x.measure + 2 + 1) +
      1 <
    f_α.measure + 3 + 1 + 1 + 1 + (env.measure + env.measure + env.measure + 2 + 1) +
      (x.measure + x.measure + x.measure + 2 + 1)

after:
  - f_α = 1
  - x = 3
  - env = 3
  - const = 11
before:
  - f_α = 1
  - env = 3
  - x = 3
  - const = 12
-/

@[dcc_size]
theorem Apply.decreasing (h : Apply f x e') : e'.measure < f.measure + x.measure := by
  induction h
  any_goals (grind)

#check Apply.decreasing

end Semantic
