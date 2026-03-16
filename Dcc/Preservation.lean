import Dcc.Ast
import Dcc.Eval
import Dcc.Judge
import Dcc.Tactic

theorem DefEq.congr_left : DefEq f f' → DefEq ⸨f x⸩ ⸨f' x⸩ := by
  intro hf
  if h : ∃ D, ParRed ⸨f x⸩ D ∧ ParRed ⸨f' x⸩ D then
    exact DefEq.step h
  else
    apply DefEq.congr h hf DefEq.refl

theorem DefEq.congr_right : DefEq x x' → DefEq ⸨f x⸩ ⸨f x'⸩ := by
  intro hx
  if h : ∃ D, ParRed ⸨f x⸩ D ∧ ParRed ⸨f x'⸩ D then
    exact DefEq.step h
  else
    apply DefEq.congr h DefEq.refl hx

theorem DefEq.congr' : DefEq f f' → DefEq x x' → DefEq ⸨f x⸩ ⸨f' x'⸩ := by
  intro hf hx
  if h : ∃ D, ParRed ⸨f x⸩ D ∧ ParRed ⸨f' x'⸩ D then
    exact DefEq.step h
  else
    apply DefEq.congr h hf hx

theorem RunPi.weak_stable : RunPi arg t t' → ParRed arg arg' → ∃ t'', RunPi arg' t t'' := fun _ _ =>
  ⟨_, RunPi.sound rfl⟩

theorem inv_app : Judge β' ⸨f x⸩ → ∃ m α α₂ β, RunPi x β β' ∧ Judge (Π.{[m]} α, β) f ∧ Judge α₂ x ∧ DefEq α α₂ := by
  intro h
  cases h
  rename_i m α₁ β α₂ hdq h_t_f h_t_x hr
  exact ⟨m, α₁, α₂, β, hr, h_t_f, h_t_x, hdq⟩

theorem preservation' : Judge t e → ParRed e e' → Judge t e' := by
  intro ht hdq
  induction hdq generalizing t
  case k x x' m n α β y hp ih =>
    repeat cases_spine
    rename_i hpr _
    cases_conv
    cases_spine
    simp_all
    cases_spine *
    cases_spine *
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    cases_spine *
    contra_binder
    rename_i hpr _ _ _ _
    have h := hpr.complete
    simp [run_pi] at h
    split at h
    binder_contra
    simp at h
    smart_reduce change_all
    
    smart_reduce show reduce (((((Expr.comb Comb.app').app ((Expr.comb Comb.app').app (Expr.comb Comb.read))).app ((Expr.comb Comb.next).app (Expr.comb Comb.next))).app
              ((Expr.comb Comb.next).app ((Expr.comb Comb.next).app (Expr.comb Comb.read)))).app
          α)
    · rename_i hnb _
      exfalso
      exact hnb (by exact Binder.mk)
    · 
      sorry
  sorry

theorem preservation : Judge t e → ParRed e e' → Judge t e' := by
  intro ht hdq
  induction ht generalizing e'
  · cases hdq
    exact Judge.K
  · cases hdq
    exact Judge.K'
  · cases hdq
    exact Judge.S
  · cases hdq
    exact Judge.Srt
  · cases hdq
    exact Judge.Pi
  · cases hdq
    repeat cases_spine
    reduce_equations
    rename_i x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    have h : (_root_.reduce x).fst = e' := by
      assumption
    rw [← h]
    rename_i ih _ _ _ _ ih₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    have h  := ih (by sorry)
    sorry
