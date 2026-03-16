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

theorem k_inv : Judge α ⸨K.{[m, n]} α β x y⸩ →
  Judge (Srt m) α ∧ Judge ((~> n.succ) α, (Srt n)) β ∧ Judge α x ∧ Judge ⸨β x⸩ y := by
  intro h
  repeat cases_spine
  rename_i hctx₁ hsrtα
  cases hctx₁
  · contra_binder
  rename_i hctx₁ hctx₂ _ _
  cases hctx₁
  · contra_binder
  simp_all
  

