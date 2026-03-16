import Dcc.Ast
import Dcc.Eval
import Dcc.Judge
import Dcc.Tactic

theorem RunPi.weak_stable : RunPi arg t t' → ParRed arg arg' → ∃ t'', RunPi arg' t t'' := fun _ _ =>
  ⟨_, RunPi.sound rfl⟩

theorem RunPi.stable : RunPi arg t t' → ParRed arg arg' → ∃ t'', RunPi arg' t t'' ∧ DefEq t' t'' := by
  intro h₁ h₂
  induction h₁ with
  | zero hnbind hpar =>
    cases hpar
    · refine ⟨_, RunPi.zero hnbind ?_, _, ParRed.reduce_sound rfl, ParRed.reduce_sound rfl⟩
      rename_i e' x m n α β h
      smart_reduce close reduction
    repeat sorry
  | succ => sorry
