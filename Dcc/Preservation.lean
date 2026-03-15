import Dcc.Ast
import Dcc.Eval
import Dcc.Judge
import Dcc.Tactic

theorem RunPi.stable : RunPi arg t t' → DefEq arg arg' → ∃ t'', RunPi arg' t t'' := by
  intro hrpi₁ hdq
  induction hrpi₁ with
  | zero => exact ⟨_, RunPi.sound rfl⟩
  | succ => exact ⟨_, RunPi.sound rfl⟩
