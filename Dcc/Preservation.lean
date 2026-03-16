import Dcc.Ast
import Dcc.Eval
import Dcc.Judge
import Dcc.Tactic

theorem DefEq.refl : DefEq e e := ⟨(_root_.reduce e).fst, (_root_.reduce e).snd.down, (_root_.reduce e).snd.down⟩

theorem DefEq.symm : DefEq e₁ e₂ → DefEq e₂ e₁ := fun ⟨D, h₁, h₂⟩ => ⟨D, h₂, h₁⟩

theorem DefEq.trans : DefEq a b → DefEq b c → DefEq a c := fun ⟨D₁, h₁, h₂⟩ ⟨D₂, h₂, h₃⟩ => by
  reduce_equations
  simp_all
  refine ⟨D₁, ?_, ?_⟩
  exact ParRed.reduce_sound (by assumption)
  exact ParRed.reduce_sound (by assumption)

theorem RunPi.weak_stable : RunPi arg t t' → ParRed arg arg' → ∃ t'', RunPi arg' t t'' := fun _ _ =>
  ⟨_, RunPi.sound rfl⟩

theorem RunPi.stable : RunPi arg t t' → ParRed arg arg' → ∃ t'', RunPi arg' t t'' ∧ DefEq t' t'' := by
  intro h₁ h₂
  induction h₁ with
  | zero hnbind hpar =>
    cases hpar
    repeat exact ⟨_, RunPi.zero hnbind (by smart_reduce close reduction), _, ParRed.reduce_sound rfl, ParRed.reduce_sound rfl⟩
    · rename_i x x' y y' z' m n o α β γ hx hy hz
      refine ⟨((x'.app (_root_.reduce z').fst).app (y'.app (_root_.reduce z').fst)), .zero hnbind ?_, ?_⟩
      · apply ParRed.s
        repeat assumption
        apply ParRed.reduce_sound
        have h : z' = arg' := by
          reduce_equations
          simp_all
        rw [h]
      · unfold DefEq
        
        sorry
    repeat sorry
  | succ => sorry
