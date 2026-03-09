import Dcc.Syn.JudgePi

theorem Whnf.no_step : Whnf e → ¬ ∃ e', Red e e' := by
  intro h
  cases h
  repeat (intro ⟨e', hstep⟩; contradiction)

theorem Whnf.left : Whnf ⸨f x⸩ → Whnf f := by
  intro h
  cases h
  exact Whnf.I₀
  exact Whnf.K₀
  exact Whnf.K₁
  exact Whnf.K₂
  exact Whnf.K'₀
  exact Whnf.K'₁
  exact Whnf.K'₂
  exact Whnf.S₀
  exact Whnf.S₁
  exact Whnf.S₂
  exact Whnf.S₃
  exact Whnf.S₄
  exact Whnf.next₀
  exact Whnf.assert₀
  exact Whnf.app'₀
  exact Whnf.app'₁
  exact Whnf.app'₂

theorem step_left_or_whole : Red ⸨f x⸩ e' → (∃ f', Red f f' ∧ e' = ⸨f' x⸩) ∨ Whnf f := by
  intro h_step
  cases h_step
  exact Or.inr Whnf.I₁
  exact Or.inr Whnf.K₃
  exact Or.inr Whnf.K'₃
  exact Or.inr Whnf.S₅
  exact Or.inr Whnf.Pi
  exact Or.inr Whnf.next₁
  exact Or.inr Whnf.read
  exact Or.inr Whnf.assert₁
  exact Or.inr Whnf.app'₃

theorem step_whole : Red ⸨f x⸩ e' → Whnf f ∨ Whnf ⸨f x⸩ := by
  intro h_r
  cases h_r
  exact Or.inl Whnf.I₁
  exact Or.inl Whnf.K₃
  exact Or.inl Whnf.K'₃
  exact Or.inl Whnf.S₅
  exact Or.inl Whnf.Pi
  exact Or.inl Whnf.next₁
  exact Or.inl Whnf.read
  exact Or.inl Whnf.assert₁
  exact Or.inl Whnf.app'₃
