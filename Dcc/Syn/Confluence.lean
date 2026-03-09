import Dcc.Syn.JudgePi

theorem no_step_atom : ParRed e e₂ → Atom e → e = e₂ := by
  intro h_r h_whnf
  cases h_whnf
  · rename_i a
    cases a
    repeat (cases h_r; rfl)
  · cases h_r
    rfl

theorem local_confluence : Red a b → Red a c → ∃ d, RedStar b d ∧ RedStar c d := by
  intro hb hc
  cases hb
  repeat (cases hc; exact ⟨_, RedStar.refl, RedStar.refl⟩)

theorem confluence_atom (h_atom : Atom a) (h_b : ParRed a b) (h_c : ParRed a c) : b = c := by
  induction h_b
  repeat (cases h_atom; rename_i h_comb; cases h_comb; cases h_c; rfl)
  cases h_atom
  rename_i h_comb
  cases h_comb
  repeat (cases h_atom; rename_i h; cases h)

/-
Exprs in whnf where ⸨f x⸩ ||-> ⸨f' x'⸩ must step ParRed f f' and ParRed x x'
-/
theorem whnf_step : Whnf ⸨f x⸩ → ParRed ⸨f x⸩ ⸨f' x'⸩ → ParRed f f' ∧ ParRed x x' := by
  intro h_wh h_app
  cases h_app
  repeat contradiction
  rename_i h_f h_x
  exact ⟨h_f, h_x⟩

theorem root_step : ¬ Whnf ⸨f x⸩ → 

theorem confluence' : ParRed a b → ParRed a c → ∃ d, ParRed b d ∧ ParRed c d := by
  intro h₁ h₂
  if ha : Atom a then
    have h := confluence_atom ha h₁ h₂
    exact ⟨c, by rw [h]; exact ParRed.refl, ParRed.refl⟩
  else if hb : Whnf a then
    sorry
  else
    
    sorry

theorem confluence : ParRed a b → ParRed a c → ∃ d, ParRed b d ∧ ParRed c d := by
  intro h₁ h₂
  induction h₁ generalizing c with
  | app e₁ e₂ ih₁ ih₂ =>
    cases h₂ with
    | app =>
      rename_i h_f h_x
      have ⟨d, ha, hb⟩ := ih₁ h_f
      have ⟨d₂, ha₂, hb₂⟩ := ih₂ h_x
      exact ⟨d.app d₂, ParRed.app ha ha₂, ParRed.app hb hb₂⟩
    | I =>
      rename_i x' _m _α h_c
      have ⟨d₁, haf, hbf⟩ := ih₁ e₁
      have ⟨dc, hac, hbc⟩ := ih₂ h_c
      refine ⟨d₁.app dc, .app haf hac, ?_⟩
      cases e₁
      have h := ParRed.app haf hac
      cases e₁
      rename_i h_i _
      have heq := no_step_atom h_i Atom.I₀
      rw [← heq] at h
      refine ⟨dc, ?_, hbc⟩
      rw [← heq]
      exact ParRed.I hac
    | K =>
      rename_i _m _n _α _β h_c
      cases e₁
      rename_i h_i _
      cases h_i
      rename_i h_i _
      cases h_i
      rename_i h_i _
      have heq := no_step_atom h_i Atom.K₀
      have ⟨d₁, h_x₃, h_x₃'⟩ := ih₂ e₂
      rename_i h_x₀ _ h_β f' x' h_α
      have ⟨d₁, haf, hbf⟩ := ih₁ (((ParRed.app ParRed.refl h_α).app h_β).app h_x₀)
      rename_i x'₁ _ _
      rw [← heq]
      cases heq
      cases hbf
      cases haf
      cases h_i
      rename_i h_k _
      cases h_k
      rename_i h_k₁ _ _
      cases h_k₁
      rename_i h_k
      cases h_k
      rename_i h_k _
      cases h_k
      
      rw [heq] at hbf
      have ⟨dc, hac, hbc⟩ := ih₂ e₂
      have h := ParRed.app haf hac
      rw [← heq] at h
      rename_i xa _ _ _ _ _ _
      refine ⟨d₁.app dc, ?_, ?_⟩
      rw [← heq]
      exact h
      
      apply ParRed.K
      exact ParRed.refl
      exact ParRed.I hac
      --have h_step := ParRed.K h_x (x := x₃) (x' := c) (_m := _m) (_n := _n) (_y := 
  | _ => sorry

/-theorem confluence : ParRed a b → ParRed a c → ∃ d, ParRed b d ∧ ParRed c d := by
  intro h₁ h₂
  induction h₁ generalizing c
  repeat exact ⟨_, h₂, ParRed.refl⟩
  · cases h₂
    · rename_i h_x ih h_c
      exact ih h_c
    · rename_i h_x ih _ _ h₂ h_x'
      cases h₂
      rename_i h₂ _
      cases h₂
      have ⟨d, ha, hb⟩ := ih h_x'
      refine ⟨d, ha, ParRed.I hb⟩
  · cases h₂
    · rename_i h_x ih
      exact  h_x ih
    · rename_i h_x ih f' x' h_k h_x'
      cases h_k
      rename_i h_k _
      cases h_k
      rename_i h_k _
      cases h_k
      rename_i h_k _
      cases h_k
      have ⟨d, ha, hb⟩ := ih h_x
      rename_i h_x₂ _ _ _ _
      have ⟨d₂, ha₂, hb₂⟩ := ih h_x₂
      exact ⟨d₂, ha₂, ParRed.K hb₂⟩
  · cases h₂
    · rename_i h_x ih
      exact  h_x ih
    · rename_i h_x ih f' x' h_k h_x'
      cases h_k
      rename_i h_k _
      cases h_k
      rename_i h_k _
      cases h_k
      rename_i h_k _
      cases h_k
      have ⟨d, ha, hb⟩ := ih h_x
      rename_i h_x₂ _ _ _ _
      have ⟨d₂, ha₂, hb₂⟩ := ih h_x₂
      exact ⟨d₂, ha₂, ParRed.K' hb₂⟩
  · cases h₂
    · rename_i h_x ih
      exact  h_x ih
    · rename_i hs _
      cases hs
      rename_i hs _
      cases hs
      rename_i hs _
      cases hs
      rename_i hs _
      cases hs
      rename_i hs _
      cases hs
      rename_i hs _
      cases hs
      rename_i x z y _ _ _ _ _ _ _ h ih _ _ _ _ _ _ _ _ _ _ _ _
      have ⟨d, ha, hb⟩ := ih h
      rename_i s' _ _ _ _ _ _ x'₅ a'₄ _ h₂ _ h₃ _ h₄ _ _ _ _
      have h_xz := ParRed.app h₃ a'₄
      have h_yz := ParRed.app h₂ a'₄
      have h_s  := ParRed.app h_xz h_yz
      have ⟨d, ha, hb⟩ := ih h_s
      exact ⟨d, ha, ParRed.S hb⟩
  · rename_i m α x β P' h_P' ih
    cases h₂
    rename_i h_c
    exact ih h_c
    rename_i f' x' α₁ α₂
    have h := ih h_P'
    cases α₁
    rename_i s_α s_β
    have ⟨d, ha, hb⟩ := ih (ParRed.Pival (.app s_α α₂) (.app s_β α₂))
    refine ⟨d, ha, ParRed.Pi hb⟩
  · rename_i α α' β β' m p_α p_β ih₁ ih₂
    cases h₂
    rename_i α'₂ β'₂ p_α' p_β'
    have ⟨d₁, h_α₁, h_α₂⟩ := ih₁ p_α
    have ⟨d₂, h_β₁, h_β₂⟩ := ih₂ p_β
    have ⟨d₃, h_α₃, h_α₄⟩ := ih₁ p_α'
    have ⟨d₄, h_β₃, h_β₄⟩ := ih₂ p_β'
    have ha : ParRed (Pi m α'₂ β'₂) (Pi m d₃ d₄) := ParRed.Pival (by assumption) (by assumption)
    have hb : ParRed (Pi m α' β') (Pi m d₃ d₄) := ParRed.Pival h_α₃ h_β₃
    exact ⟨_, hb, ha⟩
  · rename_i f f' _x h_f ih
    cases h₂
    · rename_i a
      exact ih a
    · rename_i f'' x' h_f' h_x'
      cases h_f'
      rename_i f'' x'' h_f'' h_x''
      cases h_f''
      have h := ih h_f
      have ⟨d, hd_f', hd_x''⟩ := ih h_x''
      have h := ParRed.next (f := x'') (_x := x') hd_x''
      exact ⟨d, hd_f', h⟩
  · rename_i e e' h_e' ih
    cases h₂
    · rename_i a
      exact ih a
    · rename_i f' x' h_f' h_x'
      cases h_f'
      have ⟨d, ha, hb⟩ := ih h_x'
      exact ⟨d, ha, ParRed.read hb⟩
  · rename_i e e' _x h_e' ih
    cases h₂
    · rename_i a
      exact ih a
    · rename_i f' x' h_f' h_x'
      cases h_f'
      · rename_i f'' x'' h_f' h_x''
        cases h_f'
        have ⟨d, ha, hb⟩ := ih h_x''
        have h := ParRed.assert hb (e' := d) (_x := x')
        exact ⟨d, ha, h⟩
  · rename_i π f x g P' h_P' ih
    cases h₂
    · rename_i a
      exact ih a
    · rename_i f' x' h_f' h_x'
      cases h_f'
      rename_i f'' x'' h_f'' h_x''
      cases h_f''
      rename_i f''' x''' h_f''' h_x'''
      cases h_f'''
      rename_i f'''' x'''' h_f'''' h_x''''
      cases h_f''''
      have h := (ParRed.app (.app h_x'''' (.app h_x''' h_x')) (.app h_x'' h_x'))
      have ⟨d, ha, hb⟩ := ih h
      exact ⟨d, ha, ParRed.app' hb⟩
  · rename_i f f' x x' h_f' h_x' ih₁ ih₂
    
    sorry-/

