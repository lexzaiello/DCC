import Dcc.Syn.JudgePi
import Dcc.Syn.Gen

open Expr

theorem ParRed.step_whole_or_parts : ParRed ⸨f x⸩ e₂ →
  (∃ e₁, Red ⸨f x⸩ e₁ ∧ ParRed e₁ e₂) ∨ (∃ f' x', ParRed f f' ∧ ParRed x x')
  | I h_x=> .inl ⟨_, Red.I, h_x⟩
  | K h_x => .inl ⟨_, Red.K, h_x⟩
  | K' h_x => .inl ⟨_, Red.K', h_x⟩
  | S h_x h_y h_z => .inl ⟨_, Red.S, .app (.app h_x h_z) (.app h_y h_z)⟩
  | Pi h_α h_β h_x => .inl ⟨_, Red.Pi, .Pival (.app h_α h_x) (.app h_β h_x)⟩
  | next h_f => .inl ⟨_, Red.next, h_f⟩
  | read h_x => .inl ⟨_, Red.read, h_x⟩
  | assert h_x => .inl ⟨_, Red.assert, h_x⟩
  | app' h_f h_g h_x => .inl ⟨_, Red.app', .app (.app .refl (.app h_f h_x)) (.app h_g h_x)⟩
  | @ParRed.app f f' x x' h_f h_x => Or.inr ⟨f', x', h_f, h_x⟩

theorem no_step_atom : ParRed e e₂ → Atom e → e = e₂ := by
  intro h_r h_whnf
  cases h_whnf
  · rename_i a
    cases a
    repeat (cases h_r; rfl)
  · cases h_r
    rfl
  cases h_r
  rfl

theorem not_atom_has_parts (h : ¬ (Atom e)) : (∃ f x, e = ⸨f x⸩) ∨ (∃ m α β, e = (Π' m) α, β) :=
  match heq : Atom.gen e with
  | .inl h => by contradiction
  | .inr (.inl h) => .inl h
  | .inr (.inr h) => .inr h

theorem ParRed.step_whole_or_parts_refl : ParRed e e₂
  → (∃ e₁, Red e e₁ ∧ ParRed e₁ e₂)
    ∨ ((∃ f x f' x', ⸨f x⸩ = e ∧ ParRed f f' ∧ ParRed x x')
    ∨ (∃ m α β, e = (Π' m) α, β)) ∨ e = e₂ := fun h_r =>
  match heq : Atom.gen e with
  | .inl h=> .inr <| .inr <| no_step_atom h_r h
  | .inr (.inl h₁@⟨f, x, heq⟩) => by
    have h_not_at := Atom.sound' (h_not_atom := .inl h₁) (by simp)
    simp_all
    have h := ParRed.step_whole_or_parts h_r
    match h with
    | .inl h => exact Or.inl h
    | .inr ⟨f', x', pf, px⟩ =>
      exact Or.inr (Or.inl ⟨⟨f', pf⟩, ⟨x', px⟩⟩)
  | .inr (.inr ⟨m, α, β, heq⟩) => by simp_all

theorem Red.confluence : Red a b → Red a c → ∃ d, RedStar b d ∧ RedStar c d := by
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

theorem Red.single_step_unique : Red e e₁ → Red e e₂ → e₁ = e₂ := by
  intro h₁ h₂
  induction h₁
  repeat (cases h₂; rfl)

