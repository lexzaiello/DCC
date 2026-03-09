import Dcc.Syn.JudgePi

open Expr

/-
This is a parallel "single-step" reducer for my SK-like calculus.
It is kind of halfway between normalization and single-step reduction.
Useful for checking definitional equality.

I have proven it to coincide with my definition of ParRed.
-/

def Atom.gen (e : Expr) : Atom e ∨ (∃ f x, e = ⸨f x⸩) ∨ (∃ m α β, e = (Π' m) α, β) :=
  match e with
  | (I _m) => .inl <| .comb .I₀
  | (K _m _n) => .inl <| .comb .K₀
  | (K' _m _n) => .inl <| .comb .K'₀
  | (S _m _n _o) => .inl <| .comb .S₀
  | next => .inl <| .comb .next₀
  | $ => .inl <| .comb .app'₀
  | .read => .inl <| .comb .read
  | .assert => .inl <| .comb .assert₀
  | .Srt _m => .inl .Srt
  | _? => .inl .hole
  | ⸨f x⸩ => .inr (.inl ⟨f, x, rfl⟩)
  | (Π' m) α, β => .inr (.inr ⟨m, α, β, rfl⟩)

def Atom.sound (_h : Atom.gen e = .inl h_atom) : Atom e :=
  match heq : Atom.gen e with
  | .inl h => h
  | _ => by simp_all

def Atom.sound' (_heq : Atom.gen e = .inr h_not_atom) : (¬ Atom e) := by
  simp_all
  match h_not_atom with
  | .inl ⟨f, x, heq⟩ | .inr ⟨m, α, β, heq⟩ =>
    intro hat
    match hat with
    | .comb h =>
      cases h
      repeat contradiction
    | .Srt =>
      contradiction

def Atom.complete (h : Atom e) : (Atom.gen e = .inl h) := by
  induction h
  repeat rfl

def gen (e : Expr) : ((e' : Expr) × (PLift (ParRed e e'))) :=
  match e with
  | .K' m n => ⟨.K' m n, ⟨ParRed.refl_K'⟩⟩
  | .K m n => ⟨.K m n, ⟨ParRed.refl_K⟩⟩
  | .S m n o => ⟨.S m n o, ⟨ParRed.refl_S⟩⟩
  | .I m => ⟨.I m, ⟨ParRed.refl_I⟩⟩
  | _? => ⟨_?, ⟨.refl_hole⟩⟩
  | Srt m => ⟨Srt m, ⟨.refl_Srt⟩⟩
  | .next => ⟨.next, ⟨.refl_next⟩⟩
  | .read => ⟨.read, ⟨.refl_read⟩⟩
  | .assert => ⟨.assert, ⟨.refl_assert⟩⟩
  | .app' => ⟨.app', ⟨.refl_app'⟩⟩
  | ⸨(.I _m) _α x⸩ =>
    let ⟨inner, pinner⟩ := gen x
    ⟨inner, ⟨.I pinner.down⟩⟩
  | ⸨(.K _m _n) _α _β x _y⸩ =>
    let ⟨inner, pinner⟩ := gen x
    ⟨inner, ⟨.K pinner.down⟩⟩
  | ⸨(.K' _m _n) _α _β x _y⸩ =>
    let ⟨inner, pinner⟩ := gen x
    ⟨inner, ⟨.K' pinner.down⟩⟩
  | ⸨(.S _m _n _o) _α _β _γ x y z⸩ =>
    let ⟨_inner_x, pinner₁⟩ := gen x
    let ⟨_inner_y, pinner₂⟩ := gen y
    let ⟨_inner_z, pinner₃⟩ := gen z
    ⟨_, ⟨.S pinner₁.down pinner₂.down pinner₃.down⟩⟩
  | ⸨((Π' _m) α, β) x⸩ =>
    let ⟨_inner_x, pinner₁⟩ := gen α
    let ⟨_inner_y, pinner₂⟩ := gen β
    let ⟨_inner_z, pinner₃⟩ := gen x
    ⟨_, ⟨.Pi pinner₁.down pinner₂.down pinner₃.down⟩⟩
  | ((Π' m) α, β) =>
    let ⟨inner_x, pinner₁⟩ := gen α
    let ⟨inner_y, pinner₂⟩ := gen β
    ⟨((Π' m) inner_x, inner_y), ⟨.Pival pinner₁.down pinner₂.down⟩⟩
  | ⸨.next f _x⸩ =>
    let ⟨inner, pinner⟩ := gen f
    ⟨inner, ⟨.next pinner.down⟩⟩
  | ⸨.read e⸩ =>
    let ⟨inner, pinner⟩ := gen e
    ⟨inner, ⟨.read pinner.down⟩⟩
  | ⸨.assert f _x⸩ =>
    let ⟨inner, pinner⟩ := gen f
    ⟨inner, ⟨.assert pinner.down⟩⟩
  | ⸨${_π} f g x⸩ =>
    let ⟨_innerx, pinner₁⟩ := gen f
    let ⟨_innery, pinner₂⟩ := gen g
    let ⟨_innerx, pinner₃⟩ := gen x
    ⟨_, ⟨.app' pinner₁.down pinner₂.down pinner₃.down⟩⟩
  | ⸨f x⸩ =>
    let ⟨innerx, pinner₁⟩ := gen f
    let ⟨innery, pinner₂⟩ := gen x
    ⟨⸨innerx innery⸩, ⟨.app pinner₁.down pinner₂.down⟩⟩

def diamond (h₁ : (gen a).fst = b) (h₂ : (gen a).fst = c) :
  ((d : Expr) × (PLift ((gen b).fst = d)) × (PLift ((gen c).fst = d))) := by
  let d := gen b
  refine ⟨d.fst, ?_, ?_⟩
  exact ⟨rfl⟩
  change PLift (_ = (gen b).fst)
  rw [← h₂, ← h₁]
  exact ⟨rfl⟩

def ParRed.transport_atom (h₁ : ParRed a b) (h₂ : Atom a) : (gen a).fst = b := by
  cases h₂ with
  | comb h => cases h <;> cases h₁ <;> unfold gen <;> rfl
  | _ => cases h₁; unfold gen; rfl

-- need to make cases for ParRed.
theorem gen.mono : ParRed a b → ParRed b (gen a).fst := by
  sorry

theorem gen.sound : (gen e).fst = e' → ParRed e e' := by
  intro h
  let h' := gen e
  let x := h'.fst
  let p := h'.snd
  rw [h] at p
  exact p.down

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
  match Atom.gen e with
  | .inl h=> .inr <| .inr <| no_step_atom h_r h
  | .inr (.inl ⟨f, x, heq⟩) => by
    
    sorry
  | .inr (.inr ⟨m, α, β, heq⟩) =>
    sorry

theorem Red.diamond (h_r : Red a b) (h_r₂ : ParRed a c) : ∃ d, ParRed b d ∧ ParRed c d := by
  
  
  sorry

theorem gen.com : ParRed f f' → ParRed x x' → ParRed (f'.app x') (gen (f.app x)).fst := by
  intro h_f h_x
  unfold gen
  
  sorry

@[simp] theorem gen.get_trivial (_h : (gen a).fst = b) : ∃ b, ParRed a b ∧ ParRed a b := by
  exact ⟨(gen a).fst, (gen a).snd.down, (gen a).snd.down⟩

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

theorem single_step_unique : Red e e₁ → Red e e₂ → e₁ = e₂ := by
  intro h₁ h₂
  induction h₁
  repeat (cases h₂; rfl)

namespace ParRed

theorem inv (h : ParRed ⸨f x⸩ e') : ∃ f' x', (ParRed f f' ∧ ParRed x x' ∧ ParRed ⸨f' x'⸩ e') := by
  cases h
  rename_i hx
  exact ⟨_, e', .refl, hx, .I .refl⟩
  rename_i hx
  exact ⟨_, x, .refl, .refl, .K hx⟩
  rename_i hx
  exact ⟨_, x, .refl, .refl, .K' hx⟩
  rename_i hx
  exact ⟨_, x, .refl, .refl, .S (by assumption) (by assumption)⟩
  rename_i hx
  exact ⟨_, x, .refl, .refl, .Pi (by assumption) (by assumption)⟩
  rename_i hx
  exact ⟨_, x, .refl, .refl, .next hx⟩
  rename_i hx
  exact ⟨_, x, .refl, .refl, .read hx⟩
  rename_i hx
  exact ⟨_, x, .refl, .refl, .assert hx⟩
  rename_i hx
  exact ⟨_, x, .refl, .refl, .app' (by assumption) (by assumption)⟩
  · rename_i f' x' h_f' h_x'
    exact ⟨f', x', h_f', h_x', .refl⟩

theorem par_app (h : ParRed ⸨f x⸩ e₁) : (∃ e₂, Red ⸨f x⸩ e₂ ∧ ParRed e₂ e₁) ∨ (∃ f' x', ParRed f f' ∧ ParRed x x' ∧ e₁ = ⸨f' x'⸩) := by
  cases h
  exact Or.inl ⟨_, Red.I, by assumption⟩
  exact Or.inl ⟨_, Red.K, by assumption⟩
  exact Or.inl ⟨_, Red.K', by assumption⟩
  exact Or.inl ⟨_, Red.S, .app (by assumption) (by assumption)⟩
  exact Or.inl ⟨_, Red.Pi, .Pival (by assumption) (by assumption)⟩
  exact Or.inl ⟨_, Red.next, by assumption⟩
  exact Or.inl ⟨_, Red.read, by assumption⟩
  exact Or.inl ⟨_, Red.assert, by assumption⟩
  exact Or.inl ⟨_, Red.app', .app (.app .refl (by assumption)) (by assumption)⟩
  · rename_i f' x' h_f h_x
    right
    exact ⟨f', x', h_f, h_x, rfl⟩

theorem multi_step_unique : ParRed e e₁ → ParRed e e₂ → (∃ e', ParRed e₁ e' ∧ ParRed e₂ e') := by
  intro h₁ h₂
  induction e generalizing e₁ e₂
  · cases h₁
    cases h₂
    exact ⟨_, ParRed.refl, ParRed.refl⟩
  · rename_i m a₁ a₂ ih₁ ih₂
    cases h₁
    cases h₂
    rename_i _ _ ha₁ ha₂ _ _ ha₃ ha₄
    have ⟨e, ha, hb⟩ := ih₁ ha₁ ha₃
    have ⟨e', ha', hb'⟩ := ih₂ ha₂ ha₄
    exact ⟨((Π' m)e, e'), .Pival ha ha', .Pival hb hb'⟩
  repeat (cases h₁; cases h₂; exact ⟨_, ParRed.refl, ParRed.refl⟩)
  · rename_i a b ih₁ ih₂
    match h₁.par_app with
    | .inl ⟨e₄, hr, heq⟩ =>
      have hb := h₂.par_app
      
      sorry
    | .inr ⟨f', x', h_p_f', h_p_x', h_eq₁⟩ =>
      match h₂.par_app with
      | .inr ⟨f'₁, x'₁, h_p_f'₁, h_p_x'₁, h_eq₂⟩ =>
        cases h_eq₁
        cases h_eq₂
        
        sorry
      | _ => sorry

end ParRed

theorem confluence : ParRed a b → ParRed a c → ∃ d, ParRed b d ∧ ParRed c d := by
  sorry

