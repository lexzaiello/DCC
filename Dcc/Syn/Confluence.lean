import Dcc.Syn.JudgePi

open Expr

/-
This is a parallel "single-step" reducer for my SK-like calculus.
It is kind of halfway between normalization and single-step reduction.
Useful for checking definitional equality.

I have proven it to coincide with my definition of ParRed.
-/

inductive Reduction.app : Expr → Expr → Prop
  | mk : ParRed f f' → ParRed x x' → Reduction.app ⸨f x⸩ ⸨f' x'⸩

inductive Reduction.pi : Expr → Expr → Prop
  | mk : ParRed α α' → ParRed β β' → Reduction.pi ((Π' m) α, β) ((Π' m) α', β')

inductive Reduction.red : Expr → Expr → Prop
  | mk : ParRed e' e'' → Red e e' → Reduction.red e e''

inductive Reduction.refl : Expr → Expr → Prop
  | mk : Atom e  → Reduction.refl e e

inductive Reduction : Expr → Expr → Prop
  | app'  : (Reduction.app e ⸨f' x'⸩) → Reduction e ⸨f' x'⸩
  | pi'   : (Reduction.pi e ((Π' m) α', β')) → Reduction e ((Π' m) α', β')
  | red'  : (Reduction.red e e') → Reduction e e'
  | refl' : (Reduction.refl e e') → Reduction e e'

structure Reduces (e e' : Expr) where
  hpar  : ParRed e e'
  hkind : Reduction e e'

syntax "obvious" term : tactic
macro_rules
  | `(tactic| obvious $e:term $heq:term) => `(tactic|
    refine ⟨$e, ?_⟩
    rw [$heq]
    constructor
    constructor
    exact ParRed.refl
    exact Reduction.refl' (.mk (by simp)))

def gen (e : Expr) : ((e' : Expr) × (PLift (Reduces e e'))) :=
  match heq : e with
  | .K' m n | .K m n | .S m n o | .I m | Srt m | .next | .read | .assert | .app' | _? => by
    refine ⟨e, ?_⟩
    rw [heq]
    constructor
    constructor
    exact ParRed.refl
    exact Reduction.refl' ⟨by simp⟩
  | ⸨⸨(.I _m) _α⸩ x⸩ =>
    ⟨x, ⟨⟨.I .refl, .red' ⟨.refl, .I⟩⟩⟩⟩
  | ⸨(.K _m _n) _α _β x _y⸩ =>
    ⟨x, ⟨.K .refl, .red' ⟨.refl, .K⟩⟩⟩
  | ⸨(.K' _m _n) _α _β x _y⸩ =>
    ⟨x, ⟨.K' .refl, .red' ⟨.refl, .K'⟩⟩⟩
  | ⸨(.S _m _n _o) _α _β _γ x y z⸩ =>
    ⟨⸨⸨x z⸩ ⸨y z⸩⸩, ⟨.S .refl .refl .refl, .red' ⟨.app (.app .refl .refl) (.app .refl .refl), .S⟩⟩⟩
  | ⸨((Π' m) α, β) x⸩ =>
    ⟨((Π' m) ⸨α x⸩, ⸨β x⸩), ⟨.Pi .refl .refl .refl, .red' ⟨.Pival (.app .refl .refl) (.app .refl .refl), .Pi⟩⟩⟩
  | ((Π' m) α, β) =>
    let ⟨α', ⟨⟨heq₁, _⟩⟩⟩ := gen α
    let ⟨β', ⟨⟨heq₂, _⟩⟩⟩ := gen β
    ⟨(Π' m) α', β', ⟨.Pival heq₁ heq₂, .pi' ⟨heq₁, heq₂⟩⟩⟩
  | ⸨.next f _x⸩ =>
    ⟨f, ⟨.next .refl, .red' ⟨.refl, .next⟩⟩⟩
  | ⸨.read e⸩ =>
    ⟨e, ⟨.read .refl, .red' ⟨.refl, .read⟩⟩⟩
  | ⸨.assert f _x⸩ =>
    ⟨f, ⟨.assert .refl, .red' ⟨.refl, .assert⟩⟩⟩
  | ⸨${π} f g x⸩ =>
    ⟨⸨π ⸨f x⸩ ⸨g x⸩⸩,
      ⟨.app' .refl .refl .refl, .red' ⟨.app (.app .refl (.app .refl .refl)) (.app .refl .refl), .app'⟩⟩⟩
  | ⸨f x⸩ =>
    let ⟨f', ⟨⟨heq₁, c⟩⟩⟩ := gen f
    let ⟨x', ⟨⟨heq₂, c⟩⟩⟩ := gen x

    ⟨⸨f' x'⸩, ⟨.app heq₁ heq₂, .app' ⟨heq₁, heq₂⟩⟩⟩

def Atom.gen (e : Expr) : Atom e ∨ (∃ f x, e = ⸨f x⸩) ∨ (∃ m α β, e = (Π' m) α, β) :=
  match e with
  | (.I _m) => .inl <| .comb .I₀
  | (.K _m _n) => .inl <| .comb .K₀
  | (.K' _m _n) => .inl <| .comb .K'₀
  | (.S _m _n _o) => .inl <| .comb .S₀
  | .next => .inl <| .comb .next₀
  | .app' => .inl <| .comb .app'₀
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

/-def gen (e : Expr) : ((e' : Expr) × (PLift <| (((∃ f x f' x', ParRed e ⸨f' x'⸩ ∧ e = ⸨f x⸩)
  ∨ (∃ m α β α' β', ParRed e ((Π' m) α', β')  ∧ e = (Π' m) α, β))
  ∨ (Red e e') ∨ (e' = e)) ∧ (ParRed e e'))) :=
  match e with
  | .K' m n => sorry
  | .K m n
  | .S m n o
  | .I m
  | Srt m
  | .next
  | .read
  | .assert
  | .app'
  | _? => ⟨⟨_, ⟨.inr (.inr rfl)⟩⟩, by sorry⟩
  | ⸨(.I _m) _α x⸩ => ⟨x, ⟨.inr (.inl (.I))⟩⟩
  | ⸨(.K _m _n) _α _β x _y⸩ => ⟨x, ⟨.inr (.inl .K)⟩⟩
  | ⸨(.K' _m _n) _α _β x _y⸩ => ⟨x, ⟨.inr (.inl .K')⟩⟩
  | ⸨(.S _m _n _o) _α _β _γ x y z⸩ => ⟨⸨⸨x z⸩ ⸨y z⸩⸩, ⟨.inr (.inl .S)⟩⟩
  | ⸨((Π' _m) α, β) x⸩ => ⟨⟨_, ⟨.inr (.inl .Pi)⟩⟩, by sorry⟩
  | ((Π' m) α, β) =>
    let ⟨α', h₁⟩ := α.gen
    let αp := h₁.down.right
    let ⟨β', h₂⟩ := β.gen
    let βp := h₂.down.right
    ⟨_, ⟨.inl (.inr sorry)⟩, .Pi h₁ h₂⟩
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
    ⟨⸨innerx innery⸩, ⟨.app pinner₁.down pinner₂.down⟩⟩-/

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

theorem Red.gen_complete (h : Red e e') : (gen e).fst = e' := by
  induction h
  repeat (unfold gen; rfl)

def gen.sound : (gen e).fst = e' → ParRed e e' := fun h => by
  rw [← h]
  exact (gen e).snd.down.hpar

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

theorem gen.max (p : ParRed e e') : ParRed e' (gen e).fst := by
  match p.step_whole_or_parts_refl with
  | .inl h =>
    
    sorry
  | .inr h => sorry
  /-match heq : Atom.gen e with
  | .inl h =>
    apply gen.sound
    rw [no_step_atom p h]
  | .inr (.inl ⟨f, x, heq⟩) =>
    
    
    sorry
  | .inr (.inr h) => sorry-/

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

theorem confluence : ParRed a b → ParRed a c → ∃ d, ParRed b d ∧ ParRed c d := by
  sorry

