import Dcc.Syn.JudgePi

open Expr

/-
This is a parallel "single-step" reducer for my SK-like calculus.
It is kind of halfway between normalization and single-step reduction.
Useful for checking definitional equality.

I have proven it to coincide with my definition of ParRed.

Need some way to derive gen from ParRed.

number of steps.
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
  match e with
  | ⸨⸨(.I _m) _α⸩ x⸩ =>
    let ⟨x', ⟨hpar, _reda⟩⟩ := gen x
    ⟨x', ⟨⟨.I hpar, .red' ⟨hpar, .I⟩⟩⟩⟩
  | ⸨(.K _m _n) _α _β x _y⸩ =>
    let ⟨x', ⟨hpar, _redf⟩⟩ := gen x
    ⟨x', ⟨.K hpar, .red' ⟨hpar, .K⟩⟩⟩
  | ⸨(.K' _m _n) _α _β x _y⸩ =>
    let ⟨x', ⟨hpar, _redc⟩⟩ := gen x
    ⟨x', ⟨.K' hpar, .red' ⟨hpar, .K'⟩⟩⟩
  | ⸨(.S _m _n _o) _α _β _γ x y z⸩ =>
    let ⟨x', ⟨hpar₁, _redg⟩⟩ := gen x
    let ⟨y', ⟨hpar₂, _redf⟩⟩ := gen y
    let ⟨z', ⟨hpar₃, _rede⟩⟩ := gen z
    ⟨⸨⸨x' z'⸩ ⸨y' z'⸩⸩, ⟨.S hpar₁ hpar₂ hpar₃, .red' ⟨.app (.app hpar₁ hpar₃) (.app hpar₂ hpar₃), .S⟩⟩⟩
  | ⸨((Π' m) α, β) x⸩ =>
    let ⟨α', ⟨hpar₁, _reda⟩⟩ := gen α
    let ⟨β', ⟨hpar₂, _redb⟩⟩ := gen β
    let ⟨x', ⟨hpar₃, _redc⟩⟩ := gen x
    ⟨((Π' m) ⸨α' x'⸩, ⸨β' x'⸩), ⟨.Pi hpar₁ hpar₂ hpar₃, .red' ⟨.Pival (.app hpar₁ hpar₃) (.app hpar₂ hpar₃), .Pi⟩⟩⟩
  | ((Π' m) α, β) =>
    let ⟨α', ⟨⟨heq₁, _g⟩⟩⟩ := gen α
    let ⟨β', ⟨⟨heq₂, _h⟩⟩⟩ := gen β
    ⟨(Π' m) α', β', ⟨.Pival heq₁ heq₂, .pi' ⟨heq₁, heq₂⟩⟩⟩
  | ⸨.next f _x⸩ =>
    let ⟨f', ⟨⟨heq₁, _f⟩⟩⟩ := gen f
    ⟨f', ⟨.next heq₁, .red' ⟨heq₁, .next⟩⟩⟩
  | ⸨.read e⸩ =>
    let ⟨e', ⟨⟨heq₁, _e⟩⟩⟩ := gen e
    ⟨e', ⟨.read heq₁, .red' ⟨heq₁, .read⟩⟩⟩
  | ⸨.assert f _x⸩ =>
    let ⟨f', ⟨⟨heq₁, _d⟩⟩⟩ := gen f
    ⟨f', ⟨.assert heq₁, .red' ⟨heq₁, .assert⟩⟩⟩
  | ⸨${π} f g x⸩ =>
    let ⟨f', ⟨⟨heq₁, _a⟩⟩⟩ := gen f
    let ⟨g', ⟨⟨heq₂, _b⟩⟩⟩ := gen g
    let ⟨x', ⟨⟨heq₃, _c⟩⟩⟩ := gen x
    ⟨⸨π ⸨f' x'⸩ ⸨g' x'⸩⸩,
      ⟨.app' heq₁ heq₂ heq₃, .red' ⟨.app (.app .refl (.app heq₁ heq₃)) (.app heq₂ heq₃), .app'⟩⟩⟩
  | ⸨f x⸩ =>
    let ⟨f', ⟨⟨heq₁, _c⟩⟩⟩ := gen f
    let ⟨x', ⟨⟨heq₂, _c⟩⟩⟩ := gen x

    ⟨⸨f' x'⸩, ⟨.app heq₁ heq₂, .app' ⟨heq₁, heq₂⟩⟩⟩
  | K' m n => ⟨K' m n, ⟨.refl, .refl' ⟨Atom.comb .K'₀⟩⟩⟩
  | K m n => ⟨K m n, ⟨.refl, .refl' ⟨Atom.comb .K₀⟩⟩⟩
  | S m n o => ⟨S m n o, ⟨.refl, .refl' ⟨Atom.comb .S₀⟩⟩⟩
  | I m => ⟨I m, ⟨.refl, .refl' ⟨Atom.comb .I₀⟩⟩⟩
  | Srt m => ⟨Srt m, ⟨.refl, .refl' ⟨Atom.Srt⟩⟩⟩
  | .next => ⟨.next, ⟨.refl, .refl' ⟨Atom.comb .next₀⟩⟩⟩
  | .read => ⟨.read, ⟨.refl, .refl' ⟨Atom.comb .read⟩⟩⟩
  | .assert => ⟨.assert, ⟨.refl, .refl' ⟨Atom.comb .assert₀⟩⟩⟩
  | .app' => ⟨.app', ⟨.refl, .refl' ⟨Atom.comb .app'₀⟩⟩⟩
  | .hole => ⟨.hole, ⟨.refl, .refl' ⟨Atom.hole⟩⟩⟩

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

def gen.sound : (gen e).fst = e' → ParRed e e' := fun h => by
  rw [← h]
  exact (gen e).snd.down.hpar

theorem gen_imp_well_typed : Judge α x → (gen α).fst = β → Judge β x := fun h_t h_g =>
  Judge.conv h_t ⟨β, gen.sound h_g, .refl⟩

theorem gen_pi {m : Level} {α β x : Expr} : ∃ α' β', (gen ⸨((Π' m) α, β) x⸩).fst = ((Π' m) α', β') := by
  cases h₁ : (gen ⸨((Π' m) α, β) x⸩).fst with
  | _ =>
    unfold gen at h₁
    repeat split at h₁
    simp_all

inductive gen.eq : Expr → Expr → Prop
  | step  : (gen a).fst = b → gen.eq a b
  | trans : gen.eq a b → gen.eq b c → gen.eq a c

@[simp] theorem gen.eq.of_gen : (gen a).fst = b → gen.eq a b := gen.eq.step

def gen.n_norm (n : ℕ) (e : Expr) : ((e' : Expr) × (PLift <| gen.eq e e')) :=
  match n with
  | .zero => ⟨(gen e).fst, ⟨gen.eq.step (a := e) (b := (gen e).fst) rfl⟩⟩
  | .succ n =>
    if (gen e).fst == e then
      ⟨(gen e).fst, ⟨gen.eq.step (a := e) (b := (gen e).fst) rfl⟩⟩
    else
      let ⟨inner, ⟨h⟩⟩ := gen.n_norm n e
      ⟨(gen inner).fst, ⟨gen.eq.trans h (.step (b := (gen inner).fst) rfl)⟩⟩
