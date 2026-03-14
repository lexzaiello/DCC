import Dcc.Ast
import Mathlib.Data.Nat.Notation

/-
- select innermost redex
  - can make inductive for this
- build expression back up with folding
-/

open Std (ToFormat Format)
open Std.ToFormat (format)

namespace Expr

inductive Redex : Expr → Prop where
  | k    : Redex ⸨K.{[_m, _n]} _α _β _x _y⸩
  | k'   : Redex ⸨K'.{[_m, _n]} _α _β _x _y⸩
  | s    : Redex ⸨S.{[_m, _n, _o]} _α _β _γ _x _y _z⸩
  | pi   : Redex ⸨(Π.{[_m]} _α, _β) _x⸩
  | next : Redex ⸨next _f _x⸩
  | read : Redex ⸨read _e⸩
  | app' : Redex ⸨$ _π _f _g _x⸩

inductive Redex' : Expr → Type where
  | k    : Redex' ⸨K.{[_m, _n]} _α _β _x _y⸩
  | k'   : Redex' ⸨K'.{[_m, _n]} _α _β _x _y⸩
  | s    : Redex' ⸨S.{[_m, _n, _o]} _α _β _γ _x _y _z⸩
  | pi   : Redex' ⸨(Π.{[_m]} _α, _β) _x⸩
  | next : Redex' ⸨next _f _x⸩
  | read : Redex' ⸨read _e⸩
  | app' : Redex' ⸨$ _π _f _g _x⸩

def is_redex (e : Expr) : Option (Redex' e) :=
  match e with
  | ⸨K.{[_m, _n]} _α _β _x _y⸩ => .some .k
  | ⸨K'.{[_m, _n]} _α _β _x _y⸩ => .some .k'
  | ⸨S.{[_m, _n, _o]} _α _β _γ _x _y _z⸩ => .some .s
  | ⸨(Π.{[_m]} _α, _β) _x⸩ => .some .pi
  | ⸨next _f _x⸩ => .some .next
  | ⸨read _e⸩ => .some .read
  | ⸨$ _π _f _g _x⸩ => .some .app'
  | _ => .none

theorem Redex'.sound : Redex' e → Redex e := fun h => by
  cases h
  · exact .k
  · exact .k'
  · exact .s
  · exact .pi
  · exact .next
  · exact .read
  · exact .app'

theorem is_redex.sound : is_redex e = .some p → e.Redex := fun _ => p.sound

instance Redex.instDecidable : Decidable (Redex e) := by
  match heq : is_redex e with
  | .some p => exact .isTrue p.sound
  | .none =>
    apply Decidable.isFalse
    intro h
    cases h
    repeat cases heq

theorem is_redex.sound' : is_redex e = Option.none → ¬ e.Redex := fun e => by
  intro h
  cases h
  repeat cases e

def eval (e : Expr) : Except Format Expr :=
  match e with
  | ⸨K.{[_m, _n]} _α _β x _y⸩ => pure x
  | ⸨K'.{[_m, _n]} _α _β x _y⸩ => pure x
  | ⸨S.{[_m, _n, _o]} _α _β _γ x y z⸩ => return ⸨⸨x z⸩ ⸨y z⸩⸩
  | ⸨(Π.{[m]} α, β) x⸩ => return Π.{[m]} ⸨α x⸩, ⸨β x⸩
  | ⸨next f _x⸩ => pure f
  | ⸨read e⸩ => pure e
  | ⸨$ π f g x⸩ => pure ⸨π ⸨f x⸩ ⸨g x⸩⸩
  | e => .error <| "stuck: " ++ (format e)

inductive Red : Expr → Expr → Prop
  | k      : Red ⸨K.{[m, n]} α β x y⸩ x
  | k'     : Red ⸨K'.{[m, n]} α β x y⸩ x
  | s      : Red ⸨S.{[m, n, o]} α β γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | pi     : Red ⸨(Π.{[m]} α, β) x⸩ (Π.{[m]} ⸨α x⸩, ⸨β x⸩)
  | next   : Red ⸨next f _x⸩ f
  | read   : Red ⸨read x⸩ x
  | app'   : Red ⸨$ π f g x⸩ ⸨π ⸨f x⸩ ⸨g x⸩⸩

theorem eval_sound : (eval e) = .ok e' → Red e e' := by
  intro h
  unfold eval at h
  split at h
  · cases h
    apply Red.k
  · cases h
    apply Red.k'
  · cases h
    apply Red.s
  · cases h
    apply Red.pi
  · cases h
    apply Red.next
  · cases h
    apply Red.read
  · cases h
    apply Red.app'
  · simp_all

theorem eval_complete : Red e e' → (eval e) = .ok e' := by
  intro h
  cases h
  repeat rfl

end Expr

inductive ParRed : Expr → Expr → Prop
  | k         : ParRed x x' → ParRed ⸨K.{[m, n]} α β x y⸩ x'
  | k'        : ParRed x x' → ParRed ⸨K'.{[m, n]} α β x y⸩ x'
  | s         : ParRed x x' → ParRed y y' → ParRed z z'
    → ParRed ⸨S.{[m, n, o]} α β γ x y z⸩ ⸨⸨x' z'⸩ ⸨y' z'⸩⸩
  | next      : ParRed f f' → ParRed ⸨next f x⸩ f'
  | read      : ParRed e e' → ParRed ⸨read e⸩ e'
  | pi        : ParRed α α' → ParRed β β' → ParRed x x'
    → ParRed ⸨(Π.{[m]} α, β) x⸩ (Π.{[m]} ⸨α' x'⸩, ⸨β' x'⸩)
  | app'      : ParRed π π' → ParRed f f'
    → ParRed g g' → ParRed x x'
    → ParRed ⸨$ π f g x⸩ ⸨π' ⸨f' x'⸩ ⸨g' x'⸩⸩
  | app       : (¬ ⸨f x⸩.Redex) → ParRed f f'
    → ParRed x x' → ParRed ⸨f x⸩ ⸨f' x'⸩
  | pi_val    : ParRed α α' → ParRed β β'
    → ParRed (Π.{[m]} α, β) (Π.{[m]} α', β')
  | refl_comb : ParRed (.comb c) (.comb c)
  | refl_srt  : ParRed (Srt m) (Srt m)

def reduce (e : Expr) : ((e' : Expr) × (PLift <| ParRed e e')) :=
  match heq : e.is_redex with
  | .some r => by
    cases r
    · rename_i m n α β x y
      let ⟨e', ⟨hp⟩⟩ := reduce x
      exact ⟨e', ⟨.k hp⟩⟩
    · rename_i m n α β x y
      let ⟨e', ⟨hp⟩⟩ := reduce x
      exact ⟨e', ⟨.k' hp⟩⟩
    · rename_i m n o α β γ x y z
      let ⟨x', ⟨hx⟩⟩ := reduce x
      let ⟨y', ⟨hy⟩⟩ := reduce y
      let ⟨z', ⟨hz⟩⟩ := reduce z
      exact ⟨⸨⸨x' z'⸩ ⸨y' z'⸩⸩, ⟨.s hx hy hz⟩⟩
    · rename_i m α β x
      let ⟨x', ⟨hx⟩⟩ := reduce x
      let ⟨α', ⟨hα⟩⟩ := reduce α
      let ⟨β', ⟨hβ⟩⟩ := reduce β
      exact ⟨(Π.{[m]} ⸨α' x'⸩, ⸨β' x'⸩), ⟨.pi hα hβ hx⟩⟩
    · rename_i f x
      let ⟨f', ⟨hf⟩⟩ := reduce f
      exact ⟨f', ⟨.next hf⟩⟩
    · rename_i e
      let ⟨e', ⟨he⟩⟩ := reduce e
      exact ⟨e', ⟨.read he⟩⟩
    · rename_i π f g x
      let ⟨π', ⟨hπ⟩⟩ := reduce π
      let ⟨f', ⟨hf⟩⟩ := reduce f
      let ⟨g', ⟨hg⟩⟩ := reduce g
      let ⟨x', ⟨hx⟩⟩ := reduce x
      exact ⟨⸨π' ⸨f' x'⸩ ⸨g' x'⸩⸩, ⟨.app' hπ hf hg hx⟩⟩
  | .none =>
    let not_redex : ¬ e.Redex := Expr.is_redex.sound' heq
    match heq : e with
    | ⸨f x⸩ =>
      let ⟨f', ⟨hf⟩⟩ := reduce f
      let ⟨x', ⟨hx⟩⟩ := reduce x
      ⟨⸨f' x'⸩, ⟨.app (by rw [← heq]; exact not_redex) hf hx⟩⟩
    | Srt m => ⟨Srt m, ⟨.refl_srt⟩⟩
    | Π.{[m]} α, β =>
      let ⟨α', ⟨hα⟩⟩ := reduce α
      let ⟨β', ⟨hβ⟩⟩ := reduce β
      ⟨Π.{[m]} α', β', ⟨.pi_val hα hβ⟩⟩
    | .comb c => ⟨.comb c, ⟨.refl_comb⟩⟩

namespace ParRed

theorem reduce_sound : (reduce A).fst = B → ParRed A B := fun h => by
  rw [← h]
  exact (reduce A).snd.down

theorem reduce_complete : ParRed A B → (reduce A).fst = B := fun h => by
  induction h
  repeat (rename_i h; rw [← h]; rfl)
  · unfold reduce
    unfold Expr.is_redex
    simp
    exact ⟨⟨by assumption, by assumption⟩, by assumption, by assumption⟩
  repeat (rename_i h; rw [← h]; rfl)
  case pi α α' β β' x x' m hα hβ hx ih₁ ih₂ ih₃ =>
    unfold reduce
    unfold Expr.is_redex
    simp
    exact ⟨⟨by assumption, by assumption⟩, by assumption, by assumption⟩
  case app' π π' f f' g g' x x' hπ hf hg hx ih₁ ih₂ ih₃ ih₄ =>
    unfold reduce
    unfold Expr.is_redex
    simp
    exact ⟨⟨by assumption, ⟨by assumption, by assumption⟩⟩, by assumption, by assumption⟩
  case app f x f' x' h_not_redex hp₁ h₂ ih₁ ih₂ =>
    unfold reduce
    split
    · rename_i heq
      have h := Expr.is_redex.sound (by assumption)
      contradiction
    · simp
      exact ⟨by assumption, by assumption⟩
  rename_i ih₁ ih₂
  rw [← ih₁, ← ih₂]; rfl
  repeat (unfold reduce; unfold Expr.is_redex; simp)

instance : Decidable (∃ (C : Expr), ParRed A C ∧ ParRed B C) :=
  if h : (reduce A).fst = (reduce B).fst then
    Decidable.isTrue ⟨(reduce A).fst, reduce_sound rfl, reduce_sound h.symm⟩
  else by
    apply Decidable.isFalse
    intro ⟨C, ha, hb⟩
    have h₁ := reduce_complete ha
    have h₂ := reduce_complete hb
    simp_all

instance : Decidable (ParRed A B) :=
  if h : (reduce A).fst = B then by
    rw [← h]
    exact Decidable.isTrue (reduce A).snd.down
  else by
    apply Decidable.isFalse
    intro hno
    have h := reduce_complete hno
    simp_all

theorem diamond : ParRed A B → ParRed A C → ∃ D, ParRed B D ∧ ParRed C D := by
  intro ha hb
  have h₁ := reduce_complete ha
  have h₂ := reduce_complete hb
  have h : B = C := by
    simp_all
  refine ⟨(reduce B).fst, reduce_sound rfl, reduce_sound ?_⟩
  rw [h]

end ParRed
