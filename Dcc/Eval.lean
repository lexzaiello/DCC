import Dcc.Ast
import Mathlib.Data.Nat.Notation

open Std (ToFormat Format)
open Std.ToFormat (format)

namespace Expr

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

/-
For parallel reduction:
- only proceed with the general app case if there are fewer arguments
to the innermost spine than its arity requires
-/
inductive Arity : Expr → ℕ → Prop
  | pi    : Arity (Π.{[m]} α, β) 1
  | k     : Arity (K.{[m, n]}) 4
  | k'    : Arity (K'.{[m, n]}) 4
  | s     : Arity (S.{[m, n, o]}) 6
  | next  : Arity next 2
  | read  : Arity read 1
  | app'  : Arity $ 4
  | srt   : Arity (Srt n) 0
  | app   : Arity f (Nat.succ n) → Arity ⸨f x⸩ n

abbrev Head  := Expr
abbrev Spine := List Expr

inductive Profile : Expr → Head → Spine → Prop
  | pi   : Profile (Π.{[m]} α, β) (Π.{[m]} α, β) []
  | comb : Profile (.comb c) (.comb c) []
  | srt  : Profile (Srt m) (Srt m) []
  | app  : Profile e f args -- f represents the innermost combinator
    → Profile ⸨e x⸩ f (args ++ [x])

/-inductive Stuck : Expr → Bool → Prop
  | zero : Profile e inner_comb args
    → Arity inner_comb args.length
    → Stuck e false
  -- left can step
  | succ : Stuck f False → Stuck ⸨f x⸩ True-/

inductive Stuck : Expr → Prop
  | srt     : Stuck (Srt m)
  | pi      : Stuck α
    → Stuck β
    → Stuck (Π.{[m]} α, β)
  | app     : Arity f 0 → Stuck ⸨f x⸩
  | app_inv : (∃ n, ⸨f x⸩.Arity (Nat.succ n))
    → Stuck ⸨f x⸩

end Expr

inductive ParRed : Expr → Expr → Prop
  | k         : ParRed x x' → ParRed ⸨K.{[m, n]} α β x y⸩ x'
  | k'        : ParRed x x' → ParRed ⸨K'.{[m, n]} α β x y⸩ x'
  | s         : ParRed x x' → ParRed y y' → ParRed z z'
    → ParRed ⸨S.{[m, n, o]} α β γ x y z⸩ ⸨⸨x' z'⸩ ⸨y' z'⸩⸩
  | next      : ParRed f f' → ParRed ⸨next f x⸩ f'
  | read      : ParRed e e' → ParRed ⸨read e⸩ e'
  | pi        : ParRed α α' → ParRed β β'
    → ParRed x x'
    → ParRed ⸨(Π.{[m]} α, β) x⸩ (Π.{[m]} ⸨α' x'⸩, ⸨β' x'⸩)
  | app'      : ParRed π π' → ParRed f f'
    → ParRed g g' → ParRed x x'
    → ParRed ⸨$ π f g x⸩ ⸨π' ⸨f' x'⸩ ⸨g' x'⸩⸩
  | refl_comb : ParRed (.comb c) (.comb c)
  | refl_srt  : ParRed (Srt m) (Srt m)
  | pi_val    : ParRed α α' → ParRed β β' → ParRed (Π.{[m]} α, β) (Π.{[m]} α', β')
  | app       : ⸨f x⸩.Stuck → ParRed f f' → ParRed x x' → ParRed ⸨f x⸩ ⸨f' x'⸩

namespace ParRed

theorem mk_par_app_comb : ParRed x x' → ∃ e', ParRed ⸨(.comb c) x⸩ e' := by
  intro h
  cases c
  · rename_i m n
    refine ⟨⸨K'.{[m, n]} x'⸩, ?_⟩
    apply ParRed.app
    · apply Expr.Stuck.app_inv
      refine ⟨2, ?_⟩
      apply Expr.Arity.app
      exact .k'
    · exact .refl_comb
    · assumption
  · rename_i m n
    refine ⟨⸨K.{[m, n]} x'⸩, ?_⟩
    apply ParRed.app
    · apply Expr.Stuck.app_inv
      refine ⟨2, ?_⟩
      apply Expr.Arity.app
      exact .k
    · exact .refl_comb
    · assumption
  · rename_i m n o
    refine ⟨⸨S.{[m, n, o]} x'⸩, ?_⟩
    apply ParRed.app
    · apply Expr.Stuck.app_inv
      refine ⟨4, ?_⟩
      apply Expr.Arity.app
      exact .s
    · exact .refl_comb
    · assumption
  · refine ⟨⸨next x'⸩, ?_⟩
    apply ParRed.app
    · apply Expr.Stuck.app_inv
      refine ⟨0, ?_⟩
      apply Expr.Arity.app
      exact .next
    · exact .refl_comb
    · assumption
  · refine ⟨x', ?_⟩
    apply ParRed.read
    assumption
  · refine ⟨⸨$ x'⸩, ?_⟩
    apply ParRed.app
    · apply Expr.Stuck.app_inv
      refine ⟨2, ?_⟩
      apply Expr.Arity.app
      exact .app'
    · exact ParRed.refl_comb
    · assumption

theorem mk_par_app : ParRed f f' → ParRed x x' → ∃ e', ParRed ⸨f x⸩ e' := by
  intro hf hx
  induction hf
  · rename_i kx kx' m n α β y h_k ih
    have ⟨e', h_x_app⟩ := ih
    refine ⟨⸨kx' x'⸩, .app ?_ (.k h_k) (by assumption)⟩
    apply Expr.Stuck.app
    apply Expr.Arity.app
    apply Expr.Arity.app
    apply Expr.Arity.app
    apply Expr.Arity.app
    exact .k
  · rename_i kx kx' m n α β y h_k ih
    have ⟨e', h_x_app⟩ := ih
    refine ⟨⸨kx' x'⸩, .app ?_ (.k' h_k) (by assumption)⟩
    apply Expr.Stuck.app
    apply Expr.Arity.app
    apply Expr.Arity.app
    apply Expr.Arity.app
    apply Expr.Arity.app
    exact .k'
  · rename_i sx sx' y y' z z' m n o α β γ hprx hpy hprz ih₁ ih₂ ih₃
    refine ⟨⸨⸨⸨sx' z'⸩ ⸨y' z'⸩⸩ x'⸩, ?_⟩
    apply ParRed.app
    · apply Expr.Stuck.app
      · apply Expr.Arity.app
        apply Expr.Arity.app
        apply Expr.Arity.app
        apply Expr.Arity.app
        apply Expr.Arity.app
        apply Expr.Arity.app
        exact .s
    · exact ParRed.s (by assumption) (by assumption) (by assumption)
    · assumption
  · rename_i f nf nf' nx' hpf
    refine ⟨⸨nf x'⸩, ?_⟩
    apply ParRed.app
    · apply Expr.Stuck.app
      apply Expr.Arity.app
      apply Expr.Arity.app
      exact .next
    · exact .next (by assumption)
    · assumption
  · rename_i e re hpr ih
    refine ⟨⸨re x'⸩, ?_⟩
    apply ParRed.app
    · apply Expr.Stuck.app
      · apply Expr.Arity.app
        exact .read
    · exact .read (by assumption)
    · assumption
  · rename_i α α' β β' pix pix' m hpi₁ hpi₂ hpi₃ ih₁ ih₂ ih₃
    refine ⟨⸨(Π.{[m]} ⸨α' pix'⸩, ⸨β' pix'⸩) x'⸩, ?_⟩
    apply ParRed.app
    · apply Expr.Stuck.app
      · apply Expr.Arity.app
        exact Expr.Arity.pi
    · apply ParRed.pi
      repeat assumption
    assumption
  · rename_i π π' f f' g g' appx appx' happπ happf happg happx ih₁ ih₂ ih₃ ih₄
    refine ⟨⸨π' ⸨f' appx'⸩ ⸨g' appx'⸩ x'⸩, ?_⟩
    apply ParRed.app
    · apply Expr.Stuck.app
      · apply Expr.Arity.app
        apply Expr.Arity.app
        apply Expr.Arity.app
        apply Expr.Arity.app
        exact Expr.Arity.app'
    · apply ParRed.app'
      repeat assumption
    · assumption
  · rename_i comb
    refine ⟨⸨(.comb comb) x'⸩, ?_⟩
    
    sorry
  sorry

theorem refl : ParRed A A := by
  induction A
  · apply ParRed.pi_val
    repeat assumption
  exact .refl_srt
  exact .refl_comb
  rename_i f x h_f h_x
  
  sorry

theorem diamond : ParRed A B → ParRed A C → ∃ D, ParRed B D ∧ ParRed C D := by
  intro ha hb
  induction ha generalizing C
  repeat (cases hb; simp_all; contradiction)
  
  sorry

end ParRed
