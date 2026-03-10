import Dcc.Syn.JudgePi
import Dcc.Syn.Gen
import Qq

open Std (ToFormat Format)
open Std.ToFormat (format)

open Expr

inductive InferAs : Expr → Expr → Type where
  | I   : InferAs (I.type m) (I m)
  | K   : InferAs (K.type m n) (K m n)
  | K'  : InferAs (K'.type m n) (K' m n)
  | S   : InferAs (S.type m n o) (S m n o)
  | Srt : InferAs (Srt m.succ) (Srt m)
  | Pi  : InferAs (Srt m) ((Π' m) _α, _β)
    | app  : InferAs ((Π' m) α, β) f
    → InferAs α x
    → (gen ⸨β x⸩).fst = t'
    → InferAs t' ⸨f x⸩
  | conv : InferAs A x → (∃ C, (gen A).fst = C ∧ (gen B).fst = C) → InferAs B x

inductive NoType : Expr → Type where
  | app'      : NoType app'
  | assert    : NoType assert
  | read      : NoType read
  | next      : NoType next
  | hole      : NoType hole

inductive Err : Expr → Type where
  | no_type  : NoType e → Err e
  | mismatch : InferAs ((Π' m) α, β) f
    → InferAs α₂ x
    → (¬ (∃ C, (gen α).fst = C ∧ (gen α₂).fst = C))
    → Err ⸨f x⸩
  | not_fn   : InferAs t_f f
    → (¬ ∃ m α β, gen.eq t_f ((Π' m) α, β))
    → Err ⸨f x⸩
  | appl     : Err f → Err ⸨f x⸩
  | appr     : Err x → Err ⸨f x⸩

inductive Inference : Expr → Expr → Type where
  | ok    : InferAs t e → Inference t e
  | error : Err e       → Inference t e

theorem Judgment.sound : InferAs t e → Judge t e := by
  intro h_t
  induction h_t
  · exact Judge.I
  · exact Judge.K
  · exact Judge.K'
  · exact Judge.S
  · exact Judge.Srt
  · exact Judge.Pi
  case app m α β f x t' h_t_f h_t_x h_eq h_t_f' h_t_x' =>
    apply Judge.app
    assumption
    exact .refl
    assumption
    exact gen.sound h_eq
  case conv α x β h_t_α heq ih =>
    let ⟨C, heq₁, heq₂⟩ := heq
    apply Judge.conv
    assumption
    exact ⟨C, gen.sound heq₁, gen.sound heq₂⟩

open Expr in def infer (e : Expr) (expected : Option Expr := .none) : ((t : Expr) × Inference t e) :=
  match e with
  | Srt m => ⟨Srt m.succ, .ok .Srt⟩
  | Pi m _α _β => ⟨Srt m, .ok .Pi⟩
  | K' m n => ⟨K'.type m n, .ok .K'⟩
  | K m n => ⟨K.type m n, .ok .K⟩
  | S m n o => ⟨S.type m n o, .ok .S⟩
  | I m => ⟨I.type m, .ok .I⟩
  | .app f x =>
    match infer f, infer x with
    | ⟨a, .error e⟩, ⟨_b, _⟩ => ⟨⸨a x⸩, .error <| .appl e⟩
    | ⟨a, _⟩, ⟨_b, .error e⟩ => ⟨⸨a x⸩, .error <| .appr e⟩
    | tf@⟨(Π' _m) α₁, β, .ok heq₁⟩, tx@⟨α₂, .ok heq₂⟩ =>
      if hrw : (gen α₁).fst = (gen α₂).fst then
        let h : InferAs (gen ⸨β x⸩).fst ⸨f x⸩ := InferAs.app heq₁ (.conv heq₂ (⟨(gen α₂).fst, rfl, hrw⟩)) rfl
        ⟨(gen ⸨β x⸩).fst, .ok h⟩
      else
        ⟨⸨β x⸩, .error (.mismatch heq₁ heq₂ (by intro ⟨C, h₁, h₂⟩; exact hrw (h₁.trans h₂.symm)))⟩
    | ⟨t, _⟩, _ => .error <| "not a function type: " ++ (format t)
  | e => .error <| "not well-typed: " ++ (format e)

theorem infer.sound : infer e = .ok res → Judge res.fst e := fun _ => res.snd.down

syntax "decide_infer" term : term
syntax "decide_infer'" term : term

open Qq in elab "decide_infer" e:term : term => do
  let e : Q(Expr) := ← Lean.Meta.whnf (← Lean.Meta.reduceAll (← Lean.Elab.Term.elabTerm e .none))
  let ref ← Expr.decode e
  match infer ref with
  | .ok t =>
    Lean.Meta.reduceAll (Lean.toExpr t.fst)
  | .error e => throwError (format e)

open Qq Lean Meta Simp in elab "decide_infer'" e:term : term => do
  let e : Q(_root_.Expr) := (← Lean.Elab.Term.elabTerm e .none)
  Lean.Meta.whnf (← Lean.Meta.reduceAll q(infer $e))

open Expr in example : ∃ t, infer ⸨(I 2) (Srt 1) (Srt 0)⸩ = t := by
  let h₂ := decide_infer' ⸨(I 2) (Srt 1) (Srt 0)⸩
  simp

namespace _examples

open Expr

#eval Sigma.fst <$> infer ⸨(I 2) (Srt 1) (Srt 0)⸩

end _examples
