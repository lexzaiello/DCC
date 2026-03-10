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
    → InferAs ⸨β x⸩ ⸨f x⸩
  | conv : InferAs α x → gen.eq α β → InferAs β x -- can derive Judge β x with gen

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
    → (¬ gen.eq α α₂)
    → Err ⸨f x⸩
  | not_fn   : InferAs t_f f
    → (¬ ∃ m α β, gen.eq t_f ((Π' m) α, β))
    → Err ⸨f x⸩

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
  case app m α β f x h_t_f h_α h_t_f' h_t_x' => exact Judge.app h_t_f' .refl h_t_x' .refl
  case conv α x β h_t_α heq ih => exact ih.step_gen heq

open Expr in def infer (e : Expr) : Except Format ((t : Expr) × (PLift <| Judge t e)) :=
  match e with
  | Srt m => pure ⟨Srt m.succ, ⟨.Srt⟩⟩
  | Pi m _α _β => pure ⟨Srt m, ⟨.Pi⟩⟩
  | K' m n => pure ⟨K'.type m n, ⟨.K'⟩⟩
  | K m n => pure ⟨K.type m n, ⟨.K⟩⟩
  | S m n o => pure ⟨S.type m n o, ⟨.S⟩⟩
  | I m => pure ⟨I.type m, ⟨.I⟩⟩
  | .app f x => do
    match ← infer f, ← infer x with
    | ⟨(Π' _m) α₁, β, heq₁⟩, ⟨α₂, heq₂⟩ =>
      if hrw : (gen α₁).fst = (gen α₂).fst then
        have β' := gen ⸨β x⸩
        have h_t : Judge (gen ⸨β x⸩).fst ⸨f x⸩ := by
          apply Judge.conv
          apply Judge.app
          exact heq₁.down
          exact .refl
          apply Judge.conv
          exact heq₂.down
          exact ⟨(gen α₂).fst, gen.sound rfl, by apply gen.sound; exact hrw⟩
          exact .refl
          exact ⟨(gen ⸨β x⸩).fst, gen.sound rfl, .refl⟩
        pure ⟨(gen ⸨β x⸩).fst, ⟨h_t⟩⟩
      else
        .error <| (format (gen α₁).fst) ++ " ≠ " ++ (format (gen α₂).fst)
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
