import Dcc.Syn.JudgePi
import Dcc.Syn.Gen
import Qq

open Std (ToFormat Format)
open Std.ToFormat (format)

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
