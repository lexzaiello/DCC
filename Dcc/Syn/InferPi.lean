import Dcc.Syn.JudgePi
import Dcc.Syn.Confluence
import Dcc.Syn.Preservation

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
          exact heq₂.down
          exact ⟨(gen α₁).fst, gen.sound rfl, by apply gen.sound; exact hrw.symm⟩
          exact .refl
          exact ⟨(gen ⸨β x⸩).fst, gen.sound rfl, .refl⟩
        pure ⟨(gen ⸨β x⸩).fst, ⟨h_t⟩⟩
      else
        .error <| (format (gen α₁).fst) ++ " ≠ " ++ (format (gen α₂).fst)
    | ⟨t, _⟩, _ => .error <| "not a function type: " ++ (format t)
  | e => .error <| "not well-typed: " ++ (format e)

namespace _examples

open Expr

#eval infer ⸨(I 2) (Srt 1) (Srt 0)⸩

end _examples
