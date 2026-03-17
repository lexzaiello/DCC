import Dcc.Ast2
import Dcc.Eval2
import Mathlib.Data.Nat.Notation

def K.type (m n : Level) : Expr := (SK
  Π Sort m, Π (Π #(arg 0), Sort n), Π #((arg 0).ret 1), Π #(arg 1), #((arg 0).ret 3))

--#eval Std.format <| ((K.type 1 1).reduce_pi (SK Sort 0)).fst

def K'.type (m n : Level) : Expr :=
  SK Π Sort m, Π Sort n, Π #((arg 0).ret 1), Π #((arg 1).ret 1), #((arg 0).ret 3)

@[simp] abbrev S.type (m n o : Level) : Expr := SK
    Π Sort m, -- α
    Π (Π #(arg 0), Sort n), -- β
    Π (Π #((arg 0).ret 1), Π #(arg 1), Sort o), -- γ
    Π (Π #((arg 0).ret 2), Π #((arg 1).ret 1), #(arg 2)), -- x
    Π (Π #((arg 0).ret 3), #((arg 1).ret 2)), -- y
    Π #((arg 0).ret 4), -- z
      (B (S.{[m, n, o.succ]} (__ ∶ Sort m) (__ ∶ Sort n) (__ ∶ Sort o)) #((arg 2).ret 1)) -- γ z (y z)
-- ^ note that this is safe, since prior apps were type-checked, and def-eq here is deferred to term-level

inductive Judge : Expr → Expr → Prop
  | app   : Judge (Π' α, β) f
    → Judge α x
    → RunPi x β β'
    → Judge β' ⸨f x⸩
  | srt   : Judge (Srt m.succ) (Srt m)
  | k     : Judge (K.type m n) K.{[m, n]}
  | k'    : Judge (K'.type m n) K'.{[m, n]}
  | s     : Judge (S.type m n o) S.{[m, n, o]}
  | pi    : Judge t_β β
    → RunPi α β t_β'
    → Judge t_β' (Π' α, β)
  | conv  : Judge A x → ParRed A B → Judge B x

def infer (e : Expr) : Option ((t : Expr) × PLift (Judge t e)) :=
  match e_heq : e with
  | Π' α, read => do
    match ← infer α with
    | ⟨Srt m, ⟨h⟩⟩ => pure ⟨Srt m, ⟨Judge.read h⟩⟩
    | _ => .none
  | Π' α, ⸨next β⸩ => do
    match ← infer β with
    | ⟨Srt m, ⟨h⟩⟩ => pure ⟨Srt m, ⟨Judge.next (α := α) h⟩⟩
    | _ => .none
  | Π' α, ⸨$ π f g⸩ => do
    match heq : ← infer π, ← infer f, ← infer g with
    | ⟨(Π' β, Π' ⸨next γ⸩, ⸨next ⸨next (Srt m)⸩⸩), ⟨h₁⟩⟩, ⟨(Π' α₁, ⸨next β₂⸩), ⟨h₂⟩⟩, ⟨(Π' α₂, ⸨next γ₂⸩), ⟨h₃⟩⟩ =>
      if heq₂ : α = α₁ ∧ α = α₂ ∧ γ = γ₂ ∧ β = β₂ then
        by
          let ⟨hq₀, hq₁, hq₂, hq₃⟩ := heq₂
          refine .some ⟨Srt m, ⟨.app' (m := m) (α := α) (β := β) (γ := γ) ?_ ?_ ?_⟩⟩
          · exact h₁
          · rw [← hq₀, ← hq₃] at h₂
            exact h₂
          · rw [← hq₁, ← hq₂] at h₃
            exact h₃
      else .none
    | _, _, _ => .none
  | ⸨f x⸩ => do match ← infer f, ← infer x with
    | ⟨Π' α, β, ⟨hf⟩⟩, ⟨α₂, ⟨hx⟩⟩ =>
      if heq : α = α₂ then
        match hr : run_pi x β with
        | .some h =>
          .some ⟨h.fst, ⟨.app hf (by rw [heq]; exact hx) (by apply RunPi.sound; simp_all; rw [hr]; simp_all)⟩⟩
        | _ => .none
      else
        .none
    | _, _ => .none
  | Srt m => return ⟨Srt m.succ, ⟨.srt⟩⟩
  | K.{[m, n]} => pure ⟨K.type m n, ⟨.k⟩⟩
  | K'.{[m, n]} => pure ⟨K'.type m n, ⟨.k'⟩⟩
  | S.{[m, n, o]} => pure ⟨S.type m n o, ⟨.s⟩⟩
  | Π' α, β => do
    match ← infer β with
    | ⟨Srt n, ⟨hjβ⟩⟩ =>
      let β' ← run_pi α β
      pure ⟨β'.fst, ⟨.pi (β := β) (α := α) hjβ (β'.snd.down)⟩⟩
    | _ => .none
  | _ => .none

#eval (K'.type 1 1).pi_size_of

#eval (infer ⸨K'.{[1, 1]} (Srt 0) (Srt 0)⸩).map (·.fst)
