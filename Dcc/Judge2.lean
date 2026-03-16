import Dcc.Ast2
import Dcc.Eval2
import Mathlib.Data.Nat.Notation

/-
Notes:

Π doesn't do general reduction. Just shuffle down.
So, we may need to change the K rule slightly so that β x works.
-/

@[simp] abbrev K'.type (m n : Level) : Expr :=
  Π' Srt m, Π' ⸨K* (Srt n)⸩, Π' ⸨# 0 K*⸩, Π' ⸨# 1 K*⸩, (⸨# 0 I⸩.assert_n 3)

@[simp] abbrev K.β_arg (_m n : Level) : Expr :=
  Π' ⸨# 0 I⸩, ⸨# 1 ⸨K* (Srt n)⸩⸩

@[simp] abbrev K.x_arg : Expr := ⸨# 0 K*⸩

/-
y arg: β x

in scope:
α
-/

@[simp] abbrev K.y_arg : Expr := ⸨# 2 I⸩

@[simp] abbrev K.cod : Expr := (I).assert_n 3

@[simp] abbrev K.type (m n : Level) : Expr :=
    Π' Srt m
  , Π' (K.β_arg m n)
  , Π' K.x_arg
  , Π' K.y_arg
  , K.cod

@[simp] abbrev S.type (m n o : Level) : Expr :=
    Π' Srt m
  , Π' (Π' ⸨# 0 I⸩, ⸨# 1 ⸨K* (Srt n)⸩⸩)
  , Π' (Π' ⸨# 0 K*⸩
      , Π' ⸨# 1 I⸩
      , ⸨# 3 ⸨K* (Srt o)⸩⸩)
  , Π' (Π' (⸨# 0 I⸩.assert_n 2)
      , Π' ⸨# 1 K*⸩
      , ⸨# 2 I⸩)
   , Π' (Π' (⸨# 0 I⸩.assert_n 3)
       , ⸨# 1 ⸨B K* K*⸩⸩)
   , Π' (⸨# 0 I⸩.assert_n 4)
   , I -- SORRY: fix this later

@[simp] def Expr.pi_size_of : Expr → ℕ
  | (Π' α, β) => 1 + α.pi_size_of + β.pi_size_of
  | ⸨f x⸩ => f.pi_size_of + x.pi_size_of
  | I | B | C | K* => 1
  | _ => 0

inductive RunPi (arg : Expr) : Expr → Expr → Prop
  | pi       : RunPi arg α α'
    → RunPi arg β β'
    → RunPi arg (Π' α, β) (Π' α', β')
  | app      : ⸨e arg⸩.RedTyComb e'
    → RunPi arg e e'

/-
run_pi should strictly decrease the size of in_e with respect to
pi_size.
each instruction is just shuffling around.
may have to re-evaluate $ rule. seems suspicious.
probably want to swap $ out for just normal composition.
literally almost nowhere in types where this happens.
we probably want a directed version.
-/

def run_pi (arg in_e : Expr) : Option ((e' : Expr) × (PLift (RunPi arg in_e e'))) :=
  match heq : ⸨in_e arg⸩.red_ty_comb with
  | .some ⟨e', ⟨h⟩⟩ => .some ⟨e', ⟨.app h⟩⟩
  | .none =>
    match in_e with
    | (Srt _m) => .none
    | Π' α, β => do
      let ⟨α', ⟨h₁⟩⟩ ← run_pi arg α
      let ⟨β', ⟨h₂⟩⟩ ← run_pi arg β
      .some ⟨Π' α', β', ⟨.pi h₁ h₂⟩⟩
    | ⸨_f _x⸩ => .none
    | _ => .none

theorem RunPi.sound {h : (run_pi arg in_e).isSome} : ((run_pi arg in_e).get h).fst = e' → RunPi arg in_e e' := fun heq => by
  have h := ((run_pi arg in_e).get h).snd.down
  rw [heq] at h
  exact h

theorem RunPi.complete (h : RunPi arg in_e e') : run_pi arg in_e = .some ⟨e', ⟨h⟩⟩ := by
  induction h
  · unfold run_pi
    split
    · contradiction
    simp_all
  · rename_i h
    have h := h.complete
    unfold run_pi
    simp_all
    split
    simp_all
    congr
    repeat exact h.left
    have ⟨_, h₁⟩ := h
    simp_all
    split
    repeat simp_all

inductive Judge : Expr → Expr → Prop
  | read  : Judge (Srt m) α
    → Judge (Srt m) (Π' α, read)
  | next  : Judge (Srt m) β
    → Judge (Srt m) (Π' α, ⸨next β⸩)
  | app'  : Judge (Π' β, Π' ⸨next γ⸩, ⸨next ⸨next (Srt m)⸩⸩) π
    → Judge (Π' α, ⸨next β⸩) f
    → Judge (Π' α, ⸨next γ⸩) g
    → Judge (Srt m) (Π' α, ⸨$ π f g⸩)
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
