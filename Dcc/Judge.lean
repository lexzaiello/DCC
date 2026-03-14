import Dcc.Ast
import Dcc.Eval
import Mathlib.Data.Nat.Notation

def K'.type (m n : Level) : Expr :=
  Π.{[m]} Srt m, Π.{[m]} ⸨next (Srt n)⸩, Π.{[m]} (0 next), Π.{[m]} (1 next), ((0 read).assert_n 3)

def K.β_arg (_m n : Level) : Expr :=
  Π.{[n.succ]} (0 read), (1 ⸨next (Srt n)⸩)

def K.x_arg : Expr := (0 next)

def K.y_arg : Expr := ⸨$ ⸨$ read⸩ (1 next) (2 read)⸩

def K.cod : Expr := (read).assert_n 3

def K.type (m n : Level) : Expr :=
    Π.{[m]} Srt m
  , Π.{[m]} (K.β_arg m n)
  , Π.{[m]} K.x_arg
  , Π.{[m]} K.y_arg
  , K.cod

def S.type (m n o : Level) : Expr :=
    Π.{[o]} Srt m
  , Π.{[o]} (Π.{[n.succ]} (0 read), (1 ⸨next (Srt n)⸩))
  , Π.{[o]} (Π.{[o.succ]} (0 next)
      , Π.{[o.succ]} (1 read)
      , (3 ⸨next (Srt o)⸩))
  , Π.{[o]} (Π.{[o]} ((0 read).assert_n 2)
      , Π.{[o]} (1 next)
      , (2 read))
   , Π.{[o]} (Π.{[n]} ((0 read).assert_n 3)
       , (1 (next ∘' next)))
   , Π.{[o]} ((0 read).assert_n 4)
   , (2 (next ∘' ⸨$ read⸩))

inductive Judge : Expr → Expr → Prop
  | K   : Judge (K.type m n) K.{[m, n]}
  | K'  : Judge (K'.type m n) K'.{[m, n]}
  | S   : Judge (S.type m n o) S.{[m, n, o]}
  | Srt : Judge (Srt m.succ) (Srt m)
  | Pi  : Judge (Srt m) (Π.{[m]} _α, _β)
  | app : Judge (Π.{[m]} α, β) f
    → Judge α x
    → ParRed ⸨β x⸩ β'
    → Judge β' ⸨f x⸩
  | conv : Judge A x → (∃ C, ParRed A C ∧ ParRed B C) → Judge B x

def infer (e : Expr) : Option ((t : Expr) × (PLift <| Judge t e)) :=
  match e with
  | K.{[m, n]} => .some ⟨K.type m n, ⟨Judge.K⟩⟩
  | K'.{[m, n]} => .some ⟨K'.type m n, ⟨Judge.K'⟩⟩
  | S.{[m, n, o]} => .some ⟨S.type m n o, ⟨Judge.S⟩⟩
  | Srt m => .some ⟨Srt m.succ, ⟨Judge.Srt⟩⟩
  | Π.{[m]} _α, _β => .some ⟨Srt m, ⟨Judge.Pi⟩⟩
  | ⸨f x⸩ => do match ← infer f, ← infer x with
    | ⟨Π.{[m]} α₁, β, ⟨h_t_f⟩⟩, ⟨α₂, ⟨h_t_x⟩⟩ =>
      if h : α₁ = α₂ then
        .some <| ⟨(reduce ⸨β x⸩).fst, ⟨.app h_t_f (by rw [h]; exact h_t_x) (reduce ⸨β x⸩).snd.down⟩⟩
      else if h : ∃ C, ParRed α₂ C ∧ ParRed α₁ C then
        .some <| ⟨(reduce ⸨β x⸩).fst, ⟨.app h_t_f (Judge.conv h_t_x h) (reduce ⸨β x⸩).snd.down⟩⟩
      else .none
    | _, _ => .none
  | _ => .none

theorem infer_sound : (infer e) = .some ⟨t, PLift.up proof⟩ → Judge t e := fun _ => proof
