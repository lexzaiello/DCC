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

/-
  Weak-head normal form of a type.
  If something other than these is encountered, we should
  apply the conversion constructor.
-/
inductive NormTy : Expr → Prop
  | srt   : NormTy (Srt m)
  | pi    : NormTy α → NormTy β
    →  NormTy (Π.{[m]} α, β)
  | redex : (¬ ⸨f x⸩.Redex)
    → NormTy f → NormTy x → NormTy ⸨f x⸩

inductive IsNormTy : Expr → Type
  | srt   : IsNormTy (Srt m)
  | pi    : IsNormTy α → IsNormTy β
    →  IsNormTy (Π.{[m]} α, β)
  | redex : (¬ ⸨f x⸩.Redex) → IsNormTy f
    → IsNormTy x → IsNormTy ⸨f x⸩

def Expr.is_norm_ty (e : Expr) : Option (IsNormTy e) :=
  match e with
  | Π.{[_m]} α, β => do pure <| .pi (← α.is_norm_ty) (← β.is_norm_ty)
  | ⸨f x⸩ =>
    if h : ¬⸨f x⸩.Redex then
      do pure <| .redex h (← f.is_norm_ty) (← x.is_norm_ty)
    else
      .none
  | Srt _m => pure .srt
  | _ => .none

theorem IsNormTy.sound : IsNormTy e → NormTy e := by
  intro h
  induction h
  · exact .srt
  · apply NormTy.pi
    repeat assumption
  · apply NormTy.redex
    repeat assumption

theorem is_norm_ty.sound : e.is_norm_ty = .some p → NormTy e := fun _ => p.sound

theorem is_norm_ty.complete (p : NormTy e) : ∃ p, e.is_norm_ty = .some p := by
  induction p
  · rename_i m
    exact ⟨.srt, rfl⟩
  · rename_i α β m hα hβ ih₁ ih₂
    have ⟨p₁, hp₁⟩ := ih₁
    have ⟨p₂, hp₂⟩ := ih₂
    refine ⟨.pi p₁ p₂, ?_⟩
    simp [Expr.is_norm_ty, hp₁, hp₂]
  · rename_i f x h_red hf hx ih₁ ih₂
    have ⟨p₁, hp₁⟩ := ih₁
    have ⟨p₂, hp₂⟩ := ih₂
    refine ⟨.redex h_red p₁ p₂, ?_⟩
    simp [Expr.is_norm_ty, hp₁, hp₂, h_red]

theorem is_norm_ty.sound' : e.is_norm_ty = .none → ¬ NormTy e := by
  intro heq hp
  have ⟨_, h_some⟩ := is_norm_ty.complete hp
  simp_all

instance NormTy.instDecidable : Decidable (NormTy e) :=
  match heq : e.is_norm_ty with
  | .some _p => .isTrue (is_norm_ty.sound heq)
  | .none => .isFalse (is_norm_ty.sound' heq)

inductive Judge : Expr → Expr → Prop
  | K   : Judge (K.type m n) K.{[m, n]}
  | K'  : Judge (K'.type m n) K'.{[m, n]}
  | S   : Judge (S.type m n o) S.{[m, n, o]}
  | Srt : Judge (Srt m.succ) (Srt m)
  | Pi  : Judge (Srt m) (Π.{[m]} _α, _β)
  | app : Judge (Π.{[m]} α, β) f
    → Judge α x
    → Judge ⸨β x⸩ ⸨f x⸩
  | conv : Judge A x → (∃ C, ParRed (reduce A).fst C ∧ ParRed (reduce B).fst C) → Judge B x

def infer (e : Expr) : Option ((t : Expr) × (PLift <| Judge t e)) :=
  match e with
  | K.{[m, n]} => .some ⟨K.type m n, ⟨Judge.K⟩⟩
  | K'.{[m, n]} => .some ⟨K'.type m n, ⟨Judge.K'⟩⟩
  | S.{[m, n, o]} => .some ⟨S.type m n o, ⟨Judge.S⟩⟩
  | Srt m => .some ⟨Srt m.succ, ⟨Judge.Srt⟩⟩
  | Π.{[m]} _α, _β => .some ⟨Srt m, ⟨Judge.Pi⟩⟩
  | ⸨f x⸩ => do
    let t_f₁ ← infer f
    let t_x₁ ← infer x

    match t_f₁, t_x₁ with
    | ⟨Π.{[_m]} α₁, β, ⟨h_t_f⟩⟩, ⟨α₂, ⟨h_t_x⟩⟩ =>
      if h_conv : ∃ C, ParRed (reduce α₂).fst C ∧ ParRed (reduce α₁).fst C then
        let h₀ := Judge.app h_t_f (.conv h_t_x h_conv)
        .some ⟨⸨β x⸩, ⟨.conv h₀ ParRed.reduce_self'⟩⟩
      else .none
    | _, _ => .none
  | _ => .none

theorem infer_sound : (infer e) = .some ⟨t, PLift.up proof⟩ → Judge t e := fun _ => proof

