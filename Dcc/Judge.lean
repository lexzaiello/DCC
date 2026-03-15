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

inductive Nbe : Expr → Expr → Prop
  | redex     : Nbe f f' → Nbe x x'
    → ParRed ⸨f' x'⸩ t'
    → Nbe ⸨f x⸩ t'
  | pi        : Nbe α α' → Nbe β β'
    → Nbe (Π.{[m]} α, β) (Π.{[m]} α', β')
  | refl_srt  : Nbe (Srt m) (Srt m)
  | refl_comb : Nbe (.comb c) (.comb c)

def nbe (t : Expr) : ((t' : Expr) × PLift (Nbe t t')) :=
  match t with
  | Π.{[m]} α, β =>
    let ⟨α', ⟨αp⟩⟩ := nbe α
    let ⟨β', ⟨βp⟩⟩ := nbe β
    ⟨Π.{[m]} α', β', ⟨.pi αp βp⟩⟩
  | Srt m => ⟨Srt m, ⟨.refl_srt⟩⟩
  | .comb c => ⟨.comb c, ⟨.refl_comb⟩⟩
  | ⸨f x⸩ =>
    let ⟨f', ⟨hf⟩⟩ := nbe f
    let ⟨x', ⟨hx⟩⟩ := nbe x
    let ⟨fx', ⟨hfx'⟩⟩ := reduce ⸨f' x'⸩
    ⟨fx', ⟨.redex hf hx hfx'⟩⟩

theorem Nbe.sound_nbe (h : (nbe t).fst = t') : Nbe t t' := by
  induction t generalizing t'
  · unfold nbe at h
    simp at h
    cases h
    rename_i ih₁ ih₂
    apply Nbe.pi
    · exact ih₁ rfl
    · exact ih₂ rfl
  · unfold nbe at h
    simp at h
    cases h
    exact Nbe.refl_srt
  · unfold nbe at h
    simp at h
    cases h
    exact Nbe.refl_comb
  · unfold nbe at h
    rename_i ih₁ ih₂
    simp at h
    cases h
    apply Nbe.redex
    · exact ih₁ rfl
    · exact ih₂ rfl
    exact ParRed.reduce_sound rfl

inductive Judge : Expr → Expr → Prop
  | K   : Judge (K.type m n) K.{[m, n]}
  | K'  : Judge (K'.type m n) K'.{[m, n]}
  | S   : Judge (S.type m n o) S.{[m, n, o]}
  | Srt : Judge (Srt m.succ) (Srt m)
  | Pi  : Judge (Srt m) (Π.{[m]} _α, _β)
  | app : Judge (Π.{[m]} α, β) f
    → Judge α x
    → Judge ⸨β x⸩ ⸨f x⸩
  | conv : Judge A x → B.Redex → (∃ D, Nbe A D ∧ Nbe B D) → Judge B x

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

