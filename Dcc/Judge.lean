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

theorem Nbe.sound (h : (nbe t).fst = t') : Nbe t t' := by
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

theorem Nbe.complete (h : Nbe t t') : (nbe t).fst = t' := by
  induction h
  · rename_i hpar ih₁ ih₂
    simp [nbe, ← hpar.reduce_complete]
    rw [← ih₁, ← ih₂]
  · rename_i α α' β β' m hnα hnβ ih₁ ih₂
    simp [← ih₁, ← ih₂, nbe]
  repeat (unfold nbe; rfl)

instance Nbe.instDecicdable : Decidable (Nbe t t') :=
  if h : (nbe t).fst = t' then
    .isTrue (Nbe.sound h)
  else
    .isFalse (fun h₂ => h (Nbe.complete h₂))

instance conv₁.instDecidable : Decidable (∃ D, Nbe A D ∧ Nbe B D) :=
  if h : (nbe A).fst = (nbe B).fst then
    .isTrue ⟨(nbe A).fst, (nbe A).snd.down, by rw [h]; exact (nbe B).snd.down⟩
  else
    .isFalse (fun ⟨D, h₁, h₂⟩ => by
      let heq₁ := h₁.complete
      let heq₂ := h₂.complete
      simp_all)

instance conv.instDecidable : Decidable (B.Redex ∧ (∃ D, Nbe A D ∧ Nbe B D)) :=
  if h : B.Redex then
    if h₂ : ∃ D, Nbe A D ∧ Nbe B D then
      .isTrue ⟨h, h₂⟩
    else
      .isFalse (fun h => by simp_all)
  else .isFalse (fun h => by simp_all)

inductive Judge : Expr → Expr → Prop
  | K   : Judge (K.type m n) K.{[m, n]}
  | K'  : Judge (K'.type m n) K'.{[m, n]}
  | S   : Judge (S.type m n o) S.{[m, n, o]}
  | Srt : Judge (Srt m.succ) (Srt m)
  | Pi  : Judge (Srt m) (Π.{[m]} _α, _β)
  | app : Judge (Π.{[m]} fα, β) f → Judge xα x
    → (∃ D, Nbe fα D ∧ Nbe xα D) → Nbe ⸨β x⸩ β'
    → Judge β' ⸨f x⸩

def infer (e : Expr) : Option ((t : Expr) × (PLift <| Judge t e)) :=
  match e with
  | K.{[m, n]} => .some ⟨K.type m n, ⟨Judge.K⟩⟩
  | K'.{[m, n]} => .some ⟨K'.type m n, ⟨Judge.K'⟩⟩
  | S.{[m, n, o]} => .some ⟨S.type m n o, ⟨Judge.S⟩⟩
  | Srt m => .some ⟨Srt m.succ, ⟨Judge.Srt⟩⟩
  | Π.{[m]} _α, _β => .some ⟨Srt m, ⟨Judge.Pi⟩⟩
  | ⸨f x⸩ => do
    match ← infer f, ← infer x with
    | ⟨Π.{[_m]} α₁, _β, ⟨h_t_f⟩⟩, ⟨α₂, ⟨h_t_x⟩⟩ =>
      if h : ∃ D, Nbe α₁ D ∧ Nbe α₂ D then
        .some <| ⟨_, ⟨.app h_t_f h_t_x h (Nbe.sound rfl)⟩⟩
      else .none
    | _, _ => .none
  | _ => .none

theorem infer_sound : (infer e) = .some ⟨t, PLift.up proof⟩ → Judge t e := fun _ => proof

def infer_complete (h : Judge t e) : (infer e).map (·.fst) = .some t := by
  induction h
  repeat rfl
  case app m fα b f xα x β' h_t_f h_t_x h_conv nbf ih₁ ih₂ =>
    simp at ih₁
    simp at ih₂
    have ⟨hp₁, heq₁⟩ := ih₁
    have ⟨hp₂, heq₂⟩ := ih₂
    simp [infer, heq₁, heq₂]
    exact ⟨h_conv, nbf.complete⟩
