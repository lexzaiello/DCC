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
Nbe is unnecessary. What is necessary is type normalization. Specifically, we can have two types
of types:

- sorts
- Pi binders
  - applications under pi binders
-/

inductive Binder : Expr → Prop
  | mk : Binder (Π.{[m]} α, β)

instance Binder.instDecidable : Decidable (Binder e) := by
  cases e
  · exact .isTrue .mk
  repeat (apply Decidable.isFalse; intro h; cases h)

inductive RunPi (arg : Expr) : Expr → Expr → Prop
  | zero : ¬ Binder e     → ParRed ⸨e arg⸩ e' → RunPi arg e e'
  | succ : RunPi arg α α' → RunPi arg β β'    → RunPi arg (Π.{[m]} α, β) (Π.{[m]} α', β')

def run_pi (e_arg e_pi : Expr) : ((e' : Expr) × PLift (RunPi e_arg e_pi e')) :=
  if h : ¬ Binder e_pi then
    let ⟨e', ⟨h⟩⟩ := (reduce ⸨e_pi e_arg⸩)
    ⟨e', ⟨.zero (fun h => by simp_all) h⟩⟩
  else by
    simp at h
    match heq : e_pi with
    | Π.{[m]} α, β =>
      let ⟨α', ⟨hα⟩⟩ := run_pi e_arg α
      let ⟨β', ⟨hβ⟩⟩ := run_pi e_arg β
      exact ⟨(Π.{[m]} α', β'), ⟨.succ hα hβ⟩⟩

theorem RunPi.sound : (run_pi e_arg e_pi).fst = e' → RunPi e_arg e_pi e' := fun _ => by
  have h := (run_pi e_arg e_pi).snd.down
  rename_i heq
  rw [heq] at h
  exact h

theorem RunPi.complete : RunPi e_arg e_pi e' → (run_pi e_arg e_pi).fst = e' := by
  intro h
  induction h
  · simp [run_pi]
    simp_all
    apply ParRed.reduce_complete
    assumption
  · rename_i α α' β β' m hrα hrβ ih₁ ih₂
    simp [run_pi]
    have h : Binder (Expr.Pi m α β) := .mk
    split
    · simp
      exact ⟨by assumption, by assumption⟩
    · contradiction


theorem Nbe.complete (h : Nbe t t') : (nbe t).fst = t' := by
  induction h
  · rename_i hpar ih₁ ih₂
    simp [nbe, ← hpar.reduce_complete]
    rw [← ih₁, ← ih₂]
  · rename_i α α' β β' m hnα hnβ hpr ih₁ ih₂
    simp [nbe]
    apply ParRed.reduce_complete
    rw [ih₁, ih₂]
    exact hpr
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
      else
        .none
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

#eval (infer ⸨K.{[2, 2]} (Srt 1) ⸨K'.{[3, 2]} (Srt 2) (Srt 1) (Srt 1)⸩⸩).map (·.fst)
