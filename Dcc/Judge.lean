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
  | succ : RunPi arg α α' → RunPi arg β β'
    → ParRed α' α''
    → ParRed β' β''
    → RunPi arg (Π.{[m]} α, β) (Π.{[m]} α'', β'')

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
      let ⟨α'', ⟨hα'⟩⟩ := (reduce α')
      let ⟨β'', ⟨hβ'⟩⟩ := (reduce β')
      exact ⟨(Π.{[m]} α'', β''), ⟨.succ hα hβ hα' hβ'⟩⟩

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
  · rename_i α α' β β' α'' β'' m hrα hrβ hrα' hrβ' ih₁ ih₂
    simp [run_pi]
    have h : Binder (Expr.Pi m α β) := .mk
    split
    · simp
      exact ⟨by rw [ih₁]; exact (ParRed.reduce_complete hrα'), by rw [ih₂]; exact (ParRed.reduce_complete hrβ')⟩
    · contradiction

instance RunPi.instDecidabble : Decidable (RunPi e_arg e_pi e') :=
  if h : (run_pi e_arg e_pi).fst = e' then
    Decidable.isTrue (h.symm ▸ (run_pi e_arg e_pi).snd.down)
  else
    Decidable.isFalse (fun h₂ => by
      have h := h h₂.complete
      contradiction)

inductive Judge : Expr → Expr → Prop
  | K   : Judge (K.type m n) K.{[m, n]}
  | K'  : Judge (K'.type m n) K'.{[m, n]}
  | S   : Judge (S.type m n o) S.{[m, n, o]}
  | Srt : Judge (Srt m.succ) (Srt m)
  | Pi  : Judge (Srt m) (Π.{[m]} _α, _β)
  | app : Judge (Π.{[m]} α₁, β) f → Judge α₂ x
    → (∃ D, ParRed α₁ D ∧ ParRed α₂ D)
    → RunPi x β β'
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
      if h : ∃ D, ParRed α₁ D ∧ ParRed α₂ D then
        .some <| ⟨_, ⟨.app h_t_f h_t_x h (RunPi.sound rfl)⟩⟩
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

#eval (infer ⸨K.{[2, 2]} (Srt 1) ⸨K'.{[3, 2]} (Srt 2) (Srt 1) (Srt 1)⸩ (Srt 0) (Srt 0)⸩).map (·.fst)
