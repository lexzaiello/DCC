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

/-
Todo: this is very hacky.
Only useful under Pi binders.
This turns typed user-land combinators into our Π combinators.
inductive Transport : Expr → Expr → Prop
  | K'_next  : Transport ⸨K'.{[m, n]} α β⸩ next
  | K_next   : Transport ⸨K.{[m, n]} α β⸩ next
  | app      : Transport f f'  → Transport ⸨f x⸩ ⸨f' x⸩
  | pi       : Transport α₁ α₂ → Transport (Π.{[m]} α₁, β₁) (Π.{[m]} α₂, β₂)

def transport (t : Expr) : Option ((t' : Expr) × (PLift (Transport t t'))) :=

inductive DefEq : Expr → Expr → Prop
  | red_conv : (∃ D, ParRed α₁ D ∧ ParRed α₂ D)
    → DefEq α₁ α₂
  | propext  : Binder p₁ → Binder p₂
    → (ParRed ⸨p₁ (Srt 0)⸩ B)
    → (ParRed ⸨p₂ (Srt 0)⸩ B)
    → DefEq p₁ p₂

instance DefEq.instDecidable : Decidable (DefEq t₁ t₂) := by
  cases t₁
  cases t₂
  · rename_i m α₁ β₁ n α₂ β₂
    if h : (reduce ⸨(Π.{[m]} α₁, β₁) (Srt 0)⸩).fst = (reduce ⸨(Π.{[n]} α₂, β₂) (Srt 0)⸩).fst then
      apply Decidable.isTrue
      apply DefEq.propext
      · exact Binder.mk
      · exact Binder.mk
      · exact ParRed.reduce_sound rfl
      · rw [h]
        exact ParRed.reduce_sound rfl
    else
      apply Decidable.isFalse
      intro h
      cases h
      
      sorry
  sorry-/

/-
Converts term-level combinators in an expression into type "values"
e.g., read / next / ${}.

This is essentially stripping away the typing information.
-/

inductive CanTransport : Expr → Expr → Prop
  | K'_next   : CanTransport ⸨K'.{[m, n]} α β⸩ next
  | K_next    : CanTransport ⸨K.{[m, n]} α β⸩ next
  | S_app'    : CanTransport ⸨S.{[m, n, o]} α β γ⸩ ⸨$ read⸩

inductive Transport : Expr → Expr → Prop
  | do_trans  : CanTransport e e'           → Transport e e'
  | no_trans  : (¬ ∃ e', CanTransport e e') → Transport e e
  | pi        : Transport α α' → Transport β β'
    → Transport (Π.{[m]} α, β) (Π.{[m]} α', β')
  | app       : Transport f f' → Transport x x'
    → Transport ⸨f x⸩ ⸨f' x'⸩

def transport (t : Expr) : ((t' : Expr) × (PLift (Transport t t'))) :=
  match t with
  | ⸨K'.{[m, n]} α β⸩ => ⟨_, ⟨.do_trans .K'_next⟩⟩
  | ⸨K.{[m, n]} α β⸩ => ⟨_, ⟨.do_trans .K_next⟩⟩
  | ⸨S.{[m, n, o]} α β γ⸩ => ⟨_, ⟨.do_trans .S_app'⟩⟩
  | Π.{[m]} α, β =>
    let ⟨α', ⟨hα⟩⟩ := transport α
    let ⟨β', ⟨hβ⟩⟩ := transport β
    ⟨_, ⟨.pi hα hβ⟩⟩
  | ⸨f x⸩ =>
    let ⟨f', ⟨hf⟩⟩ := transport f
    let ⟨x', ⟨hx⟩⟩ := transport x
    ⟨_, ⟨.app hf hx⟩⟩
  | next => ⟨next, ⟨.no_trans (fun ⟨_, h⟩ => by cases h)⟩⟩
  | read => ⟨read, ⟨.no_trans (fun ⟨_, h⟩ => by cases h)⟩⟩
  | $ => ⟨$, ⟨.no_trans (fun ⟨_, h⟩ => by cases h)⟩⟩
  | Srt m => ⟨Srt m, ⟨.no_trans (fun ⟨_, h⟩ => by cases h)⟩⟩
  | S.{[m, n, o]} => ⟨S.{[m, n, o]}, ⟨.no_trans (fun ⟨_, h⟩ => by cases h)⟩⟩
  | K.{[m, n]} => ⟨K.{[m, n]}, ⟨.no_trans (fun ⟨_, h⟩ => by cases h)⟩⟩
  | K'.{[m, n]} => ⟨K'.{[m, n]}, ⟨.no_trans (fun ⟨_, h⟩ => by cases h)⟩⟩

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

theorem Judge.sound : (infer e) = .some ⟨t, PLift.up proof⟩ → Judge t e := fun _ => proof

def Judge.complete (h : Judge t e) : (infer e).map (·.fst) = .some t := by
  induction h
  repeat rfl
  case app m fα b f xα x β' h_t_f h_t_x h_conv nbf ih₁ ih₂ =>
    simp at ih₁
    simp at ih₂
    have ⟨hp₁, heq₁⟩ := ih₁
    have ⟨hp₂, heq₂⟩ := ih₂
    simp [infer, heq₁, heq₂]
    exact ⟨h_conv, nbf.complete⟩

instance infer.instDecidable : Decidable (Judge α x) :=
  match h : infer x with
  | .some ⟨t, ⟨h_t_x⟩⟩ =>
    if heq : t = α then
      Decidable.isTrue <| heq ▸ h_t_x
    else by
      apply Decidable.isFalse
      intro h
      have h₁ := h.complete
      have h₂ := h_t_x.complete
      simp_all
  | .none => by
    apply Decidable.isFalse
    intro h
    have h₁ := h.complete
    simp_all

#eval (infer ⸨K.{[2, 2]} (Srt 1) ⸨K'.{[3, 2]} (Srt 2) (Srt 1) (Srt 1)⸩ (Srt 0) (Srt 0)⸩).map (·.fst)

def mk_I (α : Expr) (m : Level) : Expr :=
  let α := α
  -- y : α ~> Srt 1
  -- y z = (Srt 0)
  let y := ⸨(K'.{[2, m]}) (Srt 1) α (Srt 0)⸩
  -- x : α ~> ((Srt 1) ~> α)
  -- x z (y z) = K α (Srt 1) z (Srt 0)
  let x := ⸨(K'.{[m, 2]}) α (Srt 1)⸩

  -- (y z) : β x
  -- β x = Srt 1
  let β := ⸨(K'.{[3, m]}) (Srt 2) α (Srt 1)⸩
  -- x z (y z) : γ z (y z)
  -- γ z (y z) = α
  -- γ : α → (β x) → (Srt m)
  let γ := ⸨(K'.{[m.succ, m]}) ((~> m.succ) Srt 1, Srt m) α ⸨(K'.{[m.succ, 2]}) (Srt m) (Srt 1) α⸩⸩
  dbg_trace Std.format <| (infer γ).map (·.fst)

  ⸨(S.{[m, 2, m]}) α β γ x y⸩

#eval (infer (mk_I (Srt 2) 3)).map (·.fst)
