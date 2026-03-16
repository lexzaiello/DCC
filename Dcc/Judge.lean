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
TODO: add these back optionally
def Expr.transport (t : Expr) : Expr :=
  match t with
  | ⸨K'.{[_m, _n]} _α _β⸩
  | ⸨K.{[_m, _n]} _α _β⸩ => next
  | ⸨S.{[_m, _n, _o]} _α _β _γ⸩ => ⸨$ read⸩
  | Π.{[m]} α, ⸨next (Π.{[n]} β, γ)⸩ =>
    let α':= transport α
    let β' := transport β
    let γ' := transport γ
    Π.{[m]} α', (Π.{[n]} ⸨next β'⸩, ⸨next γ'⸩)
  | Π.{[m]} α, β =>
    let α':= transport α
    let β' := transport β
    Π.{[m]} α', β'
  | ⸨f x⸩ =>
    let f' := transport f
    let x' := transport x
    ⸨f' x'⸩
  | e => e
-/

inductive DefEq : Expr → Expr → Prop
  | step   : (∃ D, ParRed α₁ D ∧ ParRed α₂ D)
    → DefEq α₁ α₂
  | congr  : ¬ (∃ D, ParRed ⸨f x⸩ D ∧ ParRed ⸨g y⸩ D)
    → DefEq f g
    → DefEq x y
    → DefEq ⸨f x⸩ ⸨g y⸩
  | picong : ¬ (∃ D, ParRed (Π.{[m]} α, β) D ∧ ParRed (Π.{[m]} γ, δ) D)
    → DefEq α γ
    → DefEq β δ
    → DefEq (Π.{[m]} α, β) (Π.{[m]} γ, δ)

def is_def_eq (e₁ e₂ : Expr) : Option (PLift <| DefEq e₁ e₂) :=
  if h : ∃ D, ParRed e₁ D ∧ ParRed e₂ D then
    .some ⟨.step h⟩
  else
    match heq : e₁, e₂ with
    | ⸨f x⸩, ⸨g y⸩ =>
      match is_def_eq f g, is_def_eq x y with
      | .some ⟨p₁⟩, .some ⟨p₂⟩ =>
        .some ⟨.congr h p₁ p₂⟩
      | _, _ => .none
    | Π.{[m]} α, β, Π.{[n]} γ, δ =>
      if hm : m = n then
        match is_def_eq α γ, is_def_eq β δ with
        | .some ⟨p₁⟩, .some ⟨p₂⟩ =>
          have h := DefEq.picong (by rw [← hm] at h; exact h) p₁ p₂
          .some ⟨by rw [← hm]; exact h⟩
        | _, _ => .none
      else .none
    | _, _ => .none

theorem DefEq.sound : (is_def_eq e₁ e₂ = .some ⟨p⟩) → DefEq e₁ e₂ := fun _ => p

theorem DefEq.complete (h : DefEq e₁ e₂) : is_def_eq e₁ e₂ = .some ⟨h⟩ := by
  induction h
  · unfold is_def_eq
    simp_all
  repeat ({
    unfold is_def_eq
    split
    · simp_all
    simp
    rename_i df dg ih₁ ih₂ _
    simp [@ih₁, @ih₂]
  })

theorem DefEq.symm : DefEq A B → DefEq B A := by
  intro ha
  induction ha with
  | step h =>
    let ⟨D, h₁, h₂⟩ := h
    exact .step ⟨D, h₂, h₁⟩
  | congr ih =>
    apply DefEq.congr
    · simp_all
      intro x h h₂
      exact absurd h (ih _ (by assumption))
    repeat assumption
  | picong ih =>
    apply DefEq.picong
    · simp_all
      intro x h h₂
      exact absurd h (ih _ (by assumption))
    repeat assumption

theorem DefEq.diamond (h₁ : DefEq A B) (h₂ : DefEq A C) : ∃ D, DefEq B D ∧ DefEq C D := by
  have ha := h₁.complete
  have hb := h₂.complete
  
  refine ⟨_, .step ParRed.reduce_self' (by sorry) (by sorry), ?_⟩
  sorry

instance DefEq.instDecidable : Decidable (DefEq e₁ e₂) :=
  if h : (is_def_eq e₁ e₂).isSome then
    .isTrue ((is_def_eq e₁ e₂).get h).down
  else
    .isFalse (fun h => by
      have h₂ := h.complete
      simp_all)

inductive Judge : Expr → Expr → Prop
  | K     : Judge (K.type m n) K.{[m, n]}
  | K'    : Judge (K'.type m n) K'.{[m, n]}
  | S     : Judge (S.type m n o) S.{[m, n, o]}
  | Srt   : Judge (Srt m.succ) (Srt m)
  | Pi    : Judge (Srt m) (Π.{[m]} _α, _β)
  | app   : Judge (Π.{[m]} α₁, β) f → Judge α₂ x
    → DefEq α₁ α₂
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
    | ⟨Π.{[_m]} α₁, β, ⟨h_t_f⟩⟩, ⟨α₂, ⟨h_t_x⟩⟩ =>
      if h : DefEq α₁ α₂ then
        .some <| ⟨_, ⟨.app h_t_f h_t_x h (RunPi.sound
          (e_arg := x)
          (e_pi := β) rfl)⟩⟩
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
    let h_app := Judge.app h_t_f hp₂ h_conv nbf
    simp_all
    exact nbf.complete

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

/-
S (α := Srt 1) (β := λ (x : α), α) (γ := λ (x : α) (y : α) K'.{[m, m]})
-/

--#eval (infer ).map (·.fst)

#eval (infer ⸨K'.{[3, 3]} (Srt 2) (Srt 2)⸩).map (·.fst)

/-
x : (x : Srt 2) ~> Srt 2 ~> x

inner = K'.{[2, 3]} (Srt 1) (Srt 2)

x = K.{[3, 3]} (Srt 2)
-/

/-
Need transport for this to work.
def test_S : Option Expr := do
  let s := S.{[3, 3, 3]}
  let α := (Srt 2)
  let z := (Srt 1)
  let y := ⸨K'.{[3, 3]} (Srt 2) (Srt 2)⸩
  let β ← match Sigma.fst <$> infer ⸨y (Srt 1)⸩ with
  | .some β => do
    match ← Sigma.fst <$> infer α with
    | Srt out => .some ⸨K'.{[(out + 1), 3]} (Srt out) α β⸩
    | _ => .none
  | _ => none
  let t_yz ← (Sigma.fst <$> infer ⸨y z⸩)
  let t_t_yz ← Sigma.fst <$> infer t_yz
  let x ← match (Sigma.fst <$> infer t_yz) with
  | Srt m => .some ⸨K'.{[3, m]} α t_yz⸩
  | _ => .none
  let γ : Expr := ← (do
    let t_xzyz ← Sigma.fst <$> infer ⸨x z ⸨y z⸩⸩
    let t_t_xzyz ← Sigma.fst <$> infer t_xzyz
    match t_xzyz, t_t_xzyz, t_t_yz with
    | t_out, (Srt out), Srt yzm =>
      let inner := ⸨K'.{[out.succ, yzm]} (Srt out) t_yz t_out⸩
      let t_inner ← Sigma.fst <$> (infer inner)
      match ← Sigma.fst <$> infer t_inner with
      | Srt in_m =>
        .some ⸨K'.{[in_m, 3]} t_inner α inner⸩
      | _ => .none
    | _, _, _ => .none
  )
  Sigma.fst <$> infer ⸨s α β γ x y z⸩

#eval test_S.map (fun e => Sigma.fst <| reduce <| Sigma.fst <| reduce e)
-/
