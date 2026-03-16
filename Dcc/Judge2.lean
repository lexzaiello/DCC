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

inductive Expr.IsNotBinder : Expr → Prop
  | app      : IsNotBinder ⸨f x⸩
  | comb_tm  : IsNotBinder (.comb c)
  | comb_ty  : IsNotBinder (.tycomb c)
  | srt      : IsNotBinder (Srt m)
  | ty_hole  : IsNotBinder (.tyhole t)

def Expr.is_not_binder (e : Expr) : Option (PLift e.IsNotBinder) :=
  match e with
  | Π' _α, _β => .none
  | ⸨_f _x⸩ => .some ⟨.app⟩
  | (.comb _c) => .some ⟨.comb_tm⟩
  | (.tycomb _c) => .some ⟨.comb_ty⟩
  | Srt _m => .some ⟨.srt⟩
  | .tyhole _t => .some ⟨.ty_hole⟩

def Expr.IsNotBinder.sound (_h : (Expr.is_not_binder e) = .some ⟨p⟩) : e.IsNotBinder := p

def Expr.IsNotBinder.complete (_h : Expr.IsNotBinder e) : e.is_not_binder.isSome := by
  cases _h
  repeat rfl

inductive RunPi (arg : Expr) : Expr → Expr → Prop
  | pi       : RunPi arg α α'
    → RunPi arg β β'
    → RunPi arg (Π' α, β) (Π' α', β')
  | app      : e.IsNotBinder
    → ⸨e arg⸩.RedTyComb e'
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

def run_pi (arg in_e : Expr) : (e' : Expr) × (PLift (RunPi arg in_e e')) :=
  match in_e with
  | Π' α, β =>
    let ⟨α', ⟨h₁⟩⟩ := run_pi arg α
    let ⟨β', ⟨h₂⟩⟩ := run_pi arg β
    ⟨(Π' α', β'), ⟨.pi h₁ h₂⟩⟩
  | e =>
    ⟨⸨in_e arg⸩.red_ty_comb.fst, ⟨.app ⸨in_e arg⸩.red_ty_comb.snd.down⟩⟩

theorem RunPi.sound {h : (run_pi arg in_e).isSome} : ((run_pi arg in_e).get h).fst = e' → RunPi arg in_e e' := fun heq => by
  have h := ((run_pi arg in_e).get h).snd.down
  rw [heq] at h
  exact h

theorem RunPi.complete (h : RunPi arg in_e e') : run_pi arg in_e = .some ⟨e', ⟨h⟩⟩ := by
  induction h
  · rename_i  α α' β β' ha hb ih₁ ih₂
    unfold run_pi
    unfold Expr.red_ty_comb
    unfold Expr.ty_is_redex
    unfold Expr.red_ty_comb
    unfold Expr.ty_is_redex
    simp [ih₁, ih₂]
  · rename_i e e' ih
    let h := ih.complete
    simp at h
    unfold run_pi
    simp [h]
    congr
    repeat simp [h]
    exact ih

def Expr.n_ty_comb : Expr → ℕ
  | C | B | K* | I => 1
  | Π' α, β => α.n_ty_comb + β.n_ty_comb
  | ⸨f x⸩ => f.n_ty_comb + x.n_ty_comb
  | _e => 0

def Expr.is_pi : Expr → Bool
  | Π' _α, _β => true
  | _e => false

theorem RunPi.basically_well_founded (h_n₀ : (Π' α, β).n_ty_comb > 0)
  (h_step : (run_pi any_arg (Π' α, β)).isSome) :
  ((run_pi any_arg (Π' α, β)).get h_step).fst.n_ty_comb < (Π' α, β).n_ty_comb := by
  have hr := (run_pi any_arg (Π' α, β)).get h_step
  unfold run_pi at h_step
  
  simp
  
  split at h_step
  · contradiction
  · rename_i h_step heq
    simp at h_step
    unfold run_pi
    simp_all
    
    sorry

/-
λ x => e₁ e₂

INVERT pi.

∀ (x : α) (y : β), α

forming a path.

typed holes are superior.
we can run RunPi with them to calculate types.
-/

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
