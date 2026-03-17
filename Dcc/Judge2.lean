import Dcc.Ast2
import Dcc.Eval2
import Mathlib.Data.Nat.Notation

def K.type (m n : Level) : Expr := (SK
  Π Sort m, Π (Π #(arg 0), Sort n), Π #((arg 0).ret 1), Π #(arg 1), #((arg 0).ret 3))

--#eval Std.format <| ((K.type 1 1).reduce_pi (SK Sort 0)).fst

def K'.type (m n : Level) : Expr :=
  SK Π Sort m, Π Sort n, Π #((arg 0).ret 1), Π #((arg 1).ret 1), #((arg 0).ret 3)

@[simp] abbrev S.type (m n o : Level) : Expr := SK
    Π Sort m, -- α
    Π (Π #(arg 0), Sort n), -- β
    Π (Π #((arg 0).ret 1), Π #(arg 1), Sort o), -- γ
    Π (Π #((arg 0).ret 2), Π #((arg 1).ret 1), #(arg 2)), -- x
    Π (Π #((arg 0).ret 3), #((arg 1).ret 2)), -- y
    Π #((arg 0).ret 4), -- z
      (B (S.{[m, n, o.succ]} (__ ∶ Sort m) (__ ∶ Sort n) (__ ∶ Sort o)) #((arg 2).ret 1)) -- γ z (y z)
-- ^ note that this is safe, since prior apps were type-checked, and def-eq here is deferred to term-level

@[simp] def Expr.pi_size_of : Expr → ℕ
  | (Π' α, β) => α.pi_size_of + β.pi_size_of
  | K* => 2
  | B
  | C => 3
  | I => 1
  | ⸨I _x⸩ => 0
  | ⸨B _f⸩ => 2
  | ⸨B _f _g⸩ => 1
  | ⸨B _f _g _x⸩ => 0
  | ⸨C _x⸩ => 2
  | ⸨C _x _y⸩ => 1
  | ⸨C _x _y _z⸩ => 0
  | ⸨f x⸩ => f.pi_size_of + x.pi_size_of
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

instance Expr.IsNotBinder.instDecidable : Decidable (Expr.IsNotBinder e) :=
  if h : e.is_not_binder.isSome then
    .isTrue (e.is_not_binder.get h).down
  else
    .isFalse (fun h => by simp [h.complete] at *)

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
  if h : in_e.is_not_binder.isSome then
    let h_e := in_e.is_not_binder.get h
    ⟨⸨in_e arg⸩.red_ty_comb.fst, ⟨.app h_e.down ⸨in_e arg⸩.red_ty_comb.snd.down⟩⟩
  else
    match in_e with
    | Π' α, β =>
      let ⟨α', ⟨h₁⟩⟩ := run_pi arg α
      let ⟨β', ⟨h₂⟩⟩ := run_pi arg β
      ⟨(Π' α', β'), ⟨.pi h₁ h₂⟩⟩

theorem RunPi.sound : run_pi arg in_e = ⟨e', ⟨h⟩⟩ → RunPi arg in_e e' := fun heq => by
  simp_all

theorem RunPi.complete (h : RunPi arg in_e e') : run_pi arg in_e = ⟨e', ⟨h⟩⟩ := by
  induction h
  · rename_i  α α' β β' ha hb ih₁ ih₂
    dsimp [run_pi, Expr.is_not_binder]
    simp_all
    congr
    repeat simp_all
  · rename_i e e' ih
    let h := ih.complete
    simp [run_pi, e'.complete]
    exact ⟨h, by congr; expose_names; exact heq_of_eqRec_eq (congrArg (RunPi arg e_1) h) rfl⟩

instance RunPi.instDecidable : Decidable (RunPi arg in_e e') :=
  let h := run_pi arg in_e
  if heq : h.fst = e' then
    .isTrue (heq ▸ h.snd.down)
  else
    .isFalse (fun h' =>
      have ha := h'.complete
      have hb := h.snd.down.complete
      False.elim <| heq (by simp_all))

def Expr.n_ty_comb : Expr → ℕ
  | C | B | K* | I => 1
  | Π' α, β => α.n_ty_comb + β.n_ty_comb
  | ⸨f x⸩ => f.n_ty_comb + x.n_ty_comb
  | _e => 0

def Expr.is_pi : Expr → Bool
  | Π' _α, _β => true
  | _e => false

theorem RedTyComb.basically_well_founded : 0 < Expr.pi_size_of e → e.RedTyComb e' → e'.pi_size_of < e.pi_size_of := by
  intro hnpos hred
  induction hred
  simp [Expr.pi_size_of] at *
  

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
