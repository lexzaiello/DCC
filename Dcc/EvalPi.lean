import Dcc.Ast
import Dcc.Eval

/-
All arguments reduce at least one step for each argument applied.
-/

inductive Expr.RedPi : Expr → Expr → Prop
  | pi    : Expr.RedPi (SK (α x)) α'
    → Expr.RedPi (SK (β x)) β'
    → Expr.RedPi (SK ((Π α, β) x)) (SK (Π α', β'))
  | ty    : Expr.RedTyTrans e e'
    → IsNorm e'
    → Expr.RedPi e e'

def Expr.red_pi : Expr → Option Expr
  | SK ((Π α, β) x) =>
    match Expr.red_pi (SK (α x)), Expr.red_pi (SK (β x)) with
    | .some α', .some β' =>
      .some (SK (Π α', β'))
    | _, _ => .none
  | e =>
    if _heq : Expr.reduce e = e then
      .none
    else
      .some (Expr.reduce e)

theorem Expr.RedPi.sound : Expr.red_pi t = .some t' → Expr.RedPi t t' := by
  intro h
  unfold Expr.red_pi at h
  simp at h
  split at h
  · rename_i x' α β x
    split at h
    · rename_i heq₁ heq₂
      simp_all
      exact h.symm ▸ Expr.RedPi.pi (Expr.RedPi.sound heq₁) (Expr.RedPi.sound heq₂)
    · contradiction
  · rename_i x' heq
    simp at h
    have ⟨nheq, hr'⟩ := h
    have h : Relation.ReflTransGen RedTy t t' := reduce_sound hr'
    rw [← Relation.reflGen_transGen] at h
    cases h
    · contradiction
    · rename_i ih; exact RedPi.ty ih (reduce_norm hr')

/-
Size of a function.

The core combinators have a fixed number of arguments.
Eventually, their codomain resolves with an actual application.

Just count the number of β binders the way down. This corresponds to the number
of arguments accepted.
-/
inductive Expr.PiSize : Expr → ℕ → Prop
  | pi : Expr.PiSize β m
    → Expr.PiSize (SK (Π α, β)) (m + 1)
  | ty : Expr.TySize β (m + 1)
    → Expr.PiSize (SK (Π α, β)) ((m + 1) + 1)

def Expr.pi_size : Expr → Option ℕ
  | SK (Π _α, β) =>
    match Expr.ty_size β with
    | .zero => match Expr.pi_size β with
      | .some m => .some (m + 1)
      | .none => .none
    | .succ n => .some ((n + 1) + 1)
  | _ => .none

theorem Expr.PiSize.complete : Expr.PiSize e n → Expr.pi_size e = .some n := by
  intro h
  induction h
  · unfold Expr.pi_size
    rename_i ih
    split
    · simp_all
    · simp_all
      unfold Expr.pi_size at ih
      split at ih
      split at ih
      simp_all
      split at ih
      · contradiction
      · contradiction
      · contradiction
      simp_all only [imp_false, reduceCtorEq]
  · unfold Expr.pi_size
    rename_i ht
    have h := Expr.TySize.complete ht
    simp_all only

theorem Expr.PiSize.sound : Expr.pi_size e = .some n → Expr.PiSize e n := by
  intro h
  unfold Expr.pi_size at h
  split at h
  · rename_i x α β
    split at h
    · rename_i x heq
      split at h
      · simp_all only [Nat.zero_eq, Option.some.injEq]
        rename_i hsize₂
        exact h.symm ▸ Expr.PiSize.pi (Expr.PiSize.sound hsize₂)
      · contradiction
    · rename_i x hβsize
      simp_all
      exact h.symm ▸ Expr.PiSize.ty (Expr.TySize.sound hβsize)
  · contradiction

-- For checking codomain of app types.
inductive Expr.RedAppTy : Expr → Expr → Prop
  | mk : Expr.RedPi (SK (β x)) β'
    → Expr.RedAppTy (SK ((Π α, β) x)) β'

theorem app_size_dec : Expr.RedAppTy t t' → Expr.PiSize t m → Expr.PiSize t' n → n < m := by
  intro hr hm hn
  induction hm
  cases hr
  cases hr

def Expr.red_app_ty : Expr → Option Expr
  | SK ((Π _α, β) x) => Expr.red_pi (SK (β x))
  | _ => .none

theorem red_app_ty_sound : Expr.red_app_ty e = .some e' → Expr.RedAppTy e e' := by
  intro h
  unfold Expr.red_app_ty at h
  split at h
  · rename_i x₁ α β x
    have h := Expr.RedPi.sound h
    exact Expr.RedAppTy.mk h
  · contradiction
