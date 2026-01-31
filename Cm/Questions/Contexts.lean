import Mathlib.Data.Nat.Notation
import Cm.Questions.Ast

open Expr

def fst (α β : Expr) (fn : Expr := ($ id, β)) : Expr :=
  ($ const', ::[β, ($ nil, β)], α, fn)

/-
The version of snd in SigmaCorr is kind of unfaithful.
We might just want to select the second element and reject the first.

::[a, b] snd' = b
const' β α

This version just fetches the second element.
-/
def snd (α β : Expr) : Expr :=
  ($ const', β, α)

inductive IsStepStar {rel : Expr → Expr → Prop} : Expr → Expr → Prop
  | refl  : IsStepStar e e
  | trans : rel e₁ e₂
    → IsStepStar e₂ e₃
    → IsStepStar e₁ e₃

inductive IsBetaEq {s : Expr → Expr → Prop} : Expr → Expr → Prop where
  | rel   : s e₁ e₂ → IsBetaEq e₁ e₂
  | refl  : IsBetaEq e e
  | symm  : IsBetaEq e₁ e₂ → IsBetaEq e₂ e₁
  | trans : IsBetaEq e₁ e₂ → IsBetaEq e₂ e₃ → IsBetaEq e₁ e₃

inductive IsStep : Expr → Expr → Prop
  | sapp   : IsStep ($ ::[x, f], fn) ($ fn, f, x)
  | nil    : IsStep ($ nil, α, x) α
  | id     : IsStep ($ Expr.id, _α, x) x
  | both   : IsStep ($ both, _α, _β, _γ, f, g, x)
    ::[($ f, x), ($ g, x)]
  | const' : IsStep ($ const', _α, _β, x, y) x
  | left   : IsStep f f'
    → IsStep ($ f, x) ($ f', x)
  | right  : IsStep x x'
    → IsStep ($ f, x) ($ f, x')

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | step    : IsStep e e' → DefEq e e'
  | symm    : DefEq e₁ e₂ → DefEq e₂ e₁
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ($ f, x) ($ f', x)
  | right   : DefEq x x'  → DefEq ($ f, x) ($ f, x')
  | lright  : DefEq f f'  → DefEq ::[x, f] ::[x, f']
  | lleft   : DefEq x x'  → DefEq ::[x, f] ::[x', f]

inductive IsStepN : ℕ → Expr → Expr → Prop
  | one  : IsStep e e' → IsStepN 1 e e'
  | succ : IsStep e e'' → IsStepN n e'' e'''
    → IsStepN n.succ e e'''

inductive ValidJudgment : Expr → Expr → Prop
  /- TODO: Remove this in the actual calculus
     this module is just for answering reseach questions -/
  | ty        : ValidJudgment Ty Ty
  | sigma     : ValidJudgment ($ Σ', Γ) Ty
  --| id        : ValidJudgment id Σ[::[nil, id, id], Ty]
  | app       : ValidJudgment f ($ Σ', Γ)
    → ValidJudgment x ($ (fst Ty Ty), ($ Γ, ::[x, f]))
    → ValidJudgment ($ f, x) ($ snd Ty Ty, ($ Γ, ::[x, f]))
  | def_eq    : ValidJudgment e α
    → DefEq α β
    → ValidJudgment e β

/-
More universal application rule:

Question:
Γ, ::[x, f] or ::[x, f] Γ?

f : Σ T
f x : (snd (T ::[x, f]))
check x: (fst (T ::[x, f]))
-/

/-
id : Σ ($ both, (nil Ty), (nil Ty), (fst Ty Ty ($ nil, Ty))
-/

theorem id_α_well_typed : ValidJudgment α Ty → ValidJudgment ($ id, α) Σ[::[id, id], ::[::[α, Ty], Ty]] := by
  intro h_t
  apply ValidJudgment.def_eq
  apply ValidJudgment.app
  apply ValidJudgment.id
  apply ValidJudgment.def_eq h_t
  apply DefEq.symm
  apply DefEq.trans
  apply DefEq.step
  apply IsStep.sapp
  apply DefEq.step
  apply IsStep.nil
  apply DefEq.trans
  apply DefEq.sigma_t
  apply DefEq.lleft
  apply DefEq.lright
  apply DefEq.trans
  apply DefEq.step
  apply IsStep.sapp
  apply DefEq.step
  apply IsStep.nil
  apply DefEq.refl

example : ValidJudgment α Ty → ValidJudgment x α → ValidJudgment ($ id, α, x) α := by
  intro h_t h_t_x
  apply ValidJudgment.def_eq
  apply ValidJudgment.app
  exact (@id_α_well_typed α h_t)
  apply ValidJudgment.def_eq
  exact h_t_x
  
  sorry

