import Mathlib.Data.Nat.Notation
import Cm.Questions.Ast

open Expr

/-
For our very dependent types, it's 
-/

/-
nil β
fst accepts a projector.

α and β in list projections always refer to the x and xs elements,
respectively

::[(x : α), (xs : β)]

the projector π is of type β → γ
γ is set to be β by default,
since our argument is id

Technically, Σ is a combinator. So, we can put it in full list notation.
Although, this might not be ideal. ::[x, Σ T] is ideal.
-/
def fst (α β : Expr) (γ : Expr := β) (fn : Expr := ($ id, β)) : Expr :=
  ($ const', ::[β, ($ const', Ty, β, γ)], α, fn)


/-
::[a, b] flip = ::[b, a]

::[a, b] cons = cons b a = ::[b, a]
-/
def flip_list : Expr :=
  Expr.cons

/-
Type of ::[x, Σ (mk_arrow α β)]

::[a, b] pairs accept a π projector argument.
Otherwise, what is their type?

Worry about this later.
-/
def context.type : Expr :=
  sorry

/-
The version of snd in SigmaCorr is kind of unfaithful.
We might just want to select the second element and reject the first.

::[(a : α), (b : β)] snd' = b
const' β α

This version just fetches the second element.
-/
def snd (α β : Expr) : Expr :=
  ($ const', β, α)

/-
::[f, g] list
= list g f

::[a, b] g f
= g b a f
-/
def comp (f g : Expr) : Expr :=
  ::[f, g]

def mk_both (α β γ f g : Expr) : Expr :=
  ($ both, α , β, γ, f, g)

/-
New id type using our new inference rules.

ValidJudgment ($ f, x) ($ ($ T, ::[x, ($ Σ, T)]), (snd Ty Ty))

Tid ::[α, fix] = ::[Ty, Tid₂]

Issue here, again, is that we need to know the type of ::[Ty, Tid₂].
We may need more notation for this.

::[(Ty : Ty), (Tid₂ : Ty)] receives a projector. (π : Ty → Ty → 

Tid = (fst Ty Ty sorry, ($ const, sorry, Ty, ::[Ty, Tid₂]))

::[x, ::[α, ($ Σ, Tid)]]
tid₂ ::[x, α, ($ Σ, Tid)]

(id α) : ($ Σ, (Tid₂ α))

we lean on the evaluation rule for Σ here. (Σ bdy x) = (Σ (bdy x))
Tid = (fst Ty Ty sorry, ($ both, ?, ?, ?, ($ nil, Ty), ($ both, ?, ?, ?, Tid₂

α gets destroyed. We need to apply it to Tid₂.

ValidJudgmment f (Σ T)
ValidJudgment x ((T ::[x, (Σ T)]) (fst Ty Ty))

id : Σ (
-/
abbrev id.type : Expr :=
  let tid₂ := sorry
  (fst Ty Ty sorry, ($ const, sorry, Ty, ::[Ty, Σ id₂]))

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
  | sigma  : IsStep ($ Σ, Γ, x) ($ Γ, x)
  | nil    : IsStep ($ nil, α, x) α
  | id     : IsStep ($ Expr.id, _α, x) x
  /- Our most primitive, atomic datum is a list,
     so both is setup to do list-native application -/
  | both   : IsStep ($ both, _α, _β, _γ, f, g, x)
    ::[($ x, f), ($ x, g)]
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
     use type universes
     this module is just for answering reseach questions -/
  | ty        : ValidJudgment Ty Ty
  | sigma     : ValidJudgment ($ Σ, Γ) Ty
  --| id        : ValidJudgment id Σ[::[nil, id, id], Ty]
  /-
    To check an app:
    - functions have type Σ T
    - (((f : Σ T) (x : α)) : ((T ::[x, Σ T]) snd))
    - Body of f's type Σ T receives ::[x, Σ T] via list application:
      ($ ::[x, Σ T] T)
    - Fixpoint is useful to recover expected types later
    - Body of f's type produces ::[t_in, t_out]
    - Type of (f x) is ::[t_in, t_out] snd
  -/
  | app       : ValidJudgment f ($ Σ, T)
    → ValidJudgment x ($ ($ T, ::[x, ($ Σ, T)]), (fst Ty Ty))
    → ValidJudgment ($ f, x) ($ ($ T, ::[x, ($ Σ, T)]), (snd Ty Ty))
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
::[x, α, id]

both ? ? ? (

out_α_ty = ($ Σ, (both (

assert_α_ty = (fst Ty Ty ($ nil, Ty))
with_α_scope f = Σ ($ both, ($ nil, Ty), ($ nil Ty), assert_α_ty, 
id : Σ ($ both, (nil Ty), (nil Ty), assert_α_ty, (const' ? Ty (
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

