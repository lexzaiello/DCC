import Mathlib.Data.Nat.Notation
import Cm.Questions.Ast

open Expr

/-
Type inference of function application with very dependent types.

(f : Σ T)
(x : ($ T, ::[x, f]) (fst Ty Ty))
((f x : T ::[x, f]) (snd Ty Ty))
-/

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

/-
α type is dependent.
-/
def snd_dep (α β : Expr) : Expr :=
  ($ const, β, α)

/-
::[f, g] list
= list g f
-/
def comp (f g : Expr) : Expr :=
  ::[f, g]

def mk_both (α β γ f g : Expr) : Expr :=
  ($ both, α , β, γ, f, g)

/-
Arrows:
Σ (mk_arrow α β) (x : α) = ::[α, β]
-/
def mk_arrow (α β : Expr) : Expr :=
  sigma (mk_both (α := α)
      (β := ($ const', α, Ty, Ty))
      (γ := ($ const', α, Ty, Ty))
      (f := ($ nil, α))
      (g := ($ const, Ty, α, β)))

/-
::[a, b] (snd' α β fn_post)
= b fn_post

(a : β) (b : α)
-/
def snd' (α β : Expr) (γ : Expr := α) (fn_post : Expr := ($ id, α)) :=
  comp fn_post ($ const', (mk_arrow α γ), β, fn_post)

/-
Need something to represent the type of a pair.
Since we internalized the projector, the type becomes a little more complicated.
It's actually a function type.

::[x, α, id] π = π ::[α, id] x
-/
abbrev id.type : Expr :=
  /-
    Want ::[α, α]
    Tid₂ has α in scope.
    Tid₂ then accepts ::[x, α, id]
  -/
  let Tid₂ : Expr := sigma (snd'
    sorry
    sorry
    sorry
    (fst Ty sorry (mk_both Ty ($ nil, Ty) ($ nil, Ty) ($ id, Ty) ($ id, Ty))))
  sigma (fst
      Tid₂
      ($ nil, Ty)
      (mk_both (α := Ty) (β := Ty) (γ := Ty)
        (f := ($ nil, Ty))
        (g := ($ nil, Tid₂))))

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
  | sigma  : IsStep ($ sigma T, x) ($ T, x)
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

/-
::[(x : α), (xs : β)] : {γ : β → α → Type} (π : ∀ (x : β) (y : α), γ x y), γ xs x
::[x, xs] : (prod α β)

∀ (x : β) (y : α), γ x y
we can type as

this is another problem.
Σ does not capture all of ::[]

Σ should be Σ t_in t_out

feels like we shouldn't include f as an argument.
is there a way to do this without a special case?

id : Σ (const' Ty (prod ? Ty) Ty) (Σ t_out

if we type ::[x, xs] as prod α β,

can we just make a rule that say sapplying (? : prod α β)
-/

inductive ValidJudgment : Expr → Expr → Prop
  /- TODO: Remove this in the actual calculus
     use type universes
     this module is just for answering reseach questions -/
  | ty        : ValidJudgment Ty Ty
  | cons      : ValidJudgment x α
    → ValidJudgment xs β
    → ValidJudgment ::[x, xs] (prod α β)
  | sapp      : ValidJudgment f (prod α β)
    → ValidJudgment π (
  | sigma     : ValidJudgment (sigma Γ) Ty
  --| id        : ValidJudgment id Σ[::[nil, id, id], Ty]
  /-
    To check an app:
    - functions have type Σ T
    - (((f : Σ T) (x : α)) : ((T ::[x, f]) snd))
    - Body of f's type Σ T receives ::[x, f] via list application:
      ($ ::[x, f] T)
    - Body of f's type produces ::[t_in, t_out]
    - Type of (f x) is ::[t_in, t_out] snd
  -/
  | app       : ValidJudgment f (sigma T)
    → ValidJudgment x ($ ($ T, ::[x, f]), (fst Ty Ty))
    → ValidJudgment ($ f, x) ($ ($ T, ::[x, f]), (snd Ty Ty))
  | def_eq    : ValidJudgment e α
    → DefEq α β
    → ValidJudgment e β
