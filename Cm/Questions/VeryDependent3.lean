import Mathlib.Data.Nat.Notation

/-
  1. Can we redesign our Π syntax to use more positional arguments?
  Π t_in (Π t_in₂ (Π t_in₃ t_out))
  Each t_in gets the context applied.

  Note:
  - we can start off each combinator's type
  with a singleton

  Another note:
  - Tout should not have to manage maintaining its own context.

  2. Ideally, we don't carry around a context. We form it from scratch from (f x)
  We could encode the context in Π.

  What's challenging about carrying around ::[x, f]?
  We don't know how to type f if we want to project on the list.

  We will run into this issue at some point.
  Another potential approach is to carry each argument's type with it.

  3. Can we carry around x's type? Not easily.

  4. Can we include a Δ mapping register?

    Perhaps Δ is not required, and Δ does substitution?
    (Π t_in t_out) Δ = Π (t_in Δ) (t_out Δ)

    So we can actually just apply one argument at a time?

    This could be nice.

    This should not be a reduction rule, though,
    because it implies that sigma is a function.

    (Π t_in t_out) : Type

    id : Π (

  ::[

  (Π t_in t_out) Δ = (t_out Δ)

  3. Can we omit f as an argument, or at least supply its type instead, wrapped in Π?
-/

inductive Expr where
  | app    : Expr → Expr → Expr
  /- List-like objects
     They come with built-in projection.
     They are the mirror image of application "as data". -/
  | cons   : Expr → Expr → Expr
  /-
    ::[x, xs] lists are a special case. They are the mirror
    image of application as data. They internalize a projector
    argument π.
  -/
  | Prod   : Expr → Expr → Expr
  /-
    Our representation of curried function types.
    Π t_in t_out
  -/
  | Pi     : Expr → Expr → Expr
  | both   : Expr
  | const  : Expr
  | const' : Expr
  | id     : Expr
  -- downgrades a term to a type
  | nil    : Expr
  | ty     : Expr

syntax ident ".{" term,* "}"  : term
syntax "::[" term,+ "]"       : term
syntax "($" term,+ ")"        : term

macro_rules
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.cons $x ::[$xs,*])
  | `(($ $x:term) ) => `($x)
  | `(($ $f:term, $x:term )) => `(Expr.app $f $x)
  | `(($ $f, $x:term, $args:term,* )) =>
    `(($ (Expr.app $f $x), $args,*))

notation "Ty" => Expr.ty

open Expr

/-
(f : Π Tin Tout)
(x : ($ Tin, ::[x, (Π Tin Tout)]) (fst Ty Ty))
((f x : Tout ::[x, (Π Tin Tout)]) (snd Ty Ty))
-/

def fst (α β : Expr) (fn : Expr := ($ id, β)) : Expr :=
  ($ const', ::[β, ($ nil, β)], α, fn)

/-
The version of snd in PiCorr is kind of unfaithful.
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
Π (mk_arrow α β) (x : α) = ::[α, β]

This assumes the context looks like ::[(x : α), (Π Tin Tout)]
-/
def mk_arrow (α β : Expr) : Expr :=
  Pi ($ nil, α) ($ const', Ty, (Prod α Ty), β)

/-
::[a, b] (snd' α β fn_post)
= b fn_post

(a : β) (b : α)
-/
def snd' (α β : Expr) (γ : Expr := α) (fn_post : Expr := ($ id, α)) :=
  comp fn_post ($ const', (mk_arrow α γ), β, fn_post)

/-
id : Π (const' Ty Ty Ty) (Π (fst 
-/
abbrev id.type : Expr :=
  -- (α : Ty) ((x : α) → (_x α))
  Pi ($ nil, Ty) (Pi nil nil)

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
  | Pi  : IsStep ($ Pi Tin Tout, Δ) ($ Pi ($ Tin, Δ) ($ Tout, Δ))
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
     use type universes
     this module is just for answering reseach questions -/
  | ty        : ValidJudgment Ty Ty
  | cons      : ValidJudgment x α
    → ValidJudgment xs β
    → ValidJudgment ::[x, xs] (Prod α β)
  | Pi     : ValidJudgment (Pi dom cod) Ty
  --| id        : ValidJudgment id Π[::[nil, id, id], Ty]
  /-
    To check an app:
    - functions have type Π Tin Tout
    - (Π Tin Tout) Δ = (Π (Tin Δ) (Tout Δ)). This mimicks substitution.
    - (Π (Tin arg) (Tout arg))
    - (((f : Π Tin Tout) (x : α)) : (Tout x))
    - To check that x matches the domain, (Tin x)
  -/
  | app       : ValidJudgment f (Pi Tin Tout)
    → ValidJudgment x ($ Tin, x)
    → ValidJudgment ($ f, x) ($ Tout, x)
  | def_eq    : ValidJudgment e α
    → DefEq α β
    → ValidJudgment e β
