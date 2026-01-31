import Mathlib.Data.Nat.Notation

abbrev Level := ℕ

/-
Questions to answer with internalized projector argument:
1. Can we derive fst and snd?
- Can we emulate the old π combiantor with a projector arugment?
- We can derive application from π projection?
- Can we derive S from both + π(id)?
- Do we need a separate ::[] from Σ? Feels like we should
  be able to infer that it is a type from the second element.
- Do we need a separate nondependent pair? Feels useful.

If we can derive S from both + π(id), then this suggests
what I thought about Sigma.mk corresponding to terms
and Σ corresponding to types.
-/

/-
Universe levels omitted, since this AST is just for
answering research questions.
-/
inductive Expr where
  | app    : Expr → Expr → Expr
  | cons   : Expr → Expr → Expr
  | π      : Expr
  | fst    : Expr
  | snd    : Expr
  | both   : Expr
  | const  : Expr
  | const' : Expr
  | id     : Expr
  -- downgrades a term to a type
  | nil    : Expr
  | ty     : Expr

syntax ident ".{" term,* "}" : term
syntax "::[" term,+ "]"      : term
syntax "($" term,+ ")"       : term
syntax (name := atDollar) "@$" term:max term:max term:max term:max term:max term:max : term

macro_rules
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.cons $x ::[$xs,*])
  | `(($ $x:term) ) => `($x)
  | `(($ $f:term, $x:term )) => `(Expr.app $f $x)
  | `(($ $f, $x:term, $args:term,* )) =>
    `(($ (Expr.app $f $x), $args,*))

notation "Ty" => Expr.ty

open Expr

namespace der_fst_intr_proj

/-
Question 1.

Can we derive fst and snd from π projector argument?
This version has evaluation rules for fst and snd
and for π.

This assumes that fst has a projector argument
and that snd does.

Is the projector argument also possible with internalized π?

This version uses this eval rule for snd:
snd π ::[a, b] = π b a

And this projector evaluation rule.
::[a, b] π = π b a

One thing to note: deriving fst from the internal
projector requires having const and nil combinators,
though we would likely need this with fst and snd anyway.
^ not sure about this last one though.

The massive advantage to using the internalized approach is that
we can infer α and β, since ::[] is a special case.
-/

inductive IsStep : Expr → Expr → Prop
  | sapp   : IsStep ($ ::[x, f], fn) ($ fn, f, x)
  | fst    : IsStep ($ fst, _α, _β, fn, ::[x, f]) ($ fn, x)
  | snd    : IsStep ($ snd, _α, _β, fn, ::[x, f]) ($ fn, f, x)
  | nil    : IsStep ($ nil, α, x) α
  | id     : IsStep ($ Expr.id, _α, x) x
  | const' : IsStep ($ const', _α, _β, x, y) x
  | left   : IsStep f f'
    → IsStep ($ f, x) ($ f', x)
  | right  : IsStep x x'
    → IsStep ($ f, x) ($ f, x')

inductive IsStepStar : Expr → Expr → Prop
  | refl  : IsStepStar e e
  | trans : IsStep e₁ e₂
    → IsStepStar e₂ e₃
    → IsStepStar e₁ e₃

/-
Assuming that we don't substitute in the head position of contexts ::[a, b], only the tail.

fst α β ::[head, tail] = head
::[head, tail] ($ const', ::[β, nil β], α, (id β)) = (id β) head = head

Internalized fst projection and explicit fst combinator are equally expressive.
-/
theorem fst_der (head tail fn : Expr) : IsStep ($ fst, _α, _β, fn, ::[head, tail]) ($ fn, head) ↔
  IsStepStar ($ ::[head, tail], ($ const', ::[β, ($ nil, β)], α, fn)) ($ fn, head) := by
  constructor
  intro h_step
  cases h_step
  apply IsStepStar.trans
  apply IsStep.sapp
  apply IsStepStar.trans
  apply IsStep.left
  apply IsStep.const'
  apply IsStepStar.refl
  intro h_step
  cases h_step
  case mpr.trans e₂ h_step h_trans =>
    cases h_trans
    apply IsStep.fst
    apply IsStep.fst

/-
snd α β fn ::[head, tail] = ::[head, tail] fn
  = fn tail head
-/
theorem snd_der (head tail fn : Expr) : IsStep ($ snd, _α, _β, fn, ::[head, tail]) ($ fn, tail, head) ↔ IsStepStar ($ ::[head, tail], fn) ($ fn, tail, head) := by
  constructor
  intro h_step; cases h_step
  apply IsStepStar.trans; apply IsStep.sapp
  apply IsStepStar.refl
  case mp.right a =>
    cases a
  intro h_step
  cases h_step
  apply IsStep.snd

end der_fst_intr_proj

namespace der_app_proj

/-
  Same IsStep as above, but without fst and snd,
  since we have proven they are in bijection.

  Also added the both combinator, since it is analagous
  to S.
-/
inductive IsStep : Expr → Expr → Prop
  | sapp   : IsStep ($ ::[x, f], fn) ($ fn, f, x)
  | nil    : IsStep ($ nil, α, x) α
  | id     : IsStep ($ Expr.id, _α, x) x
  | const' : IsStep ($ const', _α, _β, x, y) x
  | const  : IsStep ($ const, _α, _β, x, y) x
  -- f and g order is flipped here compared to S.
  -- both f g x = ::[(f x), (g x)]
  -- both f g x id = ::[(f x), (g x)]
  | both   : IsStep ($ both, _α, _β, _γ, f, g, x) ::[
  | left   : IsStep f f'
    → IsStep ($ f, x) ($ f', x)
  | right  : IsStep x x'
    → IsStep ($ f, x) ($ f, x')

theorem application_is_projection (t_f f x : Expr) : IsStep ($ f, x) e' ↔ IsStepStar ($ ::[x, f], (id t_f)) e' := by
  sorry

end der_app_proj
