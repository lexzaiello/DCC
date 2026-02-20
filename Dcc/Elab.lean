import Dcc.Ast
import Lean.Elab.Term.TermElabM
import Qq
open Qq

open Lean.Elab.Term
open Lean.Elab.Level
open Lean.Meta
open Lean (Syntax)
open Lean.Meta (inferType)

/-
Utility for auto-generating mkcons list configurations
from the terms inside them.
-/

/-
A central goal for the dependent list calculus is to support variable substitution in a friendly,
expressive, and performant way.

In a previous iteration, I achieved random access variable substitution in sigma lists.
However, users could only substitute one variable, not multiple.

Specifically, variables could only be substituted onto the outermost application of a function
occuyping the head position of a sigma list.

I have also shown previously that application can be derived from sigma by setting πcons, πf,
and πg = I.

In this sense, mkcons supports a wide range of list programming. I have been most interested
latey in tree substitution.

- model a function application as a tree
- if a branch does not contain any variables that would be substituted
by the context, bind it to debruijn index 0, thereby rejecting all future arguments.
- also note that by setting πcons, πf, and πg to I, the argument x would be substituted,
and the resulting fst and snd components would be applied together,
thereby effectuating single-step tree substitution.

- this is essentially a 2d generalization of my ∀ lists.
-/

/-
This is the expression used to sbustitute one layer into a tree.

mkcons I I I f g x = I I I (I f x) (I g x)

Note that mkcons _ _ _ f g is defined to be ::[f, g].
However, since πcons injected multiple identities, the end result is
the substituted components being applied together.

This could be used for tree substitution.
-/

open Expr

elab_rules : term
  | `(⟪$α:comb → $β:comb⟫) => do
    let α' ← (elabTerm · none) =<< `(⟪$α⟫)
    let β' ← (elabTerm · none) =<< `(⟪$β⟫)
    let t_α ← inferType α'
    let t_β ← inferType β'

    let qα : Q(Expr) := α'
    let qβ : Q(Expr) := β'

    match t_α, t_β with
    | .sort m, .sort n =>
      return q(Expr.app (Expr.app (Expr.cons $m $n) $qα) $qβ)
    | _, _ => throwError m!"Expected a type, but found {α}"

#eval ⟪Prop → Prop⟫

/-
/-
Forms an arrow type for a judgment α → Prop.
This expects a combinator expression, not a lean expression.
-/
def mk_judge_t (α : Expr) : TermElabM Expr := do
  match ← α.toExpr with
  | ~q(Sort $m) =>
    -- α → Prop corresponds to: mkcons (πf := K α) (πg := K β)
    ⟪::(mkcons.{$m, 
  | _ => throwError m!"Expected a type, but found {α}"
-/

/-
For simple arrows, we can set f to be Type m
πf to be I.{m + 1}
as a bootstrap.

we set πf.
-/

/-
Creates an arrow (α : Type m) → Type m
-/
/-def mk_raise_arrow (t tα : Lean.Expr) : TermElabM Expr := do
  match tα with
  | ~q(Sort $m) =>
    ⟪::(mkcons 
    sorry
  | _ => throwError m!"Expected a type, but found {α}"-/

/-
A simple arrow α → β corresponds to:

mkcons with f = α, g = β,
πf = K'.{m + 1, m} (Type m) α
πg = K'.{n + 1, n} (Type n) β
α := α
F = Type m
G = Type n
A = Type m
B = Type n

So substitution results in another list with just ::(α, β)
and which accepts NO type arguments.

The innermost mkcons is:
mkcons Prop (Type m) (Type n) Prop Prop

γ = Prop, I think.

πcons = mkcons

It is really annoying that we can't have mkcons be a genuine fixpoint.
really annoying.

mkcons expects tons of type arguments.

my question is: should the inner πcons have a dependent codomain?
feels very very extra. unnecessary.
Think about it.
Substitution should preserve types anyway.
-/

/-def type_to_comb_t (t : Lean.Expr) : TermElabM Expr := do
  match t with
  | .sort m => pure <| Expr.sort m
  -- α → β corresponds to mkcons (πf := K α) (πg := K α)
  | ~q($α → $β) =>
    match ← inferType α, ← inferType β with
    | ~q(Sort $m), ~q(Sort $n) =>
      let c_α ← type_to_comb_t α
      let c_β ← type_to_comb_t β

      ⟪cons.{m, n} c_α c_β⟫
    | _ => throwError "expected an arrow type"
  | _ => throwError "unsupported"-/

/-
Run before macros. This will attempt to resolve any holes
in the comb expression before further adjustments.

Things to fill:
- obvious type arguments where the argument has already been
supplied. these are kinda hard-coded.
- universe levels go last
-/
/-def fill_holes (s : Syntax) : TermElabM Expr :=
  match s with
  | `(comb| I.{_} _ $x:comb) => do
    let x' ← (toExpr <$> elabTerm x none  >>= inferType)
    sorry
  | `(comb| I.{_} $α:comb $x:comb) =>
    
  | `(comb| $f:comb $x:comb) =>
    sorry
  
  sorry-/

/-
Sigma lists are incredibly versatile, and suitable for many kinds of repetitive,
sometimes parallel computation (e.g, variable substitution).

A primtiive operation to sigma lists is debruijn-index substitution.
Specifically, a list may be modified by referencing positions in a predefined
context as corresponding to positions in the list. Typically, I use ∀ notation for this,
since it is somewhat familiar.

For example:
∀(x : α, y : β), ::(I α x, I β x)
Note that these lists are capable of continuously rejecting future arguments
once their value has been assigned. This property is a direct consequence
of sigma's generality.

This version of ∀ behaves the same way.It only substitutes values 1-layer
deep into the list.

However, it is very easy to derive composition with sigmas as well, and ∀
could absolutely be chained in the head position to induce inneft left-most
substitution.
-/
elab "⟪" "∀""(" c₁:comb,+ ")" "," c₂:comb "⟫" : term => do
  sorry


/-
For more flexible judgment expressions. More inference.
-/

-- want to do simple arrows using new toExpr powers
def arr : Expr := sorry

/-
In this configuration, f inevitably gets applied
with g. However, we can derive our conclusion from the type of f
and the type of g.

t_f ≃ 
-/
def joinlist (t_f t_g : Expr) : Expr :=
  sorry
