/-
This mkcons is a combinator, without fixed projectors.

Our notation for debruijn indices is quite nice.
The only annoyance:

- codomain types are kind of opaque.
- type of the entire list isn't clear.
- we should only substitute arguments, we should not compose.

- we can infer cons types, potentially.
However, it may be prudent to add type arguments.

⟪(::(πc, πf, πg){f, g} x)⟫ ⟪(πc πf πg (πf f x) (πg g x))⟫

- we should also simplify the macro for creating infer cons types.
- another question: is it even necessary to make it a point-free combinator
if we enable mapping? Mapping will be sufficient, I think.
- if we make it not a combinator, then we can infer types very nicely.

also, we can avoid nested applications.

- fst and snd probably should have type arguments.

- we will also need a data structure to represent sigma.
  - Keep in mind, we want to be able to treat sigma as a type when possible.
- the very last snd is the normalized value, so very last snd's type is the entire type.
- for cons, we only need a "terminal" type. everything else bubbles up from that. we can calculate this
in our reduction rule by "bubbling up".

Note: mkcons has a "terminal value" which we derive.
Note: mkcons does not need explicit type arguments, since its πf and πg are fixed.
they are dynamic anyway.

However, in order to plug mkcons in as a fixpoint,
we need the type arguments.

If we add α and β type arguments, the type is pretty easy.

x : α
β = new fst
γ = new snd

However, new fst and new snd are different from the cons map.

This type is δ

δ = new cons.

πf : ∀ (x : α)
mkcons α β : (

This might be fine.

Worry about this later. At the very least, we will need α β γ and δ.

πf f : ∀ (x : α), β x

πf : ∀ (f : ∀ (x : α), β x) (x : α), β x

etc.
-/

import Mathlib.Data.Nat.Notation
import Init.Meta.Defs

open Std Format

abbrev Level := ℕ

inductive Expr where
  | I      : Level → Expr
  | K      : Level → Level → Expr -- Dependent K
  | K'     : Level → Level → Expr -- Nondependent K
  | S      : Level → Level → Level → Expr -- Dependent S
  | mkcons : Expr -- (mkcons α β γ δ πcons (πf : ∀ (x : α), β x) (πg : ∀ (x : α)) f g x = πcons πf πg ⸨πf f x⸩ ⸨πg g x⸩
  | judge  : Expr  → Expr -- judge t is a freestanding expr
  /-
    Sorts:
  -/
  | type   : Level → Expr
  | prop   : Expr
  | sort   : Level → Expr
  /-
    Sigma projection:
    TODO: we will need explicit type arguments here of some kind.
  -/
  | fst    : Expr
  | snd    : Expr
  | app    : Expr → Expr → Expr

open Expr

declare_syntax_cat expr
declare_syntax_cat u_level
declare_syntax_cat atom
declare_syntax_cat sort
declare_syntax_cat sort_cat
declare_syntax_cat lit
declare_syntax_cat stmt
declare_syntax_cat app
declare_syntax_cat judgment
declare_syntax_cat declare
declare_syntax_cat assign
declare_syntax_cat substitution

syntax "#(" term ")" : lit

syntax num           : u_level
syntax ident         : u_level
syntax lit           : u_level

syntax "Type" : sort_cat
syntax "Prop" : sort_cat
syntax "Sort" : sort_cat

syntax sort_cat u_level : sort

syntax "*"                     : atom
syntax "(" expr ")"            : atom
syntax "__"                    : atom
syntax ident "[" u_level,* "]" : atom
syntax "::(" atom,* ")"        : atom
syntax "{" atom,+ "}"          : atom
syntax ":" atom                : atom
syntax lit                     : atom

syntax:50 (name := judge_all) atom ":" expr : judgment

-- assignments are always well-typed judgment
-- with an assigned value.
-- these are not core to the language,
-- but rather derived from operational semantics of cons.
syntax judgment ":=" atom  : declare
syntax atom ":=" atom      : declare

syntax "⟦" declare "⟧" : assign

syntax atom assign : substitution

syntax app atom : app
syntax atom     : app

syntax app          : expr
syntax judgment     : expr

