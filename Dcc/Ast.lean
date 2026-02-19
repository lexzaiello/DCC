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

Since α is a type, and β produces a type, we will need level arguments, too.

does πcons : tπc contain all the information we need?

almost certainly yes.

wait a second. we can fix the first argument of mkcons.
-/

import Mathlib.Data.Nat.Notation
import Init.Meta.Defs

open Std Format

abbrev Level := ℕ

inductive Expr where
  | I       : Level → Expr
  | K       : Level → Level → Expr -- Dependent K
  | K'      : Level → Level → Expr -- Nondependent K
  | S       : Level → Level → Level → Expr -- Dependent S
  | mkcons  : Expr
  -- ^ (mkcons πcons πf πg f g x) = (πcons πf πg (πf f x) (πg g x))
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
declare_syntax_cat atom
declare_syntax_cat comb
declare_syntax_cat sort
declare_syntax_cat sort_cat
declare_syntax_cat lit
declare_syntax_cat stmt
declare_syntax_cat app
declare_syntax_cat judgment
declare_syntax_cat declare
declare_syntax_cat assign
declare_syntax_cat substitution
declare_syntax_cat arrow
declare_syntax_cat fall
declare_syntax_cat cons

syntax "#(" term ")" : lit

syntax num           : atom
syntax ident         : atom
syntax lit           : atom

syntax "Type" : sort_cat
syntax "Sort" : sort_cat

syntax "::(" atom,* ")"                : cons
syntax "{" atom,+ "}"                  : cons
syntax "::=[" substitution,* "]"       : cons
-- ^ assumed debruijn, unless a human variable
-- is encountered
-- For keeping track of human variables
syntax "::={" ident,* "}[" substitution,* "]" : cons
syntax cons cons                                : cons

syntax ident "[" atom,* "]"        : comb
syntax "(" term ")" "[" atom,* "]" : comb

syntax comb                    : atom
syntax sort_cat atom           : atom
syntax "Prop"                  : atom
syntax "*"                     : atom
syntax "(" expr ")"            : atom
syntax "__"                    : atom
syntax ":" atom                : atom
syntax "judge(" judgment ")"   : atom

syntax:50 (name := judge_all) atom ":" expr : judgment

-- assignments are always well-typed judgment
-- with an assigned value.
-- these are not core to the language,
-- but rather derived from operational semantics of cons.
syntax judgment ":=" atom  : declare
syntax atom ":=" atom      : declare

syntax "⟦" declare "⟧" : assign

syntax atom "→" atom           : arrow
syntax "∀" judgment,+ "," atom : fall

syntax atom assign : substitution
syntax judgment    : substitution

syntax app atom : app
syntax atom     : app

syntax app          : expr
syntax judgment     : expr
syntax arrow        : expr
syntax substitution : expr
syntax cons         : expr

syntax "⟪" expr "⟫"      : term
syntax "a⟪" app "⟫"      : term
syntax "at⟪" atom "⟫"    : term
syntax "c⟪" comb "⟫"     : term
syntax "::⟪" cons "⟫"    : term
syntax "j⟪" judgment "⟫" : term

macro_rules
  -- TODO: fix to use new recursive mkcons
  /-| `(::⟪::(($α:atom : Type $m), ($β:atom : ($α:atom : Type $m) → (Type $n : Type #($n + 1))), ($γ:atom : ($α:atom : Type $m) → (Type $o : Type #($o + 1))), ($δ:atom : Type $p), $rst:atom,*)⟫) => do
    let inner ← `(app| (mkcons $m:atom $n:atom $o:atom $p:atom) $α:atom $β:atom $γ:atom $δ:atom)
    let args ← rst.getElems.toList.foldlM (fun acc e => `(app| $acc:app $e:atom)) inner
    `(a⟪$args⟫)-/
  | `(::⟪$a:cons {$f:atom,$g:atom,$xs:atom,*}⟫) => `(a⟪($a:cons) $f:atom ($a:cons {$g:atom, $xs:atom,*})⟫)
  | `(::⟪$a:cons {$f:atom,$g:atom}⟫) => `(a⟪($a:cons) $f:atom $g:atom⟫)
  -- We are substituting a variable.
  -- note that we always carry a set of variables seen so far
  -- and which debruijn indices they correspond to.
  | `(::⟪::=[$elems,*]⟫) => `(::⟪::={}[$elems,*]⟫)
  -- Note: this only works for letter variables
  | `(::⟪::={$vars:ident,*}[($f:atom ⟦__ : ($α:atom : Type $m:atom) := $var:ident⟧) : ($β:atom : Type $n:atom)
    , $g:atom : ($tg:atom : Type $o:atom)]⟫) => do
    let ret_g    ← `(atom| (I[$o:atom] $tg:atom))
    let judge_α  ← `(atom| ($α:atom : Type $m:atom))
    let judge_β  ← `(atom| ($β:atom : Type $n:atom))
    let norm_t_f ← `(atom| ($judge_α:atom → $judge_β:atom))

    -- If this variable is contained in vars, then look up the corresponding debruijn index
    -- otherwise, insert the variable

    -- debruijn index 0 corresponds to rejecting all future inputs
    -- for the head
    -- 1 corresponds to accepting the input
    -- all others decrement from n to 1
    let rec mk_debruijn (n' : ℕ) : Lean.MacroM (Lean.TSyntax `cons) := do
      match n' with
      | .zero => `(cons| ::(mkcons, (K'[$n:atom, $n:atom] $β:atom $β:atom), (I[$o:atom] $tg:atom)))
      | .succ n' =>
        let inner ← mk_debruijn n'
        let map_f ← if n' == .succ .zero then
          `(atom| (I[$n:atom] $norm_t_f:atom))
        else
          `(atom| (K'[$n:atom, $m:atom] $norm_t_f:atom))

        `(cons| ::(($inner:cons), $map_f:atom, $ret_g:atom))

    match vars.getElems.toList.findIdx? (· == var) with
    | .some debruijnIdx =>
      let inner ← mk_debruijn debruijnIdx
      `(::⟪$inner:cons {$f:atom,$g:atom}⟫)
    | .none =>
      -- Not contained in vars, so this is de bruijn index 0
      let inner ← mk_debruijn 0
      
      sorry
  | `(at⟪judge($x:atom : $t:atom)⟫) => `(⟪(judge $t:atom) $x:atom⟫)
  | `(⟪$c:cons⟫) => `(::⟪$c:cons⟫)
  | `(at⟪($a:atom)⟫) => `(at⟪$a:atom⟫)
  | `(at⟪($a:expr)⟫) => `(⟪$a:expr⟫)
  | `(at⟪$n:num⟫) => `($n)
  | `(at⟪$ide:ident⟫) => `($ide)
  | `(at⟪#($t:term)⟫) => `($t)
  | `(at⟪Type $n:atom⟫) => `(Expr.type at⟪$n⟫)
  | `(at⟪Sort $n:atom⟫) => `(Expr.sort at⟪$n⟫)
  | `(at⟪Prop⟫) => `(Expr.prop)
  | `(at⟪: $T:atom⟫) => `(Expr.judge at⟪$T⟫)
  | `(c⟪$comb:ident[]⟫) => `(at⟪$comb:ident⟫)
  | `(c⟪($comb:term)[]⟫) => `($comb)
  | `(c⟪$comb:ident[$u:atom, $xs:atom,*]⟫) =>`(c⟪($comb at⟪$u⟫)[$xs,*]⟫)
  | `(c⟪($comb:term)[$u:atom, $xs:atom,*]⟫) =>`(c⟪($comb at⟪$u⟫)[$xs,*]⟫)
