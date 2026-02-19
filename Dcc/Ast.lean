/-
New alert check.

mkcons we should ASSUME to produce objects which are judgments.

Every element in the list is EVENTUALLY going to be a Prop.

Another thing: we want to use mkcons to represent function types.

We could literally just say that mkcons is a type.

Specifically, in ::[], we assume:

f : α → Prop

::[] should be specifically for function types.

Its type should be the very last snd's final substituted value.

Each layer we push onto the very last element, we remove
a binder from its type, eventually producing Type.

The very last element in our list receives ALL our arguments. No indices.
This element has type α → β → γ → δ...

each layer up we go, we snd its type.

We are still using mostly untyped mkcons. no type argument parameters.

Another question I have:
should we not be able to infer ALL the types from jsut the variables in context?

Pretty sure we decided that cons lists will NOT produce props in their last codomain.
This will be a raw type, and it won't mention the application.

fst and snd could potentially be invisible to the user.
we can just use ∀.

Note: we aren't able to do cool substitution powers in the tail

This is something to think about more tomorrow, but it probably doesn't make sense to substitute
values in without knowing their types.

With judgments, we don't have to type anything.

Consider the ∀ list a special case where
-/

import Mathlib.Data.Nat.Notation
import Init.Meta.Defs

open Std Format
open Lean (Macro)
open Lean (MacroM)
open Lean (Syntax)

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
  | app    : Expr → Expr → Expr
deriving BEq

open Expr

declare_syntax_cat name
declare_syntax_cat operator
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
declare_syntax_cat arrow
declare_syntax_cat list
declare_syntax_cat fall
declare_syntax_cat binderlist
declare_syntax_cat binder

syntax "mkcons" : name
syntax "K"      : name
syntax "K'"     : name
syntax "S"      : name
syntax "I"      : name
syntax "judge"  : name

syntax "asvar"  : operator -- strip judgment information, if it is present
syntax "sortof" : operator
syntax "typeof" : operator
syntax "head"   : operator
syntax "tail"   : operator
syntax "judge"  : operator

syntax "#(" term ")" : lit

syntax num           : atom
syntax lit           : atom
syntax ident         : atom

syntax "Type" : sort_cat
syntax "Sort" : sort_cat

syntax sort_cat atom : sort
syntax "Prop"        : sort

syntax "[" expr,+ "]"                  : list

syntax ident ":" atom                 : binder
syntax "(" binder,* ")"               : binderlist
syntax "∀" binderlist "," list        : fall


-- ^ assumed debruijn, unless a human variable
-- is encountered
-- For keeping track of human variables

syntax name                    : comb
syntax name "[" atom,* "]"     : comb

syntax "{" atom,* "}"          : atom
syntax "::(" atom,* ")"        : atom
syntax name                    : atom
syntax comb                    : atom
syntax sort                    : atom
syntax:1000 "(" expr ")"       : atom
syntax ":" atom                : atom

syntax:50 atom ":" atom : judgment

-- assignments are always well-typed judgment
-- with an assigned value.
-- these are not core to the language,
-- but rather derived from operational semantics of cons.

syntax atom "→" atom           : arrow

syntax app atom : app
syntax atom     : app

syntax fall         : expr
syntax app          : expr
syntax judgment     : expr
syntax arrow        : expr
syntax:65 operator "<|" atom:65 : atom

syntax "c⟪" comb "⟫"                        : term
syntax (name := msort) "srt⟪" sort "⟫"      : term
syntax (name := matom) "at⟪" atom "⟫"       : term
syntax (name := mapp) "a⟪" app "⟫"          : term
syntax (name := mexpr) "⟪" expr "⟫"         : term

@[macro msort] def parse_sort : Lean.Macro
  | `(srt⟪Type $n:atom⟫) => `(Expr.type at⟪$n⟫)
  | `(srt⟪Sort $n:atom⟫) => `(Expr.sort at⟪$n⟫)
  | `(srt⟪Prop⟫) => `(Expr.prop)
  | _ => Macro.throwUnsupported

def parse_typeof : Lean.Macro
  | `(at⟪ typeof <| Sort $m:atom ⟫) => `(⟪Type $m:atom⟫)
  | `(at⟪ typeof <| Type $m:atom ⟫) => `(⟪Type #(1 + at⟪$m:atom⟫)⟫)
  | `(at⟪ typeof <| Prop ⟫)    => `(⟪Type 0⟫)
  | `(at⟪ typeof <| ($_x:atom : $t:atom) ⟫) => `(⟪$t:atom⟫)
  | `(⟪ typeof <| judge <| ($_x:atom : $_t:atom) ⟫) => `(⟪Prop⟫)
  | `(⟪ typeof <| : $T:atom⟫) => `(⟪$T:atom → Prop⟫)
  | `(at⟪ typeof <| (∀$_vars:binderlist, [$_dom:expr, $cod:expr]) ⟫) =>
    `(at⟪typeof <| ($cod:expr)⟫)
  | `(at⟪ typeof <| (∀$vars:binderlist, [$_dom:expr, $cod:expr,*]) ⟫) =>
    `(at⟪tail <| typeof <| (∀$vars:binderlist, [$cod:expr,*])⟫)
  | _ => Macro.throwUnsupported

def parse_asvar : Lean.Macro
  | `(⟪ asvar <| $x:atom $_t:atom ⟫) => pure x
  | `(⟪ asvar <| $x⟫) => pure x
  | _ => Macro.throwUnsupported

def parse_aoperator : Lean.Macro
  | `(at⟪ head <| judge <| ($x:atom : $_t:atom)⟫) => pure x
  | `(at⟪ tail <| judge <| ($_x:atom : $t:atom)⟫) => pure t
  | `(at⟪judge <| ($x:atom : $t:atom)⟫) => `(at⟪((: $t:atom) $x:atom)⟫)
  | s@`(at⟪ typeof <| $_e:atom⟫) => parse_typeof s
  | `(at⟪ sortof <| $e:atom ⟫) =>
    `(match at⟪$e:atom⟫ with
      | Expr.prop => 0
      | Expr.sort m => m
      | Expr.type m => m + 1
      | _ => 0)
  | s@`(at⟪ asvar  <| $_e:atom⟫) => parse_asvar s
  | `(at⟪ head <| ($x:atom : $_t:atom)⟫) => pure x
  | `(at⟪ tail <| ($_x:atom : $t:atom)⟫) => pure t
  | `(at⟪ head <| ($_a:atom {$a:atom, $_xs:atom,*})⟫) => pure a
  | `(at⟪ tail <| ($a:atom {$_a:atom, $xs:atom,*})⟫) => `(a⟪$a:atom {$xs:atom,*}⟫)
  | _ => Macro.throwUnsupported

@[macro matom] def parse_atom : Lean.Macro
  | `(at⟪($e:app)⟫) => `(a⟪$e:app⟫)
  | `(at⟪($e:expr)⟫) => `(⟪$e:expr⟫)
  | `(at⟪mkcons⟫) => `(Expr.mkcons)
  | `(at⟪::($πcons:atom, $πf:atom, $πg:atom)⟫) => `(a⟪mkcons $πcons $πf $πg⟫)
  | `(at⟪I[$m:atom]⟫) => `(Expr.I at⟪$m⟫)
  | `(at⟪S[$m:atom, $n:atom, $o:atom]⟫) => `(Expr.S at⟪$m⟫ at⟪$n⟫ at⟪$o⟫)
  | `(at⟪K'[$m:atom, $n:atom]⟫) => `(Expr.K' at⟪$m⟫ at⟪$n⟫)
  | `(at⟪K[$m:atom, $n:atom]⟫) => `(Expr.K at⟪$m⟫ at⟪$n⟫)
  | `(at⟪judge[$α:atom]⟫) => `(Expr.judge at⟪$α:atom⟫)
  | `(at⟪$s:sort⟫) => `(srt⟪$s:sort⟫)
  | `(at⟪$c:comb⟫) => `(c⟪$c:comb⟫)
  | `(at⟪$n:num⟫) => `($n)
  | `(at⟪#($t:term)⟫) => `($t)
  | `(at⟪: $T:atom⟫) => `(Expr.judge at⟪$T⟫)
  | s@`(at⟪$_op:operator <| $_a:atom⟫) => parse_aoperator s
  | _ => Macro.throwUnsupported

@[macro mapp] def parse_app : Lean.Macro
  | `(a⟪$a:atom⟫) => `(at⟪$a:atom⟫)
  | `(a⟪$a:atom $b:atom⟫) => `(Expr.app at⟪$a:atom⟫ at⟪$b:atom⟫)
  | `(a⟪$a:app $b:atom⟫) => `(Expr.app a⟪$a:app⟫ at⟪$b:atom⟫)
  | _ => Macro.throwUnsupported

-- If this variable is contained in vars, then look up the corresponding debruijn index
-- otherwise, insert the variable

-- debruijn index 0 corresponds to rejecting all future inputs
-- for the head
-- 1 corresponds to accepting the input
-- all others decrement from n to 1
-- this assumes that α is well-tyepd as a Type
def mk_debruijn (n' : ℕ) : Lean.MacroM (Lean.TSyntax `app) := do
  match n' with
  -- by this point, we could have substituted a variable in,
  -- and thus, we have produced some kind of judgment (slot : T)
  | .zero =>
    `(app| ::(mkcons, (K'[0, 0] Prop Prop), (I[0] Prop)))
  | .succ n' =>
    let inner ← mk_debruijn n'
    let map_f ← if n' == .succ .zero then
      `(atom| (I[0] Prop))
    else
      `(atom| (K'[0, 0] Prop))

    `(app| ::(($inner:app), $map_f:atom, (I[0] Prop)))

def parse_fall : Lean.Macro
  | `(⟪∀($vars:binder,*), [$hyps:expr,*, $conclude:atom]⟫) => do
    -- Finds the entry of an indexed variable judgment
    -- corresponding to a hypothesis binder
    let find_entry (var : Lean.TSyntax `ident) : Lean.TSyntax `binder × ℕ → Bool :=
          fun (⟨bind, _idx⟩ : Lean.TSyntax `binder × ℕ) => match bind with
          | `(binder| $v:ident : $_α:atom) => v == var
          | _ => false
    -- generates ::(a, b, c) head without f and g inserted.
    let gen_debruijn (fhead : Lean.TSyntax `expr) : MacroM (Lean.TSyntax `app) := do
      -- if a variable isn't in substitution position
      -- we can be fairly sure they will never need an argument.
      match fhead with
      | `(expr| $f:app $var:ident) =>
        match vars.getElems.toList.zipIdx.find? (find_entry var) with
        | .some (.mk _a debruijnIdx) =>
          let inner ← mk_debruijn debruijnIdx.succ
          `(app| $inner:app ($f:app))
        | .none => Macro.throwError "variable missing in context"
      -- this slot does not take the variable as substitution.
      | f => `(app| $(← mk_debruijn 0) ($f:expr))
    hyps.getElems.toList.foldrM (fun e fst => do
      `(a⟪$(← gen_debruijn e) $(⟨fst⟩):atom⟫))
      (init := conclude)
  | _ => Macro.throwUnsupported

@[macro mexpr] def parse_expr : Lean.Macro
  | s@`(⟪∀$_vars:binderlist, $_hyps:list⟫) => parse_fall s
  | `(⟪$s:sort⟫) => `(srt⟪$s:sort⟫)
  | `(⟪$a:atom⟫) => `(at⟪$a:atom⟫)
  | `(⟪$a:app⟫) => `(a⟪$a:app⟫)
  | `(⟪$α:atom → $β:atom⟫) => do
    let myId ← Lean.withFreshMacroScope (pure <| Lean.mkIdent `my_x)
    `(⟪∀($myId:ident : $α:atom), [: $α:atom $myId:ident, $β:atom]⟫)
  | _ => Macro.throwUnsupported

#eval ⟪mkcons I[0]⟫
#eval ⟪I[1] (Type 0) Prop⟫

#eval ⟪Prop → Prop⟫

#eval ⟪∀(x : Type 2, y : Prop), [I[3] (Type 2) x, I[3]]⟫
