/-

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

syntax ident "[" term,* "]"    : comb
syntax ident                   : comb

syntax "{" atom,* "}"          : atom
syntax "::(" atom,* ")"        : atom
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

syntax (name := mcomb) "c⟪" comb "⟫"        : term
syntax (name := msort) "srt⟪" sort "⟫"      : term
syntax (name := matom) "at⟪" atom "⟫"       : term
syntax (name := mapp) "a⟪" app "⟫"          : term
syntax (name := mexpr) "⟪" expr "⟫"         : term

@[macro msort] def parse_sort : Lean.Macro
  | `(srt⟪Type $n:atom⟫) => `(Expr.type at⟪$n:atom⟫)
  | `(srt⟪Sort $n:atom⟫) => `(Expr.sort at⟪$n:atom⟫)
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

@[macro mcomb] def parse_comb : Lean.Macro
  | `($c:ident [$args:term,*]) => `($c:term $args*)
  | `($c:ident) => `($c:term)
  | _ => Macro.throwUnsupported

@[macro matom] def parse_atom : Lean.Macro
  | `(at⟪($e:app)⟫) => `(a⟪$e:app⟫)
  | `(at⟪($e:expr)⟫) => `(⟪$e:expr⟫)
  | `(at⟪mkcons⟫) => `(Expr.mkcons)
  | `(at⟪::($πcons:atom, $πf:atom, $πg:atom)⟫) => `(a⟪mkcons $πcons $πf $πg⟫)
  | `(at⟪judge <| $α:atom⟫) => `(Expr.judge at⟪$α:atom⟫)
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
-- default behavior of the second component is that it will accept the next argument.
def mk_debruijn (n₁ : ℕ) (n₂ : Option ℕ := .none) : Lean.MacroM (Lean.TSyntax `atom) := do
  /-
    If we are at indxe 1, we will accept the argument. Otherwise, we will reject it.
  -/
  let mk_fetch (n : ℕ) : Lean.MacroM (Lean.TSyntax `app) :=
    if n == .succ .zero then
      `(app| I[0] Prop) -- only once we've hit debruijn index one we accept the argument
    else
      `(app| K'[0, 0] Prop Prop)

  let advance (inner : Lean.TSyntax `atom) : Lean.MacroM (Lean.TSyntax `atom) := do
    let map_f ← mk_fetch n₁
    let map_g ← (mk_fetch <$> n₂).getD `(app| I[0] Prop)
    -- if we don't care where substitutions get sent,
    -- e.g., if we are not the very tail of the list,
    -- we can usually leave n₂ alone.

    `(atom| ::($inner:atom, ($map_f:app), ($map_g:app)))

  match n₁ with
    | .succ n₁ =>
      match n₂ with
      | .some (.succ n₂) =>
        mk_debruijn n₁ n₂ >>= advance
      | .some .zero =>
        mk_debruijn n₁ (.some .zero) >>= advance
      | .none =>
        mk_debruijn n₁ .none >>= advance
    | .zero =>
      match n₂ with
      | .some (.succ n₂) => do
        mk_debruijn .zero n₂ >>= advance
      | .some .zero => do `(atom| ::(mkcons, (K'[0, 0] Prop Prop), (K'[0, 0] Prop Prop)))
      | .none => `(atom| ::(mkcons, (K'[0, 0] Prop Prop), (I[0] Prop)))

def allOuterIdents (base_vars : List (Lean.TSyntax `ident)) (e : Lean.TSyntax `app) : List (Lean.TSyntax `ident) :=
  match base_vars with
  | .nil => .nil
  | (.cons _x xs) =>
    match e with
    | `(app| $f:app $x:ident) =>
      (x :: allOuterIdents xs f)
    | `(app| $f:atom $x:ident) => [x]
    | _ => []

#eval (fun c => allOuterIdents [(Lean.mkIdent `x), (Lean.mkIdent `y)] c) <$> `(app| I[0] x y)

def parse_fall : Lean.Macro
  -- when there is only one head hypothesis, the conclusion
  -- may want a say in subbstitution
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
          let inner ← mk_debruijn debruijnIdx.succ .none
          `(app| $inner:atom ($f:app))
        | .none => Macro.throwError "variable missing in context"
      -- this slot does not take the variable as substitution.
      | f =>
        let inner ← mk_debruijn 0 .none
        `(app| $inner:atom ($f:expr))
    let init ← match conlude with
      | `(a⟪$f:app $var:ident⟫
    hyps.getElems.toList.foldrM (fun e fst => do
      `(a⟪$(← gen_debruijn e) $(⟨fst⟩):atom⟫))
      (init := conclude)
  | _ => Macro.throwUnsupported

@[macro mexpr] def parse_expr : Lean.Macro
  | s@`(⟪∀$_vars:binderlist, $_hyps:list⟫) => parse_fall s
  | `(⟪$s:sort⟫) => `(srt⟪$s:sort⟫)
  | `(⟪$a:atom⟫) => `(at⟪$a:atom⟫)
  | `(⟪$a:app⟫) => `(a⟪$a:app⟫)
  | `(⟪$c:comb⟫) => `(c⟪$c:comb⟫)
  | `(⟪$α:atom → $β:atom⟫) => do
    let myId ← Lean.withFreshMacroScope (pure <| Lean.mkIdent `my_x)
    `(⟪∀($myId:ident : $α:atom), [: $α:atom $myId:ident, $β:atom]⟫)
  | _ => Macro.throwUnsupported

#eval ⟪mkcons I[0]⟫
#eval ⟪I[1] (Type 0) Prop⟫

--#eval ⟪Prop → Prop⟫

--#eval ⟪∀(x : Type 2, y : Prop), [I[3] (Type 2) x, I[3]]⟫
