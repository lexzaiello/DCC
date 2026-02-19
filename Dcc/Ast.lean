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
declare_syntax_cat cons
declare_syntax_cat list
declare_syntax_cat fall
declare_syntax_cat binderlist

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
syntax ident         : atom
syntax lit           : atom

syntax "Type" : sort_cat
syntax "Sort" : sort_cat

syntax sort_cat atom : sort
syntax "Prop"        : sort

syntax "[" expr,+ "]"                  : list

syntax "(" judgment,+ ")"              : binderlist
syntax "∀" binderlist "," list        : fall

syntax "::(" atom,* ")"                : cons
syntax "∘(" atom,* ")"                 : cons
syntax "{" atom,+ "}"                  : cons
syntax cons cons                       : cons

-- ^ assumed debruijn, unless a human variable
-- is encountered
-- For keeping track of human variables

syntax name                    : comb
syntax name "[" atom,* "]"     : comb

syntax name                    : atom
syntax comb                    : atom
syntax sort                    : atom
syntax "*"                     : atom
syntax "(" expr ")"            : atom
syntax "__"                    : atom
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
syntax cons         : expr
syntax:65 operator "<|" atom:65 : atom

syntax "c⟪" comb "⟫"        : term
syntax (name := msort) "srt⟪" sort "⟫"      : term
syntax (name := matom) "at⟪" atom "⟫"       : term
syntax (name := mapp) "a⟪" app "⟫"          : term
syntax (name := mcons) "::⟪" cons "⟫"       : term
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
  | `(at⟪ head <| ($_a:cons {$a:atom, $_xs:atom,*})⟫) => pure a
  | `(at⟪ tail <| ($a:cons {$_a:atom, $xs:atom,*})⟫) => `(::⟪$a:cons {$xs:atom,*}⟫)
  | _ => Macro.throwUnsupported

@[macro matom] def parse_atom : Lean.Macro
  | `(at⟪mkcons⟫) => `(Expr.mkcons)
  | `(at⟪I[$m:atom]⟫) => `(Expr.I at⟪$m⟫)
  | `(at⟪S[$m:atom, $n:atom, $o:atom]⟫) => `(Expr.S at⟪$m⟫ at⟪$n⟫ at⟪$o⟫)
  | `(at⟪K'[$m:atom, $n:atom]⟫) => `(Expr.K' at⟪$m⟫ at⟪$n⟫)
  | `(at⟪K[$m:atom, $n:atom]⟫) => `(Expr.K at⟪$m⟫ at⟪$n⟫)
  | `(at⟪judge[$α:atom]⟫) => `(Expr.judge at⟪$α:atom⟫)
  | `(at⟪$s:sort⟫) => `(srt⟪$s:sort⟫)
  | `(at⟪$c:comb⟫) => `(c⟪$c:comb⟫)
  | `(at⟪($a:atom)⟫) => `(at⟪$a:atom⟫)
  | `(at⟪($a:expr)⟫) => `(⟪$a:expr⟫)
  | `(at⟪$n:num⟫) => `($n)
  | `(at⟪$ide:ident⟫) => `($ide)
  | `(at⟪#($t:term)⟫) => `($t)
  | `(at⟪: $T:atom⟫) => `(Expr.judge at⟪$T⟫)
  | s@`(at⟪$_op:operator <| $_a:atom⟫) => parse_aoperator s
  | _ => Macro.throwUnsupported

@[macro mapp] def parse_app : Lean.Macro
  | `(a⟪$a:atom⟫) => `(at⟪$a:atom⟫)
  | `(a⟪$a:app $b:atom $c:atom⟫) => `(Expr.app a⟪$a:app $b:atom⟫ at⟪$c:atom⟫)
  | `(a⟪$a:atom $b:atom⟫) => `(Expr.app at⟪$a⟫ at⟪$b⟫)
  | _ => Macro.throwUnsupported

@[macro mcons] def parse_cons : Lean.Macro
  | `(::⟪$a:cons {$f:atom,$g:atom,$xs:atom,*}⟫) =>
    `(a⟪($a:cons) $f:atom ($a:cons {$g:atom, $xs:atom,*})⟫)
  | `(::⟪$a:cons {$f:atom,$g:atom}⟫) =>
    `(a⟪($a:cons) $f:atom $g:atom⟫)
  | `(::⟪::($πcons:atom, $πf:atom, $πg:atom)⟫) =>
    `(⟪mkcons $πcons $πf $πg⟫)
  | _ => Macro.throwUnsupported

-- If this variable is contained in vars, then look up the corresponding debruijn index
-- otherwise, insert the variable

-- debruijn index 0 corresponds to rejecting all future inputs
-- for the head
-- 1 corresponds to accepting the input
-- all others decrement from n to 1
-- this assumes that α is well-tyepd as a Type
def mk_debruijn (α β tg : Lean.TSyntax `atom) (n' : ℕ) : Lean.MacroM (Lean.TSyntax `cons) := do
  let m ← `(at⟪sortof <| typeof <| $α:atom⟫)
  let n ← `(at⟪sortof <| typeof <| $β:atom⟫)
  let o ← `(at⟪sortof <| typeof <| $tg:atom⟫)
  let ret_g    ← `(atom| (I[#($o:term)] $tg:atom))
  let judge_α  ← `(atom| ($α:atom : Type #($m:term)))
  let judge_β  ← `(atom| ($β:atom : Type #($n:term)))
  let norm_t_f ← `(atom| ($judge_α:atom → $judge_β:atom))
  match n' with
  | .zero => `(cons| ::(mkcons, (K'[#($n:term), #($n:term)] $β:atom $β:atom), (I[#($o:term)] $tg:atom)))
  | .succ n' =>
    let inner ← mk_debruijn α β tg n'
    let map_f ← if n' == .succ .zero then
      `(atom| (I[#($n:term)] $norm_t_f:atom))
    else
      `(atom| (K'[#($n:term), #($m:term)] $norm_t_f:atom))

    `(cons| ::(($inner:cons), $map_f:atom, $ret_g:atom))

def parse_fall : Lean.Macro
  | `(⟪∀($vars:judgment,*), [$hyps:expr,*, $conclude:atom : $why:atom]⟫) => do
    -- Finds the entry of an indexed variable judgment
    -- corresponding to a hypothesis binder
    let TJudge' := Prod (Lean.MacroM (Lean.TSyntax `atom)) (Lean.MacroM (Lean.TSyntax `atom))
    let find_entry (var : Lean.TSyntax `term) : Lean.TSyntax `judgment × ℕ → Lean.MacroM Bool :=
          fun (⟨judgmt, _idx⟩ : Lean.TSyntax `judgment × ℕ) => match judgmt with
          | `(judgment| $v:ident : $_α:atom) => do
            pure <| (← `($v)) == var
          | _ => pure false
    let Ctx := Lean.MacroM (Lean.TSyntax `binderlist)
    -- generates ::(a, b, c) head without f and g inserted.
    let gen_debruijn (fhead : Lean.TSyntax `expr) (rest : TJudge') (vars : Ctx) : (Lean.MacroM
      (Ctx × (MacroM (Lean.TSyntax `cons)))) := do
      let t_rest ← rest.snd
      match ← vars with
      | `(binderlist| ($thevars:judgment,*)) =>
        -- if a variable isn't in substitution position
        -- we can be fairly sure they will never need an argument.
        match fhead with
        | `(expr| ($_f:app $var:ident) : $β:atom) =>
          match ← thevars.getElems.toList.zipIdx.findM? (find_entry var) with
          | .some (.mk a debruijnIdx) =>
            match a with
            | `(judgment| $_x:atom : $α:atom) =>
              pure <| ⟨vars, mk_debruijn α β t_rest debruijnIdx.succ⟩
            | _ => Macro.throwError "variable missing in context"
          | .none => Macro.throwError "variable missing in context"
        -- this slot does not take the variable as substitution.
        | `(expr| $_f:atom : $β:atom) =>
          pure <| ⟨vars, mk_debruijn β β t_rest 0⟩
        | _ => Macro.throwError "not a valid context"
      | _ => Macro.throwError "not a valid context"
    let acc : Ctx × TJudge' :=
      Prod.mk (`(binderlist| ($vars:judgment,*))) (⟨pure conclude, pure why⟩ : TJudge')
    hyps.getElems.toList.foldrM (fun e (⟨vars, acc_e⟩ : Ctx × TJudge') => do
      let ⟨vars', fc⟩ ← gen_debruijn e acc_e vars
      let fst ← acc_e.fst
      let mycons ← fc
      pure <| Prod.mk vars' ((Prod.mk
        (`(atom| ($mycons:cons {($e:expr), $fst:atom})))
        (`(atom| tail <| $(← acc_e.snd)))) : TJudge'))
      (init := acc)
      >>= (fun (⟨_vars, acc_e⟩ : Ctx × TJudge') =>do
        let fst ← acc_e.fst
        `(at⟪$fst:atom⟫))
  | _ => Macro.throwUnsupported

@[macro mexpr] def parse_expr : Lean.Macro
  | s@`(⟪∀$_vars:binderlist, $_hyps:list⟫) => parse_fall s
  | `(⟪$s:sort⟫) => `(srt⟪$s:sort⟫)
  | `(⟪$a:atom⟫) => `(at⟪$a:atom⟫)
  | `(⟪$c:cons⟫) => `(::⟪$c:cons⟫)
  | `(⟪$a:app⟫) => `(a⟪$a:app⟫)
  | `(⟪$α:atom → ($β:atom : Type $n)⟫) =>
    `(⟪∀(x : $α:atom), [(: $α:atom x) : Prop, $β:atom : Type $n]⟫)
  | `(⟪$α:atom → $β:atom⟫) =>
    `(⟪∀(x : $α:atom), [(: $α:atom x) : Prop, $β:atom : (sortof <| typeof <| $β)]⟫)
  | _ => Macro.throwUnsupported

#eval ⟪mkcons I[0]⟫
#eval ::⟪::(mkcons, I[0], I[0]){Prop, Prop, Type 0}⟫
#eval ⟪I[1] (Type 0) Prop⟫
#eval at⟪sortof<|typeof<|Type 0⟫

#eval ⟪∀(x : Prop, y : Type 1), [(I[1] (Type 0) x) : Type 0, (I[1] (Type 0) x) : Type 0]⟫
