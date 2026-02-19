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
  | fst    : Expr
  | snd    : Expr
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
declare_syntax_cat substitution
declare_syntax_cat arrow
declare_syntax_cat cons
declare_syntax_cat list
declare_syntax_cat fall
declare_syntax_cat binderlist

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

syntax "[" atom,+ "]"                  : list

syntax "(" judgment,+ ")"              : binderlist
syntax "∀" binderlist "," list        : fall

syntax "::(" atom,* ")"                : cons
syntax "{" atom,+ "}"                  : cons
syntax cons cons                       : cons

-- ^ assumed debruijn, unless a human variable
-- is encountered
-- For keeping track of human variables

syntax ident "[" atom,* "]"        : comb
syntax "(" term ")" "[" atom,* "]" : comb

syntax comb                    : atom
syntax sort                    : atom
syntax "*"                     : atom
syntax "(" expr ")"            : atom
syntax "__"                    : atom
syntax ":" atom                : atom

syntax:50 (name := judge_all) atom ":" expr : judgment

-- assignments are always well-typed judgment
-- with an assigned value.
-- these are not core to the language,
-- but rather derived from operational semantics of cons.
syntax judgment ":=" atom  : declare
syntax atom ":=" atom      : declare

syntax "⟦" judgment "⟧" : assign

syntax atom "→" atom           : arrow

syntax "(" atom assign ")" : substitution
syntax judgment            : substitution

syntax app atom : app
syntax atom     : app

syntax fall         : atom
syntax app          : expr
syntax judgment     : expr
syntax arrow        : expr
syntax substitution : expr
syntax cons         : expr
syntax:65 operator "<|" atom:65 : atom

syntax (name := mexpr) "⟪" expr "⟫"         : term
syntax (name := mapp) "a⟪" app "⟫"         : term
syntax (name := matom) "at⟪" atom "⟫" : term
syntax (name := msort) "srt⟪" sort "⟫"      : term
syntax (name := mcomb) "c⟪" comb "⟫"        : term
syntax (name := mcons) "::⟪" cons "⟫"       : term


-- If this variable is contained in vars, then look up the corresponding debruijn index
-- otherwise, insert the variable

-- debruijn index 0 corresponds to rejecting all future inputs
-- for the head
-- 1 corresponds to accepting the input
-- all others decrement from n to 1
-- this assumes that α is well-tyepd as a Type
def mk_debruijn (α β tg : Lean.TSyntax `atom) (n' : ℕ) : Lean.MacroM (Lean.TSyntax `cons) := do
  let m ← `(atom| sortof <| typeof <| $α:atom)
  let n ← `(atom| sortof <| typeof <| $β:atom)
  let o ← `(atom| sortof <| typeof <| $tg:atom)
  let ret_g    ← `(atom| (I[$o:atom] $tg:atom))
  let judge_α  ← `(atom| ($α:atom : Type $m:atom))
  let judge_β  ← `(atom| ($β:atom : Type $n:atom))
  let norm_t_f ← `(atom| ($judge_α:atom → $judge_β:atom))
  match n' with
  | .zero => `(cons| ::(mkcons, (K'[$n:atom, $n:atom] $β:atom $β:atom), (I[$o:atom] $tg:atom)))
  | .succ n' =>
    let inner ← mk_debruijn α β tg n'
    let map_f ← if n' == .succ .zero then
      `(atom| (I[$n:atom] $norm_t_f:atom))
    else
      `(atom| (K'[$n:atom, $m:atom] $norm_t_f:atom))

    `(cons| ::(($inner:cons), $map_f:atom, $ret_g:atom))

def parse_typeof : Lean.Macro
  | `(⟪ typeof <| Sort $m:atom ⟫) => `(⟪Type $m:atom⟫)
  | `(⟪ typeof <| Type $m:atom ⟫) => `(⟪Type #(1 + at⟪$m:atom⟫)⟫)
  | `(⟪ typeof <| Prop ⟫)    => `(⟪Type 0⟫)
  | `(⟪ typeof <| $_x:atom : $t:atom ⟫) => `(⟪$t:atom⟫)
  | `(⟪ typeof <| judge <| $_x:atom : $_t:atom ⟫) => `(⟪Prop⟫)
  | `(⟪ typeof <| : $T:atom⟫) => `(⟪$T:atom → Prop⟫)
  | `(at⟪ typeof <| ∀$_vars:binderlist, [$_dom:atom, $cod:atom] ⟫) => `(at⟪typeof <| $cod:atom⟫)
  | `(at⟪ typeof <| ∀$vars:binderlist, [$_dom:atom, $cod:atom,*] ⟫) =>
    `(at⟪tail <| typeof <| ∀$vars:binderlist, [$cod:atom,*]⟫)
  | `(⟪ typeof <| $_α:atom → $β:atom⟫) => `(⟪typeof <| $β:atom⟫)
  | _ => Macro.throwUnsupported

def parse_sortof : Lean.Macro
  | `(⟪ sortof <| Prop ⟫) => `(0)
  | `(⟪ sortof <| Sort $m ⟫) => `(at⟪$m⟫)
  | `(⟪ sortof <| Type $m ⟫) => `(at⟪$m⟫ + 1)
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
  | s@`(at⟪ sortof <| $_e:atom⟫) => parse_sortof s
  | s@`(at⟪ asvar  <| $_e:atom⟫) => parse_asvar s
  | `(at⟪ head <| ($x:atom : $_t:atom)⟫) => pure x
  | `(at⟪ tail <| ($_x:atom : $t:atom)⟫) => pure t
  | `(at⟪ head <| ($_a:cons {$a:atom, $_xs:atom,*})⟫) => pure a
  | `(at⟪ tail <| ($a:cons {$_a:atom, $xs:atom,*})⟫) => `(::⟪$a:cons {$xs:atom,*}⟫)
  | _ => Macro.throwUnsupported

@[macro msort] def parse_sort : Lean.Macro
  | `(srt⟪Type $n:atom⟫) => `(Expr.type at⟪$n⟫)
  | `(srt⟪Sort $n:atom⟫) => `(Expr.sort at⟪$n⟫)
  | `(srt⟪Prop⟫) => `(Expr.prop)
  | _ => Macro.throwUnsupported

@[macro mcomb] def parse_comb : Lean.Macro
  | `(c⟪$comb:ident[]⟫) => `(at⟪$comb:ident⟫)
  | `(c⟪($comb:term)[]⟫) => `($comb)
  | `(c⟪$comb:ident[$u:atom, $xs:atom,*]⟫) =>`(c⟪($comb at⟪$u⟫)[$xs,*]⟫)
  | `(c⟪($comb:term)[$u:atom, $xs:atom,*]⟫) =>`(c⟪($comb at⟪$u⟫)[$xs,*]⟫)
  | _ => Macro.throwUnsupported

def parse_fall : Lean.Macro
  | `(at⟪∀($vars:judgment,*), [$hyps:atom,*, ($conclude:atom : $why:atom)]⟫) => do
    -- Finds the entry of an indexed variable judgment
    -- corresponding to a hypothesis binder
    let TJudge' := Prod (Lean.MacroM (Lean.TSyntax `atom)) (Lean.MacroM (Lean.TSyntax `atom))
    let find_entry (var : Lean.TSyntax `term) : Lean.TSyntax `judgment × ℕ → Lean.MacroM Bool :=
          fun (⟨judgmt, _idx⟩ : Lean.TSyntax `judgment × ℕ) => match judgmt with
          | `(judgment| $v:atom : $_α:atom) => do
            pure <| (← `(at⟪$v⟫)) == var
          | _ => pure false
    let Ctx := Lean.MacroM (Lean.TSyntax `binderlist)
    -- generates ::(a, b, c) head without f and g inserted.
    let gen_debruijn (fhead : Lean.TSyntax `atom) (rest : TJudge') (vars : Ctx) : (Lean.MacroM
      (Ctx × (MacroM (Lean.TSyntax `cons)))) := do
      let t_rest ← rest.snd
      match ← vars with
      | `(binderlist| ($thevars,*)) =>
        match fhead with
        | `(⟪($_f:app $var:atom) : $β:atom⟫) =>
          match ← thevars.getElems.toList.zipIdx.findM? (find_entry (← `(⟪asvar <| $var:atom⟫))) with
          | .some (.mk a debruijnIdx) =>
            match var, a with
            | _, `(judgment| $_x:atom : $α:atom) =>
              pure <| ⟨vars, mk_debruijn α β t_rest debruijnIdx.succ⟩
            | `(judgment| $x:atom : $α:atom), _ =>
              pure <| ⟨vars, mk_debruijn α β t_rest debruijnIdx.succ⟩
            | _, _ => Macro.throwError "variable's type is undefined"
          | .none =>
            match var with
            | `(judgment| $x:atom : $α:atom) =>
              -- this is the first time seeing this variable.
              -- we should add it to the context and also
              -- substitute the bound variable
              let inner := ← mk_debruijn α β t_rest 1
              let vars' := `(binderlist| ($thevars:judgment,*, $x:atom : $α:atom))
              pure <| ⟨vars', pure inner⟩
            | _ => Macro.throwError "variable's type is undefined"
        | _ => Macro.throwError "this is not a valid list"
      | _ => Macro.throwError "not a valid context"
    let acc : Ctx × TJudge' :=
      Prod.mk (`(binderlist| ($vars:judgment,*))) (⟨pure conclude, pure why⟩ : TJudge')
    hyps.getElems.toList.foldrM (fun e (⟨vars, acc_e⟩ : Ctx × TJudge') => do
      let ⟨vars', fc⟩ ← gen_debruijn e acc_e vars
      let fst ← acc_e.fst
      let mycons ← fc
      pure <| Prod.mk vars' ((Prod.mk
        (`(atom| ($mycons:cons {$e:atom, $fst:atom})))
        (`(atom| tail <| $(← acc_e.snd)))) : TJudge'))
      (init := acc)
      >>= (fun (⟨_vars, acc_e⟩ : Ctx × TJudge') =>do
        let fst ← acc_e.fst
        `(at⟪$fst:atom⟫))
  | _ => Macro.throwUnsupported

@[macro matom] def parse_atom : Lean.Macro
  | `(at⟪($a:atom)⟫) => `(at⟪$a:atom⟫)
  | `(at⟪($a:expr)⟫) => `(⟪$a:expr⟫)
  | `(at⟪$n:num⟫) => `($n)
  | `(at⟪$ide:ident⟫) => `($ide)
  | `(at⟪#($t:term)⟫) => `($t)
  | `(at⟪: $T:atom⟫) => `(Expr.judge at⟪$T⟫)
  | s@`(at⟪∀$_vars:binderlist, $_hyps:list⟫) => parse_fall s
  | s@`(at⟪$_op:operator <| $_a:atom⟫) => parse_aoperator s
  | _ => Macro.throwUnsupported

@[macro mapp] def parse_app : Lean.Macro
  | `(::⟪$a:cons {$f:atom,$g:atom,$xs:atom,*}⟫) => `(a⟪($a:cons) $f:atom ($a:cons {$g:atom, $xs:atom,*})⟫)
  | `(::⟪$a:cons {$f:atom,$g:atom}⟫) => `(a⟪($a:cons) $f:atom $g:atom⟫)
  | _ => Macro.throwUnsupported

@[macro mexpr] def parse_expr : Lean.Macro
  | `(⟪$s:sort⟫) => `(srt⟪$s:sort⟫)
  | `(⟪$a:atom⟫) => `(at⟪$a:atom⟫)
  | `(⟪$c:cons⟫) => `(::⟪$c:cons⟫)
  | _ => Macro.throwUnsupported

@[macro mcons] def parse_cons : Lean.Macro
  | `(::⟪::($πcons:atom, $πf:atom, $πg:atom)⟫) => `(⟪mkcons $πcons $πf $πg⟫)
  | _ => Macro.throwUnsupported

/-
macro_rules
  | `(::⟪::(($α:atom : Type $m), ($β:atom : ($α:atom : Type $m) → (Type $n : Type #($n + 1))), ($γ:atom : ($α:atom : Type $m) → (Type $o : Type #($o + 1))), ($δ:atom : Type $p), $rst:atom,*)⟫) => do
    let inner ← `(app| (mkcons $m:atom $n:atom $o:atom $p:atom) $α:atom $β:atom $γ:atom $δ:atom)
    let args ← rst.getElems.toList.foldlM (fun acc e => `(app| $acc:app $e:atom)) inner
    `(a⟪$args⟫)-/
  -- This is the base case of debruijn-index substitution in lists
  
  -- base case. this is technically the head element.
  -- here, we produce a judged list
  -- the type is exactly the type of concl
  /-| `(⟪∀{$vars} $last:substitution, $concl:atom : $α:atom⟫) =>
    
  | `(⟪∀{$vars} $prev:binderlist $last:substitution, $concl:atom⟫) => 
  -- base case for debruijn indices. this produces a judged cons list.
  | `(::⟪::={$vars:ident,*}[($f:atom ⟦$var:ident : ($α:atom : Type $m:atom)⟧) : ($β:atom : Type $n:atom)
    , $g:atom : ($tg:atom : Type $o:atom)]⟫) => do
    match vars.getElems.toList.findIdx? (· == var) with
    | .some debruijnIdx =>
      let inner ← mk_debruijn n m o α β tg debruijnIdx
      `(⟪judge(($inner:cons {$f:atom,$g:atom}) : )⟫)
    | .none =>
      -- Not contained in vars, so this is de bruijn index 0
      let inner ← mk_debruijn n m o α β tg 0
      
      sorry-/
