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

syntax binderlist atom         : binderlist
syntax atom                    : binderlist

syntax "∀(" judgment,* ")" "," list    : fall

syntax "::(" atom,* ")"                : cons
syntax "{" atom,+ "}"                  : cons
syntax cons cons                       : cons

syntax "[" expr,+ "]"                  : list

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

syntax fall         : expr
syntax app          : expr
syntax judgment     : expr
syntax arrow        : expr
syntax substitution : expr
syntax cons         : expr
syntax:65 operator "<|" expr:65 : atom

syntax "⟪" expr "⟫"         : term
syntax "a⟪" app "⟫"         : term
syntax "at⟪" atom "⟫"       : term
syntax "srt⟪" sort "⟫"      : term
syntax "c⟪" comb "⟫"        : term
syntax "::⟪" cons "⟫"       : term
syntax "j⟪" judgment "⟫"    : term

-- If this variable is contained in vars, then look up the corresponding debruijn index
-- otherwise, insert the variable

-- debruijn index 0 corresponds to rejecting all future inputs
-- for the head
-- 1 corresponds to accepting the input
-- all others decrement from n to 1
-- this assumes that α is well-tyepd as a Type
def mk_debruijn (α β tg : Lean.TSyntax `atom) (n' : ℕ) : Lean.MacroM (Lean.TSyntax `cons) := do
  let m := `(atom| typeof <| $α:atom)
  let n := `(atom| typeof <| $β:atom)
  let o := `(atom| typeof <| $tg:atom)
  let ret_g    ← `(atom| (I[$o:atom] $tg:atom))
  let judge_α  ← `(atom| ($α:atom : Type $m:atom))
  let judge_β  ← `(atom| ($β:atom : Type $n:atom))
  let norm_t_f ← `(atom| ($judge_α:atom → $judge_β:atom))
  match n' with
  | .zero => `(cons| ::(mkcons, (K'[$n:atom, $n:atom] $β:atom $β:atom), (I[$o:atom] $tg:atom)))
  | .succ n' =>
    let inner ← mk_debruijn n m o α β tg n'
    let map_f ← if n' == .succ .zero then
      `(atom| (I[$n:atom] $norm_t_f:atom))
    else
      `(atom| (K'[$n:atom, $m:atom] $norm_t_f:atom))

    `(cons| ::(($inner:cons), $map_f:atom, $ret_g:atom))

macro_rules
  | `(⟪$s:sort⟫) => `(srt⟪$s:sort⟫)
  | `(⟪$op:operator <| $e:expr⟫) => do
    match op, ← `(⟪$e⟫) with
    | `(operator| sortof), `(⟪Prop⟫) => `(0)
    | `(operator| sortof), `(⟪Sort $m⟫) => `(at⟪$m⟫)
    | `(operator| sortof), `(⟪Type $m⟫) => `(at⟪$m⟫ + 1)
    | `(operator| typeof), `(⟪Sort $m⟫) => `(⟪Type $m⟫)
    | `(operator| typeof), `(⟪Type $m⟫) => `(⟪Type #(1 + at⟪$m⟫)⟫)
    | `(operator| typeof), `(⟪Prop⟫) => `(⟪Type 0⟫)
    | `(operator| typeof), `(⟪$x:atom : $t:atom⟫) => `(⟪$t:atom⟫)
    | `(operator| typeof), `(⟪judge <| ($x:atom : $t:atom)⟫) => `(⟪Prop⟫)
    | `(operator| typeof), `(⟪: $T:atom⟫) => `(⟪$T:atom → Prop⟫)
    | `(operator| typeof), `(⟪∀($vars), [$dom:expr, $cod:expr]⟫) => `(⟪typeof <| $cod:expr⟫)
    | `(operator| typeof), `(⟪∀($vars), [$dom:judgment, $cod:expr,*]⟫) =>
      `(⟪tail <| typeof <| ∀($vars), [$cod:expr,*]⟫)
    | `(operator| typeof), `(⟪$α:atom → $β:atom⟫) => `(⟪typeof <| $β:atom⟫)
    | `(operator| typeof), `(⟪($e:expr)⟫) => `(⟪typeof <| $e⟫)
    | `(operator| judge), `(⟪$x:atom : $t:atom⟫) => `(⟪: $t:atom $x:atom⟫)
    | `(operator| head), `(⟪judge <| $x:atom : $t:atom⟫) => pure x
    | `(operator| tail), `(⟪judge <| $x:atom : $t:atom⟫) => pure t
    | `(operator| head), `(⟪$x:atom : $t:atom⟫) => pure x
    | `(operator| tail), `(⟪$x:atom : $t:atom⟫) => pure t
    | `(operator| head), `(::⟪$a:cons {$a:atom, $xs:atom,*}⟫) => pure a
    | `(operator| tail), `(::⟪$a:cons {$a:atom, $xs:atom,*}⟫) => `(::⟪$a:cons {$xs:atom,*}⟫)
    | _, _ => `(sorry)
  /-| `(::⟪::(($α:atom : Type $m), ($β:atom : ($α:atom : Type $m) → (Type $n : Type #($n + 1))), ($γ:atom : ($α:atom : Type $m) → (Type $o : Type #($o + 1))), ($δ:atom : Type $p), $rst:atom,*)⟫) => do
    let inner ← `(app| (mkcons $m:atom $n:atom $o:atom $p:atom) $α:atom $β:atom $γ:atom $δ:atom)
    let args ← rst.getElems.toList.foldlM (fun acc e => `(app| $acc:app $e:atom)) inner
    `(a⟪$args⟫)-/
  | `(::⟪$a:cons {$f:atom,$g:atom,$xs:atom,*}⟫) => `(a⟪($a:cons) $f:atom ($a:cons {$g:atom, $xs:atom,*})⟫)
  | `(::⟪$a:cons {$f:atom,$g:atom}⟫) => `(a⟪($a:cons) $f:atom $g:atom⟫)
  -- This is the base case of debruijn-index substitution in lists
  | `(⟪∀($vars:judgment,*), [$hyps,*, $conclude:judgment]⟫) => do
    -- Finds the entry of an indexed variable judgment
    -- corresponding to a hypothesis binder
    let find_entry (var : Lean.TSyntax `atom) : _ → Lean.MacroM Bool :=
          fun (⟨judgmt, idx⟩ : (Lean.TSyntax `judgment) × ℕ) => match judgmt with
          | `(judgment| $v:atom : $α:atom) => do
            pure <| (← `(at⟪$v⟫)) == (← `(at⟪$var⟫))
          | _ => pure false
    
    let swap_head (f : Lean.TSyntax `expr) : (Lean.MacroM (Lean.TSyntax `expr)) := do
      let t_f ← `(⟪typeof <| $f⟫)
      let t_t_f ← `(⟪typeof <| typeof <| $f⟫)
      match f, t_f, t_t_f with
      | `(⟪$f:app $var:atom⟫), t_f, `(⟪ Type $m:atom ⟫) =>
        match ← vars.getElems.toList.zipIdx.findM? (find_entry var) with
        | .some debruijnIdx =>
          let inner ← mk_debruijn 
          sorry
        | .none =>
          -- this is the first time seeing this variable.
          we should add it to the context.
          sorry
      | _, _, _ => `(⟪__⟫)
    sorry
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
  | `(at⟪judge <| $x:atom : $t:atom⟫) => `(⟪(: $t:atom) $x:atom⟫)
  | `(⟪$c:cons⟫) => `(::⟪$c:cons⟫)
  | `(at⟪($a:atom)⟫) => `(at⟪$a:atom⟫)
  | `(at⟪($a:expr)⟫) => `(⟪$a:expr⟫)
  | `(at⟪$n:num⟫) => `($n)
  | `(at⟪$ide:ident⟫) => `($ide)
  | `(at⟪#($t:term)⟫) => `($t)
  | `(srt⟪Type $n:atom⟫) => `(Expr.type at⟪$n⟫)
  | `(srt⟪Sort $n:atom⟫) => `(Expr.sort at⟪$n⟫)
  | `(srt⟪Prop⟫) => `(Expr.prop)
  | `(at⟪: $T:atom⟫) => `(Expr.judge at⟪$T⟫)
  | `(c⟪$comb:ident[]⟫) => `(at⟪$comb:ident⟫)
  | `(c⟪($comb:term)[]⟫) => `($comb)
  | `(c⟪$comb:ident[$u:atom, $xs:atom,*]⟫) =>`(c⟪($comb at⟪$u⟫)[$xs,*]⟫)
  | `(c⟪($comb:term)[$u:atom, $xs:atom,*]⟫) =>`(c⟪($comb at⟪$u⟫)[$xs,*]⟫)
