import Mathlib.Data.Nat.Notation
import Init.Meta.Defs

open Std Format
open Lean (Macro)
open Lean (MacroM)
open Lean (Syntax)

abbrev Level := ℕ

/-
I'm fairly certain you can derive fst and snd from the new generalized cons.
-/

inductive Expr where
  | I       : Level → Expr
  | K       : Level → Level → Expr -- Dependent K
  | K'      : Level → Level → Expr -- Nondependent K
  | S       : Level → Level → Level → Expr -- Dependent S
  | mkcons  : Expr
  -- ^ (mkcons πcons πf πg f g x) = (πcons πf πg (πf f x) (πg g x))
  | judge  : Level  → Expr -- judge t is a freestanding expr
  /-
    Sorts:
  -/
  | type   : Level → Expr
  | prop   : Expr
  | sort   : Level → Expr
  | fst    : Level → Expr
  | snd    : Level → Expr
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

syntax ident ".[" term,+ "]"          : atom
syntax "[" atom,+ "]"                 : list

syntax ident ":" atom                 : binder
syntax "(" binder,* ")"               : binderlist
syntax "∀" binderlist "," list        : fall


-- ^ assumed debruijn, unless a human variable
-- is encountered
-- For keeping track of human variables

syntax atom "{" atom,* "}"     : atom
syntax "::(" atom,* ")"        : atom
syntax "⟨" atom,+ "⟩"          : atom
syntax sort                    : atom
syntax  "(" expr ")"           : atom
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
  | `(⟪ typeof <| (: m) $T:atom⟫) => `(⟪$T:atom → Prop⟫)
  | `(at⟪ typeof <| (∀$_vars:binderlist, [$_dom:atom, $cod:atom]) ⟫) =>
    `(at⟪typeof <| $cod:atom⟫)
  | `(at⟪ typeof <| (∀$vars:binderlist, [$_dom:atom, $cod:atom,*]) ⟫) =>
    `(at⟪tail <| typeof <| (∀$vars:binderlist, [$cod:atom,*])⟫)
  | _ => Macro.throwUnsupported

def parse_asvar : Lean.Macro
  | `(⟪ asvar <| $x:atom $_t:atom ⟫) => pure x
  | `(⟪ asvar <| $x⟫) => pure x
  | _ => Macro.throwUnsupported

def parse_aoperator : Lean.Macro
  | `(at⟪ head <| judge <| ($x:atom : $_t:atom)⟫) => pure x
  | `(at⟪ tail <| judge <| ($_x:atom : $t:atom)⟫) => pure t
  | `(at⟪judge <| ($x:atom : ($t:atom : Type $m))⟫) =>
    `(at⟪(((: $m) $t:atom) $x:atom)⟫)
  | `(at⟪judge <| ($x:atom : $t:atom)⟫) =>
    `(at⟪(((: sortof <| $t:atom) $t:atom) $x:atom)⟫)
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
  | `(at⟪⟨($a:atom : ($α:atom : Type $m:atom))
    , ($b:atom : ($β:atom : Type $n:atom))⟩⟫) =>
    `(a⟪mkcons (I.[at⟪$m:atom⟫] (($α:atom : Type $m) → $α:atom))
      (I.[at⟪$m:atom⟫] $α:atom)
      (I.[at⟪$n:atom⟫] $β:atom) $a:atom $b:atom⟫)
  | `(at⟪$a:atom {$f:atom, $g:atom, $elems:atom,*}⟫) =>
    `(a⟪$a:atom $f:atom $g:atom ($a:atom {$elems:atom,*})⟫)
  | `(at⟪$a:atom {$f:atom, $g:atom}⟫) => `(a⟪$a:atom $f:atom $g:atom⟫)
  | `(at⟪($e:app)⟫) => `(a⟪$e:app⟫)
  | `(at⟪($e:expr)⟫) => `(⟪$e:expr⟫)
  | `(at⟪mkcons⟫) => `(Expr.mkcons)
  | `(at⟪::($πcons:atom, $πf:atom, $πg:atom)⟫) => `(a⟪mkcons $πcons:atom $πf:atom $πg:atom⟫)
  | `(at⟪$s:sort⟫) => `(srt⟪$s:sort⟫)
  | `(at⟪$n:num⟫) => `($n)
  | `(at⟪#($t:term)⟫) => `($t)
  | `(at⟪: $m:atom⟫) => `(Expr.judge a⟪$m:atom⟫)
  | `(at⟪fst.[$u:term]⟫) => `(Expr.fst $u)
  | `(at⟪snd.[$u:term]⟫) => `(Expr.snd $u)
  | `(at⟪I.[$uvs:term,*]⟫) => `(Expr.I $uvs*)
  | `(at⟪S.[$uvs:term,*]⟫) => `(Expr.S $uvs*)
  | `(at⟪K.[$uvs:term,*]⟫) => `(Expr.K $uvs*)
  | `(at⟪K'.[$uvs:term,*]⟫) => `(Expr.K' $uvs*)
  | s@`(at⟪$_op:operator <| $_a:atom⟫) => parse_aoperator s
  | `(at⟪$id:ident⟫) => `($id)
  | _ => Macro.throwUnsupported

@[macro mapp] def parse_app : Lean.Macro
  | `(a⟪$a:app $b:atom⟫) => `(Expr.app a⟪$a:app⟫ at⟪$b:atom⟫)
  | `(a⟪$a:atom⟫) => `(at⟪$a:atom⟫)
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
      `(app| I.[0] Prop) -- only once we've hit debruijn index one we accept the argument
    else
      `(app| K'.[0, 0] Prop Prop)

  let advance (inner : Lean.TSyntax `atom) : Lean.MacroM (Lean.TSyntax `atom) := do
    let map_f ← mk_fetch n₁
    let map_g ← (mk_fetch <$> n₂).getD `(app| I.[0] Prop)
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
      | .some .zero => do `(atom| ::(mkcons, (K'.[0, 0] Prop Prop), (K'.[0, 0] Prop Prop)))
      | .none => `(atom| ::(mkcons, (K'.[0, 0] Prop Prop), (I.[0] Prop)))

/-
Use this to figure out which variables an element in the list is using.
-/
def allOuterIdents (base_vars : List (Lean.TSyntax `ident)) (e : Lean.TSyntax `app) : List (Lean.TSyntax `ident) :=
  match base_vars with
  | .nil => .nil
  | (.cons x' xs) =>
    match e with
    | `(app| $f:app $x:ident) =>
      if x' == x then (x :: allOuterIdents xs f) else []
    | `(app| $f:atom $x:ident) => if x' == x then [x] else []
    | _ => []

def parse_fall (f : Syntax) : MacroM Syntax :=
  -- Finds the entry of an indexed variable judgment
  -- corresponding to a hypothesis binder
  let find_entry (vars : Syntax.TSepArray `binder ",")
    (var : Lean.TSyntax `ident) : Option (Lean.TSyntax `binder × ℕ) :=
      vars.getElems.zipIdx.find? (fun ⟨a, idx⟩ =>
        match a with
          | `(binder| $var':ident : $t:atom) => if var' == var then
            True
          else False
          | _ => False)
  let best_var_for (vars : Syntax.TSepArray `binder ",") (elem : Lean.TSyntax `atom) : Option (Lean.TSyntax `binder × ℕ):=
      match elem with
      | `(atom| $var:ident)
      | `(atom| ($f:app $var:ident)) => find_entry vars var
      | _ => .none
  let best_body (vars : Syntax.TSepArray `binder ",") (elem  : Lean.TSyntax `atom) : OptionT MacroM (Lean.TSyntax `app) := do
    match elem with
      | elem@`(atom| $var:ident) =>
        let vs ← (OptionT.mk <| pure (best_var_for vars elem))
        match vs.fst with
        | `(binder | $var:ident : ($t:atom : Type $m))=>
          pure <| `(⟪I.[a⟪$m:atom⟫] $t:atom⟫)
        | `(binder | $var:ident : $t:atom) =>
          let srt ← `(at⟪sortof <| typeof <| $t:atom⟫)
          pure <| `(⟪I.[$srt] $t:atom⟫)
        | _ => pure `(⟪I.[0] Prop⟫)
      | `(atom| ($f:app $var:ident)) => pure f
      | `(atom| $f:atom) => pure `(app| $f:atom)

  -- when there is only one head hypothesis, the conclusion
  -- may want a say in subbstitution
  match f with
  | `(⟪∀($vars:binder,*), [$hyp:atom, $conclude:atom]⟫) => do
    let best_idx := Prod.snd ∘ best_var_for
    best_idx hyp
      >>= (mk_debruijn · (best_idx conclude))
      >>= (fun e => do
        let hypb ← best_body vars hyp
        let hypc ← best_body vars conclude
        `(a⟪$e:atom $(best_body vars hyp) $(best_body vars conclude)⟫))
  | `(⟪∀($vars:binder,*), [$hyps:atom,*, $conclude:atom]⟫) => do
    -- Finds the entry of an indexed variable judgment
    -- corresponding to a hypothesis binder
    let find_entry (var : Lean.TSyntax `ident) : Option (Lean.TSyntax `binder × ℕ) :=
      vars.getElems.zipIdx.firstM (fun ⟨a, idx⟩ =>
        match a with
          | `(binder| $var':ident : $t:atom) => if var' == var then
            pure ⟨a, idx⟩
          else .none
          | _ => .none)

    let best_var_for (elem : Lean.TSyntax `atom) : (Option (Lean.TSyntax `binder × ℕ)):=
      match elem with
      | `(atom| $var:ident)
      | `(atom| ($f:app $var:ident)) => find_entry var
      | _ => .none

    -- generates ::(a, b, c) head without f and g inserted.
    let gen_debruijn (fhead : Lean.TSyntax `atom) : MacroM (Lean.TSyntax `app) := do
      -- if a variable isn't in substitution position
      -- we can be fairly sure they will never need an argument.
      match fhead with
      | `(atom| $var:ident) =>
        match find_entry var with
        | .some (.mk binder debruijnIdx) =>
          match binder with
          | `(binder| $_v:ident : ($α:atom : Type $m)) =>
            let inner ← mk_debruijn debruijnIdx .none
            `(app| $inner:atom (I.[a⟪$m:atom⟫] $α:atom))
          | `(binder| $_v:ident : $α:atom) =>
            let inner ← mk_debruijn debruijnIdx .none
            let srt   ← `(at⟪sortof <| $α:atom⟫)
            `(app| $inner:atom (I.[$srt] $α:atom))
          | _ => Macro.throwError "variable missing in context"
        | .none => Macro.throwError "variable missing in context"
      | `(atom| ($f:app $var:ident)) =>
        match find_entry var with
        | .some (.mk _a debruijnIdx) =>
          let inner ← mk_debruijn debruijnIdx.succ .none
          `(app| $inner:atom ($f:app))
        | .none => Macro.throwError "variable missing in context"
      -- this slot does not take the variable as substitution.
      | f =>
        let inner ← mk_debruijn 0 .none
        `(app| $inner:atom $f:atom)
    hyps.getElems.toList.foldrM (fun e fst => do
      `(a⟪$(← gen_debruijn e) $(⟨fst⟩):atom⟫))
      (init := conclude)
  | _ => Macro.throwUnsupported

@[macro mexpr] def parse_expr : Lean.Macro
  | s@`(⟪∀$_vars:binderlist, $_hyps:list⟫) => parse_fall s
  | `(⟪$a:app $b:atom⟫) => `(Expr.app a⟪$a:app⟫ at⟪$b:atom⟫)
  | `(⟪$s:sort⟫) => `(srt⟪$s:sort⟫)
  | `(⟪$a:atom⟫) => `(at⟪$a:atom⟫)
  | `(⟪($α:atom : Type $m) → $β:atom⟫) => do
    let myId ← Lean.withFreshMacroScope (pure <| Lean.mkIdent `my_x)
    `(⟪∀($myId:ident : $α:atom), [((: $m) $α:atom $myId:ident), $β:atom]⟫)
  | `(⟪$α:atom → $β:atom⟫) => do
    let myId ← Lean.withFreshMacroScope (pure <| Lean.mkIdent `my_x)

    `(⟪∀($myId:ident : $α:atom), [((: sortof <| $α:atom) $α:atom $myId:ident), $β:atom]⟫)
  | _ => Macro.throwUnsupported

