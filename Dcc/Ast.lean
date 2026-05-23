import Dcc.Attrs
import Mathlib.Data.Nat.Notation
import Init.Data.String.Search

-- Infinite sort universe hierarchy
abbrev Level := ℕ

/-
Similar to the categorical combinators and contextual categories.

- Fst corresponds to truncation of contexts.
  Fst(α, β) : ∀ (s : Σ α, β), α

Σ corresponds to substitution:
⟦α, x⟧ : Σ Type, id(Type)
Fst(α, β) : Σ α β → α
Snd(α, β) : Σ (x : α) β → β x

we can derive `()

Λ(Fst(α, β)
-/

namespace GenAst

open Lean Macro Parser.Command
open Lean (Parser.Command.derivingClass)
open Lean.Parser.Term

syntax "gen_ast" gen_flag_set                   : command

def field (s : String) : TSyntax `ident :=
    Lean.mkIdent (Lean.Name.mkSimple s).eraseMacroScopes

def mk_ext (my_name ext : TSyntax `ident) : MacroM (TSyntax ``ctor) := do
    `(ctor| | $(field "ext"):ident : $ext:ident → $my_name)

def Flag.base_ctors (flags : Flag) : Lean.MacroM (Array (TSyntax ``ctor)) := do
  let my_name ← flags.get!' Flag.as?
  return #[
    ← `(ctor| | $(field "refl"):ident   : $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "eq"):ident     : $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "eql"):ident    : $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "fstc"):ident   : $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "sndc"):ident   : $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "sort"):ident   : _root_.Level → $my_name:ident),
    ← `(ctor| | $(field "comp'"):ident  : $my_name:ident → $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "comp"):ident   : $my_name:ident → $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "pair"):ident   : $my_name:ident → $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "sigma"):ident  : $my_name:ident → $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "coup"):ident   : $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "mkc"):ident    : $my_name:ident → $my_name:ident → $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "pi"):ident     : $my_name:ident → $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "curr"):ident   : $my_name:ident → $my_name:ident → $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "quot"):ident   : $my_name:ident → $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "id"):ident     : $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "app"):ident    : $my_name:ident → $my_name:ident → $my_name:ident),
    ← `(ctor| | $(field "top"):ident    : $my_name:ident),
    ← `(ctor| | $(field "tintro"):ident : $my_name:ident),
    ← `(ctor| | $(field "bot"):ident    : $my_name:ident)]

def Flag.ext_ctors (flags : Flag) : Lean.MacroM (Array (TSyntax ``ctor)) := do
  let my_name ← flags.get!' Flag.as?
  flags.with!.mapM (mk_ext my_name)

def mk_my_expr (my_attrs : TSyntax ``attrInstance)
  (flags : Flag) : MacroM (TSyntax `command) := do
  let my_name ← flags.as!'
  let with_derive : Syntax.TSepArray ``derivingClass "," := flags.deriving?.getD #[]

  -- Optional embedded datatype (e.g., Lean.Expr for metatactics)
  let ext ← flags.ext_ctors

  /-
    Core DCC constructors. This is a spec so that meta-layer (tactic) mirror-image can be updated
  -/
  let base ← flags.base_ctors

  let all := base ++ ext

  let cmd := if with_derive.getElems.toList.isEmpty then
    `(command|
      @[$my_attrs]
      inductive $my_name:ident where
      $all:ctor*)
  else
  `(command|
    @[$my_attrs]
    inductive $my_name:ident where
      $all:ctor*
      deriving $with_derive,*)

  cmd

macro_rules
  | `(command| gen_ast $flags:gen_flag_set) => do
    let pflags := parse_flags flags
    let attrs ← pflags.attrs

    mk_my_expr attrs pflags

namespace _test

gen_ast as StrExpr
  with String
  deriving Repr

#check StrExpr.ext
#check Repr StrExpr

end _test

end GenAst

open GenAst in
gen_ast as Expr
  deriving BEq, DecidableEq

#check Expr.sort

declare_syntax_cat gen_dcc

syntax "=(" gen_dcc,* ")"                                     : gen_dcc
syntax "Eql(" gen_dcc,* ")"                                   : gen_dcc
syntax "refl(" gen_dcc,* ")"                                  : gen_dcc
syntax "#(" term ")"                                          : gen_dcc
syntax "⊤"                                                    : gen_dcc
syntax "∗"                                                    : gen_dcc
syntax "⊥"                                                    : gen_dcc
syntax:max "`(" gen_dcc,* ")"                                 : gen_dcc
syntax:max "Id(" gen_dcc,* ")"                                : gen_dcc
syntax:max "Fstc(" gen_dcc,* ")"                              : gen_dcc
syntax:max "Sndc(" gen_dcc,* ")"                              : gen_dcc
syntax "Σ(" gen_dcc,* ")"                                     : gen_dcc
syntax "Coup(" gen_dcc ")"                                    : gen_dcc
syntax:max (priority := high) "Λ(" gen_dcc,* ")"              : gen_dcc
syntax:max (priority := high) "Π(" gen_dcc,* ")"              : gen_dcc
syntax gen_dcc "∘'" gen_dcc                                   : gen_dcc
syntax gen_dcc "∘" gen_dcc                                    : gen_dcc
syntax:30 ident                                               : gen_dcc
syntax "(" gen_dcc+ ")"                                       : gen_dcc
syntax:max "Sort" term                                        : gen_dcc
syntax (priority := high) "⟨" gen_dcc,* "⟩"                   : gen_dcc
syntax (priority := high) "⟦" gen_dcc,* "⟧" "(" gen_dcc,* ")" : gen_dcc

declare_syntax_cat gen_dcc_loc

syntax "."   : gen_dcc_loc
syntax ident : gen_dcc_loc

syntax "DCC" "[" gen_dcc_loc "]"  gen_dcc : term

def field (in_ty : Lean.TSyntax `gen_dcc_loc) (fld : String) : Lean.MacroM (Lean.TSyntax `term) := do
  match in_ty with
  | `(gen_dcc_loc| .) => return Lean.mkIdent (Lean.Name.mkSimple fld).eraseMacroScopes
  | `(gen_dcc_loc| $idt:ident) =>
    let nm := (idt.getId ++ Lean.Name.mkSimple fld).eraseMacroScopes
    return Lean.mkIdent nm
  | s => Lean.Macro.throwErrorAt in_ty s!"this is not a DCC-like: {s}"

open Lean.Syntax in macro_rules
  | `(DCC[$ty:gen_dcc_loc] ⊤)                                        => field ty "top"
  | `(DCC[$ty:gen_dcc_loc] ⊥)                                        => field ty "bot"
  | `(DCC[$ty:gen_dcc_loc] ∗)                                        => field ty "tintro"
  | `(DCC[$ty:gen_dcc_loc] =($f_α:gen_dcc))                          => do
    return mkApp (← field ty "eq") #[← `(DCC[$ty:gen_dcc_loc] $f_α)]
  | `(DCC[$ty:gen_dcc_loc] Eql($f_α:gen_dcc))                        => do
    return mkApp (← field ty "eql") #[← `(DCC[$ty:gen_dcc_loc] $f_α)]
  | `(DCC[$ty:gen_dcc_loc] refl($f_α:gen_dcc))                       => do
    return mkApp (← field ty "refl") #[← `(DCC[$ty:gen_dcc_loc] $f_α)]
  | `(DCC[$ty:gen_dcc_loc] ($f:gen_dcc $x:gen_dcc))                  => do
    return mkApp (← field ty "app") #[← `(DCC[$ty:gen_dcc_loc] $f:gen_dcc), ← `(DCC[$ty:gen_dcc_loc] $x:gen_dcc)]
  | `(DCC[$ty:gen_dcc_loc] ($f:gen_dcc $x:gen_dcc $xs:gen_dcc*))     =>
    `(DCC[$ty:gen_dcc_loc] (($f:gen_dcc $x:gen_dcc) $xs:gen_dcc*))
  | `(DCC[$ty:gen_dcc_loc] `($β:gen_dcc, $x:gen_dcc))                => do
    return mkApp (← field ty "quot") #[← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] Λ($α:gen_dcc, $β:gen_dcc, $e:gen_dcc))    => do
    return mkApp (← field ty "curr") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $e)]
  | `(DCC[$ty:gen_dcc_loc] Π($α:gen_dcc, $β:gen_dcc))                => do
    return mkApp (← field ty "pi") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] ⟨$x:gen_dcc, $y:gen_dcc⟩)                 => do
    return mkApp (← field ty "pair") #[← `(DCC[$ty:gen_dcc_loc] $x), ← `(DCC[$ty:gen_dcc_loc] $y)]
  | `(DCC[$ty:gen_dcc_loc] ⟦$β:gen_dcc⟧($x, $y))                     => do
    return mkApp (← field ty "mkc") #[← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $x), ← `(DCC[$ty:gen_dcc_loc] $y)]
  | `(DCC[$ty:gen_dcc_loc] Sort $m:term)                             => do
    return mkApp (← field ty "sort") #[m]
  | `(DCC[$ty:gen_dcc_loc] Σ($α:gen_dcc, $β:gen_dcc))                => do
    return mkApp (← field ty "sigma") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] Coup($β:gen_dcc))                         => do
    return mkApp (← field ty "coup") #[← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] Fstc($β:gen_dcc))                         => do
    return mkApp (← field ty "fstc") #[← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] Sndc($β:gen_dcc))                         => do
    return mkApp (← field ty "sndc") #[← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] Id($α:gen_dcc))                           => do
    return mkApp (← field ty "id") #[← `(DCC[$ty:gen_dcc_loc] $α)]
  | `(DCC[$ty:gen_dcc_loc] $f:gen_dcc ∘' $g:gen_dcc)                 => do
    return mkApp (← field ty "comp'") #[← `(DCC[$ty:gen_dcc_loc] $f:gen_dcc), ← `(DCC[$ty:gen_dcc_loc] $g:gen_dcc)]
  | `(DCC[$ty:gen_dcc_loc] $f:gen_dcc ∘ $g:gen_dcc)                  => do
    return mkApp (← field ty "comp") #[← `(DCC[$ty:gen_dcc_loc] $f:gen_dcc), ← `(DCC[$ty:gen_dcc_loc] $g:gen_dcc)]
  | `(DCC[$_ty:gen_dcc_loc] #($t:term))                              => `($t)
  | `(DCC[$_ty:gen_dcc_loc] $idt:ident)                              => `($idt:term)
  | `(DCC[$ty:gen_dcc_loc] ($t:gen_dcc))                             => `(DCC[$ty:gen_dcc_loc] $t)

syntax "gen_dsl" str "for" term : command

macro_rules
  | `(gen_dsl $pre:str for $ty:ident) =>
    `(command| macro $pre:str exp:gen_dcc : term => `(DCC[$ty:ident] $$exp))

gen_dsl "DCC" for Expr

#eval (DCC Sort 0)

def runDcc : Lean.TSyntax `gen_dcc → Lean.MacroM Lean.Syntax
  | `(gen_dcc| $e:gen_dcc) => `(DCC $e:gen_dcc)
