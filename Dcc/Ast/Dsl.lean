import Dcc.Ast.Core

abbrev Expr := GenericExpr Unit

namespace Dsl

declare_syntax_cat gen_dcc

scoped syntax "(Dom" gen_dcc ")"                              : gen_dcc
syntax "(!<>" gen_dcc ")"                                     : gen_dcc
syntax "($<>" gen_dcc ")"                                     : gen_dcc
syntax "(*" gen_dcc ")"                                       : gen_dcc
scoped syntax "(!" gen_dcc ")"                                : gen_dcc
syntax "(&" gen_dcc ")"                                       : gen_dcc
syntax  gen_dcc "=" gen_dcc                                   : gen_dcc
syntax "(Eval" gen_dcc+ ")"                                   : gen_dcc
syntax "(Eql" gen_dcc+ ")"                                    : gen_dcc
syntax "(refl" gen_dcc+ ")"                                   : gen_dcc
syntax "#(" term ")"                                          : gen_dcc
syntax "⊤"                                                    : gen_dcc
syntax "∗"                                                    : gen_dcc
syntax "⊥"                                                    : gen_dcc
scoped syntax:max "(`" gen_dcc+ ")"                           : gen_dcc
syntax:max "(Id" gen_dcc+ ")"                                 : gen_dcc
syntax:max "(Fst" gen_dcc+ ")"                                : gen_dcc
syntax:max "(Swap" gen_dcc+ ")"                               : gen_dcc
syntax:max "(Snd" gen_dcc+ ")"                                : gen_dcc
scoped syntax "(Σ" gen_dcc ")"                                : gen_dcc
scoped syntax "(Σ" gen_dcc gen_dcc ")"                        : gen_dcc
syntax "(Uncoup" gen_dcc ")"                                  : gen_dcc
syntax "(Unbang" gen_dcc ")"                                  : gen_dcc
syntax "const(" term ")"                                      : gen_dcc
syntax:max (priority := high) "(Λ" gen_dcc+ ")"               : gen_dcc
syntax:max (priority := high) "(!Λ" gen_dcc+ ")"              : gen_dcc
scoped syntax:max (priority := high) "(Π" gen_dcc+ ")"        : gen_dcc
syntax "(∘" gen_dcc gen_dcc ")"                               : gen_dcc
syntax:30 ident                                               : gen_dcc
syntax "(" gen_dcc+ ")"                                       : gen_dcc
syntax:max "Sort" term                                        : gen_dcc
syntax (priority := high) "(⟨,⟩" (noWs gen_dcc) gen_dcc* ")"  : gen_dcc
syntax (priority := high) "(," (noWs gen_dcc) gen_dcc* ")"    : gen_dcc

declare_syntax_cat gen_dcc_loc

syntax "?"   : gen_dcc_loc
syntax "."   : gen_dcc_loc
syntax term  : gen_dcc_loc

end Dsl

open Dsl in
syntax "DCC" "[" gen_dcc_loc "]"  gen_dcc : term

open Dsl in
def field (in_ty : Lean.TSyntax `gen_dcc_loc) (fld : String) : Lean.MacroM (Lean.TSyntax `term) := do
  match in_ty with
  | `(gen_dcc_loc| ?) => return Lean.mkIdent (Lean.Name.str ``GenericExpr fld).eraseMacroScopes
  | `(gen_dcc_loc| .) => return Lean.mkIdent (Lean.Name.mkSimple fld).eraseMacroScopes
  /-| `(gen_dcc_loc| $idt:ident) =>
    let nm := (idt.getId ++ Lean.Name.mkSimple fld).eraseMacroScopes
    return Lean.mkIdent nm-/
  | `(gen_dcc_loc| $tm:term) =>
    let idt := Lean.mkIdent (Lean.Name.str ``GenericExpr fld).eraseMacroScopes
    `(term| $idt (τ := $tm))
  | s => Lean.Macro.throwErrorAt in_ty s!"this is not a DCC-like: {s}"

open Dsl in
open Lean.Syntax in macro_rules
  | `(DCC[$ty:gen_dcc_loc] (Eval $α:gen_dcc $β:gen_dcc $x:gen_dcc)) => return mkApp (← field ty "eval") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] const($tm:term))                          =>
    return mkApp (← field ty "const") #[← `($tm:term)]
  | `(DCC[$ty:gen_dcc_loc] ⊤)                                        => field ty "top"
  | `(DCC[$ty:gen_dcc_loc] ⊥)                                        => field ty "bot"
  | `(DCC[$ty:gen_dcc_loc] ∗)                                        => field ty "tintro"
  | `(DCC[$ty:gen_dcc_loc] $x:gen_dcc = $y:gen_dcc)                  => do
    return mkApp (← field ty "eq") #[← `(DCC[$ty:gen_dcc_loc] $x), ← `(DCC[$ty:gen_dcc_loc] $y)]
  | `(DCC[$ty:gen_dcc_loc] (!$x:gen_dcc))                  => do
    return mkApp (← field ty "bang") #[← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] (&$x:gen_dcc))                  => do
    return mkApp (← field ty "box") #[← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] (*$α:gen_dcc))                  => do
    return mkApp (← field ty "unbox") #[← `(DCC[$ty:gen_dcc_loc] $α)]
  | `(DCC[$ty:gen_dcc_loc] (Eql$f_α:gen_dcc))                        => do
    return mkApp (← field ty "eql") #[← `(DCC[$ty:gen_dcc_loc] $f_α)]
  | `(DCC[$ty:gen_dcc_loc] (refl$f_α:gen_dcc))                       => do
    return mkApp (← field ty "refl") #[← `(DCC[$ty:gen_dcc_loc] $f_α)]
  | `(DCC[$ty:gen_dcc_loc] ($f:gen_dcc $x:gen_dcc))                  => do
    return mkApp (← field ty "app") #[← `(DCC[$ty:gen_dcc_loc] $f:gen_dcc), ← `(DCC[$ty:gen_dcc_loc] $x:gen_dcc)]
  | `(DCC[$ty:gen_dcc_loc] ($f:gen_dcc $x:gen_dcc $xs:gen_dcc*))     =>
    `(DCC[$ty:gen_dcc_loc] (($f:gen_dcc $x:gen_dcc) $xs:gen_dcc*))
  | `(DCC[$ty:gen_dcc_loc] (`$β:gen_dcc $x:gen_dcc))                => do
    return mkApp (← field ty "quot") #[← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] (Λ$α:gen_dcc $β:gen_dcc $e:gen_dcc))    => do
    return mkApp (← field ty "curr") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $e)]
  | `(DCC[$ty:gen_dcc_loc] (!<> $x:gen_dcc))    => do
    return mkApp (← field ty "map") #[← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] ($<> $x:gen_dcc))    => do
    return mkApp (← field ty "fmap") #[← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] (!Λ $α:gen_dcc $β:gen_dcc $e:gen_dcc))    => do
    return mkApp (← field ty "curr'") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $e)]
  | `(DCC[$ty:gen_dcc_loc] (Π$α:gen_dcc $β:gen_dcc))                => do
    return mkApp (← field ty "pi") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] (⟨,⟩$β:gen_dcc $x:gen_dcc $y:gen_dcc))     => do
    return mkApp (← field ty "pair") #[← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $x), ← `(DCC[$ty:gen_dcc_loc] $y)]
  | `(DCC[$ty:gen_dcc_loc] (,$β:gen_dcc $x $y))                     => do
    return mkApp (← field ty "mkc") #[← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $x), ← `(DCC[$ty:gen_dcc_loc] $y)]
  | `(DCC[$ty:gen_dcc_loc] Sort $m:term)                             => do
    return mkApp (← field ty "sort") #[m]
  | `(DCC[$ty:gen_dcc_loc] (Σ$α:gen_dcc $β:gen_dcc))                => do
    return mkApp (← field ty "sigma") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] (Σ$β:gen_dcc))                         => do
    return mkApp (← field ty "coup") #[← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] (Uncoup $β:gen_dcc))                         => do
    return mkApp (← field ty "uncoup") #[← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] (Unbang $β:gen_dcc))                         => do
    return mkApp (← field ty "unbang") #[← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] (Fst $β:gen_dcc))                         => do
    return mkApp (← field ty "fstc") #[← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] (Swap $B:gen_dcc $C:gen_dcc)) => do
    return mkApp (← field ty "swap") #[← `(DCC[$ty:gen_dcc_loc] $B), ← `(DCC[$ty:gen_dcc_loc] $C)]
  | `(DCC[$ty:gen_dcc_loc] (Snd $β:gen_dcc))                         => do
    return mkApp (← field ty "sndc") #[← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] (Id $α:gen_dcc))                           => do
    return mkApp (← field ty "id") #[← `(DCC[$ty:gen_dcc_loc] $α)]
  | `(DCC[$ty:gen_dcc_loc] (Dom $α:gen_dcc))                           => do
    return mkApp (← field ty "dom") #[← `(DCC[$ty:gen_dcc_loc] $α)]
  | `(DCC[$ty:gen_dcc_loc] (∘ $f:gen_dcc $g:gen_dcc))                  => do
    return mkApp (← field ty "comp") #[← `(DCC[$ty:gen_dcc_loc] $f:gen_dcc), ← `(DCC[$ty:gen_dcc_loc] $g:gen_dcc)]
  | `(DCC[$_ty:gen_dcc_loc] #($t:term))                              => `($t)
  | `(DCC[$_ty:gen_dcc_loc] $idt:ident)                              => `($idt:term)
  | `(DCC[$ty:gen_dcc_loc] ($t:gen_dcc))                             => `(DCC[$ty:gen_dcc_loc] $t)

open Dsl in
syntax "(" gen_dcc ":" gen_dcc ")" "→" gen_dcc : gen_dcc
open Dsl in
syntax "(" ":" gen_dcc ")" "→" gen_dcc : gen_dcc

open Dsl in
macro_rules
  | `(DCC[$ty:gen_dcc_loc] ($α:gen_dcc : Sort $m) → $β:gen_dcc) =>
    `(DCC[$ty:gen_dcc_loc] ((Π (Id Sort $m) (Λ Sort $m (Id Sort $m) (`(Σ (Id Sort $m)) $β))) $α))
  | `(DCC[$ty:gen_dcc_loc] (: Sort $m) → $β:gen_dcc) =>
    `(DCC[$ty:gen_dcc_loc] (Λ Sort $m (Id Sort $m) (`(Σ(Id Sort $m)) $β)))

open Dsl in
syntax "gen_dsl" str "for" term  : command
open Dsl in
syntax "gen_dsl" str "for" "?"   : command

open Dsl in
macro_rules
  | `(gen_dsl $pre:str for ?) =>
    `(command| macro $pre:str exp:gen_dcc : term => `(DCC[?] $$exp))
  | `(gen_dsl $pre:str for $ty:ident) =>
    `(command| macro $pre:str exp:gen_dcc : term => `(DCC[$ty:ident] $$exp))
  | `(gen_dsl $pre:str for $ty:term) =>
    `(command| macro $pre:str exp:gen_dcc : term => `(DCC[$ty:term] $$exp))

open Dsl in
gen_dsl "DCC" for Unit
open Dsl in
gen_dsl "DCC?" for ?

#eval (DCC Sort 0)

def runDcc : Lean.Syntax → Lean.MacroM Lean.Syntax
  | `(gen_dcc| $e:gen_dcc) => `(DCC $e:gen_dcc)
