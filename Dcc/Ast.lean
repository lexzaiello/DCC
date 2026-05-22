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

inductive Expr where
  -- refl(f_α) env
  | refl   : Expr  → Expr
  -- eq(f_α, f_β) env
  | eq     : Expr  → Expr
  | eql    : Expr  → Expr
  | fstc   : Expr  → Expr
  | sndc   : Expr  → Expr
  | sort   : Level → Expr
  | comp'  : Expr  → Expr  → Expr
  | comp   : Expr  → Expr  → Expr
  | pair   : Expr  → Expr → Expr
  -- Σ(β) is the usual sigma type
  | sigma  : Expr  → Expr  → Expr
  | coup   : Expr  → Expr
  | mkc    : Expr  → Expr  → Expr  → Expr
  | pi     : Expr  → Expr  → Expr
  | curr   : Expr  → Expr  → Expr  → Expr
  | quot   : Expr  → Expr  → Expr
  | id     : Expr  → Expr
  | app    : Expr → Expr  → Expr
  -- ⊤ : Sort 0
  | top    : Expr
  -- ∗ : ⊤
  | tintro : Expr
  -- 0 : Sort 0
  | bot    : Expr
deriving BEq, DecidableEq

class DccLike (τ : Type) where
  refl   : τ  → τ := by exact .refl
  eq     : τ  → τ := by exact .eq
  eql    : τ  → τ := by exact .eql
  fstc   : τ  → τ := by exact .fstc
  sndc   : τ  → τ := by exact .sndc
  sort   : Level → τ := by exact .sort
  comp'  : τ  → τ  → τ := by exact .comp'
  comp   : τ  → τ  → τ := by exact .comp
  pair   : τ  → τ → τ := by exact .pair
  sigma  : τ  → τ  → τ := by exact .sigma
  coup   : τ  → τ := by exact .coup
  mkc    : τ  → τ  → τ  → τ := by exact .mkc
  pi     : τ  → τ  → τ := by exact .pi
  curr   : τ  → τ  → τ  → τ := by exact .curr
  quot   : τ  → τ  → τ := by exact .quot
  id     : τ  → τ := by exact .id
  app    : τ → τ  → τ := by exact .app
  top    : τ := by exact .top
  tintro : τ := by exact .tintro
  bot    : τ := by exact .bot

instance : DccLike Expr where

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

syntax "DCC" "[" ident "]" gen_dcc : term
syntax "DCC" "[" "." "]"   gen_dcc : term

def field (in_ty : Lean.TSyntax `ident) (fld : String) : Lean.MacroM (Lean.TSyntax `term) := do
  let nm := (in_ty.getId ++ Lean.Name.mkSimple fld).eraseMacroScopes
  return Lean.mkIdent nm

open Lean.Syntax in macro_rules
  | `(DCC[$ty:ident] ⊤)                                        => field ty "top"
  | `(DCC[$ty:ident] ⊥)                                        => field ty "bot"
  | `(DCC[$ty:ident] ∗)                                        => field ty "tintro"
  | `(DCC[$ty:ident] =($f_α:gen_dcc))                          => do
    return mkApp (← field ty "eq") #[← `(DCC[$ty:ident] $f_α)]
  | `(DCC[$ty:ident] Eql($f_α:gen_dcc))                        => do
    return mkApp (← field ty "eql") #[← `(DCC[$ty:ident] $f_α)]
  | `(DCC[$ty:ident] refl($f_α:gen_dcc))                       => do
    return mkApp (← field ty "refl") #[← `(DCC[$ty:ident] $f_α)]
  | `(DCC[$ty:ident] ($f:gen_dcc $x:gen_dcc))                  => do
    return mkApp (← field ty "app") #[← `(DCC[$ty:ident] $f:gen_dcc), ← `(DCC[$ty:ident] $x:gen_dcc)]
  | `(DCC[$ty:ident] ($f:gen_dcc $x:gen_dcc $xs:gen_dcc*))     =>
    `(DCC[$ty:ident] (($f:gen_dcc $x:gen_dcc) $xs:gen_dcc*))
  | `(DCC[$ty:ident] `($β:gen_dcc, $x:gen_dcc))                => do
    return mkApp (← field ty "quot") #[← `(DCC[$ty:ident] $β), ← `(DCC[$ty:ident] $x)]
  | `(DCC[$ty:ident] Λ($α:gen_dcc, $β:gen_dcc, $e:gen_dcc))    => do
    return mkApp (← field ty "curr") #[← `(DCC[$ty:ident] $α), ← `(DCC[$ty:ident] $β), ← `(DCC[$ty:ident] $e)]
  | `(DCC[$ty:ident] Π($α:gen_dcc, $β:gen_dcc))                => do
    return mkApp (← field ty "pi") #[← `(DCC[$ty:ident] $α), ← `(DCC[$ty:ident] $β)]
  | `(DCC[$ty:ident] ⟨$x:gen_dcc, $y:gen_dcc⟩)                 => do
    return mkApp (← field ty "pair") #[← `(DCC[$ty:ident] $x), ← `(DCC[$ty:ident] $y)]
  | `(DCC[$ty:ident] ⟦$β:gen_dcc⟧($x, $y))                     => do
    return mkApp (← field ty "mkc") #[← `(DCC[$ty:ident] $β), ← `(DCC[$ty:ident] $x), ← `(DCC[$ty:ident] $y)]
  | `(DCC[$ty:ident] Sort $m:term)                             => do
    return mkApp (← field ty "sort") #[m]
  | `(DCC[$ty:ident] Σ($α:gen_dcc, $β:gen_dcc))                => do
    return mkApp (← field ty "sigma") #[← `(DCC[$ty:ident] $α), ← `(DCC[$ty:ident] $β)]
  | `(DCC[$ty:ident] Coup($β:gen_dcc))                         => do
    return mkApp (← field ty "coup") #[← `(DCC[$ty:ident] $β)]
  | `(DCC[$ty:ident] Fstc($β:gen_dcc))                         => do
    return mkApp (← field ty "fstc") #[← `(DCC[$ty:ident] $β)]
  | `(DCC[$ty:ident] Sndc($β:gen_dcc))                         => do
    return mkApp (← field ty "sndc") #[← `(DCC[$ty:ident] $β)]
  | `(DCC[$ty:ident] Id($α:gen_dcc))                           => do
    return mkApp (← field ty "id") #[← `(DCC[$ty:ident] $α)]
  | `(DCC[$ty:ident] $f:gen_dcc ∘' $g:gen_dcc)                 => do
    return mkApp (← field ty "comp'") #[← `(DCC[$ty:ident] $f:gen_dcc), ← `(DCC[$ty:ident] $g:gen_dcc)]
  | `(DCC[$ty:ident] $f:gen_dcc ∘ $g:gen_dcc)                  => do
    return mkApp (← field ty "comp") #[← `(DCC[$ty:ident] $f:gen_dcc), ← `(DCC[$ty:ident] $g:gen_dcc)]
  | `(DCC[$_ty:ident] #($t:term))                              => `($t)
  | `(DCC[$_ty:ident] $idt:ident)                              => `($idt:term)
  | `(DCC[$ty:ident] ($t:gen_dcc))                             => `(DCC[$ty:ident] $t)

syntax "gen_dsl" str "for" term : command

macro_rules
  | `(gen_dsl $pre:str for $ty:ident) =>
    `(command| macro $pre:str exp:gen_dcc : term => `(DCC[$ty:ident] $$exp))

gen_dsl "DCC"  for Expr
gen_dsl "DCC*" for DccLike

def runDcc : Lean.TSyntax `gen_dcc → Lean.MacroM Lean.Syntax
  | `(gen_dcc| $e:gen_dcc) => `(DCC $e:gen_dcc)
