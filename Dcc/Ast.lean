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
  | mk     : Expr  → Expr  → Expr  → Expr
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
  mkc    : τ  → τ  → τ  → τ := by exact .mk
  pi     : τ  → τ  → τ := by exact .pi
  curr   : τ  → τ  → τ  → τ := by exact .curr
  quot   : τ  → τ  → τ := by exact .quot
  id     : τ  → τ := by exact .id
  app    : τ → τ  → τ := by exact .app
  top    : τ := by exact .top
  tintro : τ := by exact .tintro
  bot    : τ := by exact .bot

instance : DccLike Expr where

syntax "gen_dsl" str "for" term : command

macro_rules
  | `(gen_dsl $pre:str for $ty:ident) => do
    let field : Lean.Name → Lean.Name := .str pre
    let cat : Lean.TSyntax `ident   :=
      ⟨Lean.mkIdent (.str .anonymous s!"expr_{pre}")⟩
    let mk_cat : Lean.TSyntaxArray `command := #[
      ← `(command| declare_syntax_cat $cat:ident),
      ← `(command| syntax "=(" $cat:ident,* ")"                        : $cat:ident),
      ← `(command| syntax "Eql(" $cat:ident,* ")"                      : $cat:ident),
      ← `(command| syntax "refl(" $cat:ident,* ")"                     : $cat:ident),
      ← `(command| syntax "#(" term ")"                                : $cat:ident),
      ← `(command| syntax "⊤"                                          : $cat:ident),
      ← `(command| syntax "∗"                                          : $cat:ident),
      ← `(command| syntax "⊥"                                          : $cat:ident),
      ← `(command| syntax:max "`(" $cat:ident,* ")"                    : $cat:ident),
      ← `(command| syntax:max "Id(" $cat:ident,* ")"                   : $cat:ident),
      ← `(command| syntax:max "Fstc(" $cat:ident,* ")"                 : $cat:ident),
      ← `(command| syntax:max "Sndc(" $cat:ident,* ")"                 : $cat:ident),
      ← `(command| syntax "Σ(" $cat:ident,* ")"                        : $cat:ident),
      ← `(command| syntax "Coup(" $cat:ident ")"                       : $cat:ident),
      ← `(command| syntax:max (priority := high) "Λ(" $cat:ident,* ")" : $cat:ident),
      ← `(command| syntax:max (priority := high) "Π(" $cat:ident,* ")" : $cat:ident),
      ← `(command| syntax $cat:ident "∘'" $cat:ident                   : $cat:ident),
      ← `(command| syntax $cat:ident "∘" $cat:ident                    : $cat:ident),
      ← `(command| syntax:30 ident                                     : $cat:ident),
      ← `(command| syntax "(" $cat:ident+ ")"                          : $cat:ident),
      ← `(command| syntax:max "Sort" term                              : $cat:ident),
      ← `(command| syntax (priority := high) "⟨" $cat:ident,* "⟩"      : $cat:ident),
      ← `(command| syntax (priority := high) "⟦" $cat:ident,* "⟧"
                                                  "(" $cat:ident,* ")" : $cat:ident)
    ]
    let parser : Lean.TSyntax `command ← `(command| syntax $pre:str $cat:ident : term)
    
    sorry

declare_syntax_cat expr

syntax "=(" expr,* ")"                                           : expr
syntax "Eql(" expr,* ")"                                         : expr
syntax "refl(" expr,* ")"                                        : expr
syntax "#(" term ")"                                             : expr
syntax "⊤"                                                       : expr
syntax "∗"                                                       : expr
syntax "⊥"                                                       : expr
syntax:max "`(" expr,* ")"                                       : expr
syntax:max "Id(" expr,* ")"                                      : expr
syntax:max "Fstc(" expr,* ")"                                    : expr
syntax:max "Sndc(" expr,* ")"                                    : expr
syntax "Σ(" expr,* ")"                                           : expr
syntax "Coup(" expr ")"                                          : expr
syntax:max (priority := high) "Λ(" expr,* ")"                    : expr
syntax:max (priority := high) "Π(" expr,* ")"                    : expr
syntax expr "∘'" expr                                            : expr
syntax expr "∘" expr                                             : expr
syntax:30 ident                                                  : expr
syntax "(" expr+ ")"                                             : expr
syntax:max "Sort" term                                           : expr
syntax (priority := high) "⟨" expr,* "⟩"                         : expr
syntax (priority := high) "⟦" expr,* "⟧" "(" expr,* ")"          : expr

syntax "DCC"  expr : term

macro_rules
  | `(DCC ⊤)                                     => `(Expr.top)
  | `(DCC ⊥)                                     => `(Expr.bot)
  | `(DCC ∗)                                     => `(Expr.tintro)
  | `(DCC =($f_α:expr))                          => `(Expr.eq (DCC $f_α))
  | `(DCC Eql($f_α:expr))                        => `(Expr.eql (DCC $f_α))
  | `(DCC refl($f_α:expr))                       => `(Expr.refl (DCC $f_α))
  | `(DCC ($f:expr $x:expr))                     => `(Expr.app   (DCC $f:expr)   (DCC $x:expr))
  | `(DCC ($f:expr $x:expr $xs:expr*))           => `(DCC (($f:expr $x:expr) $xs:expr*))
  | `(DCC `($β:expr, $x:expr))                   => `(Expr.quot (DCC $β) (DCC $x))
  | `(DCC Λ($α:expr, $β:expr, $e:expr))          => `(Expr.curr (DCC $α) (DCC $β) (DCC $e))
  | `(DCC Π($α:expr, $β:expr))                   => `(Expr.pi (DCC $α) (DCC $β))
  | `(DCC ⟨$x:expr, $y:expr⟩)                    => `(Expr.pair (DCC $x) (DCC $y))
  | `(DCC ⟦$β:expr⟧($x, $y))                     => `(Expr.mk (DCC $β) (DCC $x) (DCC $y))
  | `(DCC Sort $m:term)                          => `(Expr.sort $m)
  | `(DCC Σ($α:expr, $β:expr))                   => `(Expr.sigma (DCC $α) (DCC $β))
  | `(DCC Coup($β:expr))                         => `(Expr.coup (DCC $β))
  | `(DCC Fstc($β:expr))                         => `(Expr.fstc (DCC $β))
  | `(DCC Sndc($β:expr))                         => `(Expr.sndc (DCC $β))
  | `(DCC Id($α:expr))                           => `(Expr.id (DCC $α))
  | `(DCC $f:expr ∘' $g:expr)                    => `(Expr.comp' (DCC $f:expr) (DCC $g:expr))
  | `(DCC $f:expr ∘ $g:expr)                     => `(Expr.comp (DCC $f:expr) (DCC $g:expr))
  | `(DCC #($t:term))                            => `($t)
  | `(DCC $idt:ident)                            => `($idt:term)
  | `(DCC ($t:expr))                             => `(DCC $t)

def runDcc : Lean.Syntax → Lean.MacroM Lean.Syntax
  | `(expr| $e:expr) => `(DCC $e:expr)
