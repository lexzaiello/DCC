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
  | eq     : Expr  → Expr → Expr
  | fstc   : Expr  → Expr
  | sndc   : Expr  → Expr
  | sort   : Level → Expr
  | fst    : Expr  → Expr  → Expr
  | snd    : Expr  → Expr  → Expr
  | snd'   : Expr  → Expr  → Expr
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
  | subst  : Expr  → Expr  → Expr
  | app    : Expr → Expr  → Expr
  -- ⊤ : Sort 0
  | top    : Expr
  -- ∗ : ⊤
  | tintro : Expr
  -- 0 : Sort 0
  | bot    : Expr
deriving BEq, DecidableEq

declare_syntax_cat expr

syntax "=(" expr,* ")"                                           : expr
syntax "refl(" expr,* ")"                                        : expr
syntax "#(" term ")"                                             : expr
syntax "⊤"                                                       : expr
syntax "∗"                                                       : expr
syntax "⊥"                                                       : expr
syntax:max "`(" expr,* ")"                                       : expr
syntax:max "Id(" expr,* ")"                                      : expr
syntax:max "Fst(" expr,* ")"                                     : expr
syntax:max "Fstc(" expr,* ")"                                    : expr
syntax:max "Sndc(" expr,* ")"                                    : expr
syntax:max "Snd'(" expr,* ")"                                    : expr
syntax:max "Snd(" expr,* ")"                                     : expr
syntax:max "Subst(" expr,* ")"                                   : expr
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
  | `(DCC =($f_α:expr, $f_β:expr))               => `(Expr.eq (DCC $f_α) (DCC $f_β))
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
  | `(DCC Fst($α:expr, $β:expr))                 => `(Expr.fst (DCC $α) (DCC $β))
  | `(DCC Snd($α:expr, $β:expr))                 => `(Expr.snd (DCC $α) (DCC $β))
  | `(DCC Fstc($β:expr))                         => `(Expr.fstc (DCC $β))
  | `(DCC Sndc($β:expr))                         => `(Expr.sndc (DCC $β))
  | `(DCC Snd($β:expr))                          => `(Expr.snd (DCC $β))
  | `(DCC Snd'($α:expr, $β:expr))                => `(Expr.snd' (DCC $α) (DCC $β))
  | `(DCC Id($α:expr))                           => `(Expr.id (DCC $α))
  | `(DCC Subst($x:expr, $β:expr))               => `(Expr.subst (DCC $x) (DCC $β))
  | `(DCC $f:expr ∘' $g:expr)                    => `(Expr.comp' (DCC $f:expr) (DCC $g:expr))
  | `(DCC $f:expr ∘ $g:expr)                     => `(Expr.comp (DCC $f:expr) (DCC $g:expr))
  | `(DCC #($t:term))                            => `($t)
  | `(DCC $idt:ident)                            => `($idt:term)
  | `(DCC ($t:expr))                             => `(DCC $t)

def runDcc : Lean.Syntax → Lean.MacroM Lean.Syntax
  | `(expr| $e:expr) => `(DCC $e:expr)
