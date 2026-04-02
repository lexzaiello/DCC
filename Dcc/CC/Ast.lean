import Mathlib.Data.Nat.Notation

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

Fst(α

Π(B) A x = B ⟦A, x⟧
-/

inductive Expr where
  | sort  : Level → Expr
  | id    : Expr  → Expr
  | fst   : Expr  → Expr → Expr
  | snd   : Expr  → Expr → Expr
  | comp  : Expr  → Expr → Expr
  | pair  : Expr  → Expr → Expr
  | sigma : Expr  → Expr → Expr
  | mk    : Expr  → Expr → Expr
  | pi    : Expr  → Expr
  | curr  : Expr  → Expr
  | appl  : Expr  → Expr → Expr
  | app   : Expr  → Expr → Expr
deriving BEq, Repr, DecidableEq

declare_syntax_cat expr

syntax "#(" term ")"                         : expr
syntax:max "Id(" expr ")"                    : expr
syntax:max "Fst(" expr,* ")"                 : expr
syntax:max "App(" expr,* ")"                 : expr
syntax:max "Snd(" expr,* ")"                 : expr
syntax "Σ" expr "," expr                     : expr
syntax "Σ" expr "," expr                     : expr
syntax:max (priority := high) "Λ(" expr ")"  : expr
syntax:max (priority := high) "Π(" expr ")"  : expr
syntax expr "∘" expr                         : expr
syntax:30 ident                              : expr
syntax "(" expr+ ")"                         : expr
syntax:max "Sort" term                       : expr
syntax (priority := high) "⟨" expr,* "⟩"     : expr
syntax (priority := high) "⟦" expr,* "⟧"     : expr

syntax "DCC"  expr : term

macro_rules
  | `(DCC ($f:expr $x:expr))             => `(Expr.app   (DCC $f:expr)   (DCC $x:expr))
  | `(DCC ($f:expr $x:expr $xs:expr*))   => `(DCC (($f:expr $x:expr) $xs:expr*))
  | `(DCC Λ($e:expr))                    => `(Expr.curr (DCC $e))
  | `(DCC Π($e:expr))                    => `(Expr.pi (DCC $e))
  | `(DCC ⟨$x:expr, $y:expr⟩)            => `(Expr.pair (DCC $x) (DCC $y))
  | `(DCC ⟦$x:expr, $y:expr⟧)            => `(Expr.coup (DCC $x) (DCC $y))
  | `(DCC Sort $m:term)                  => `(Expr.sort $m)
  | `(DCC Σ $α:expr, $β:expr)            => `(Expr.sigma (DCC $α) (DCC $β))
  | `(DCC Id($α:expr))                   => `(Expr.id (DCC $α))
  | `(DCC Fst($α:expr, $β:expr))         => `(Expr.fst (DCC $α) (DCC $β))
  | `(DCC Snd($α:expr, $β:expr))         => `(Expr.snd (DCC $α) (DCC $β))
  | `(DCC App($α:expr, $β:expr))         => `(Expr.appl (DCC $α) (DCC $β))
  | `(DCC $f:expr ∘ $g:expr)             => `(Expr.comp (DCC $f:expr) (DCC $g:expr))
  | `(DCC #($t:term))                    => `($t)
  | `(DCC $idt:ident)                    => `($idt:term)
  | `(DCC ($t:expr))                     => `(DCC $t)
  
