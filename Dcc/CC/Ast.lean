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

we can derive `()

Λ(Fst(α, β)
-/

inductive Expr where
  | sort  : Level → Expr
  | fst   : Expr  → Expr
  | snd   : Expr  → Expr
  | snd'  : Expr  → Expr  → Expr
  | comp  : Expr  → Expr  → Expr
  | pair  : Expr  → Expr  → Expr  → Expr
  | sigma : Expr  → Expr
  | mk    : Expr  → Expr  → Expr  → Expr
  | pi    : Level → Expr  → Expr  → Expr
  | curr  : Expr  → Expr  → Expr
  | appl  : Expr → Expr
  | quot  : Expr  → Expr  → Expr
  | id    : Expr  → Expr
  | app   : Expr  → Expr  → Expr
deriving BEq, Repr, DecidableEq

declare_syntax_cat expr

syntax "#(" term ")"                                             : expr
syntax:max "`(" expr,* ")"                                       : expr
syntax:max "Id(" expr,* ")"                                      : expr
syntax:max "Fst(" expr,* ")"                                     : expr
syntax:max "Snd'(" expr,* ")"                                    : expr
syntax:max "App(" expr,* ")"                                     : expr
syntax:max "Snd(" expr,* ")"                                     : expr
syntax "Σ(" expr,* ")"                                           : expr
syntax:max (priority := high) "Λ(" expr,* ")"                    : expr
syntax:max (priority := high) "Π(" term "," expr,* ")"           : expr
syntax expr "∘" expr                                             : expr
syntax:30 ident                                                  : expr
syntax "(" expr+ ")"                                             : expr
syntax:max "Sort" term                                           : expr
syntax (priority := high) "⟦" expr,* "⟧" "⟨" expr,* "⟩" : expr
syntax (priority := high) "⟦" expr,* "⟧" "(" expr,* ")"          : expr

syntax "DCC"  expr : term

macro_rules
  | `(DCC ($f:expr $x:expr))                    => `(Expr.app   (DCC $f:expr)   (DCC $x:expr))
  | `(DCC ($f:expr $x:expr $xs:expr*))          => `(DCC (($f:expr $x:expr) $xs:expr*))
  | `(DCC `($β:expr, $x:expr))                  => `(Expr.quot (DCC $β) (DCC $x))
  | `(DCC Λ($α:expr, $e:expr))                  => `(Expr.curr (DCC $α) (DCC $e))
  | `(DCC Π($m:term, $α:expr, $β:expr))         => `(Expr.pi $m (DCC $α) (DCC $β))
  | `(DCC ⟦$β:expr⟧⟨$x:expr, $y:expr⟩)          => `(Expr.pair (DCC $β) (DCC $x) (DCC $y))
  | `(DCC ⟦$β:expr⟧($x, $y))                    => `(Expr.mk (DCC $β) (DCC $x) (DCC $y))
  | `(DCC Sort $m:term)                         => `(Expr.sort $m)
  | `(DCC Σ($β:expr))                           => `(Expr.sigma (DCC $β))
  | `(DCC Fst($β:expr))                         => `(Expr.fst (DCC $β))
  | `(DCC Snd($β:expr))                         => `(Expr.snd (DCC $β))
  | `(DCC Snd'($α:expr, $β:expr))               => `(Expr.snd' (DCC $α) (DCC $β))
  | `(DCC App($β:expr))                         => `(Expr.appl (DCC $β))
  | `(DCC Id($α:expr))                          => `(Expr.id (DCC $α))
  | `(DCC $f:expr ∘ $g:expr)                    => `(Expr.comp (DCC $f:expr) (DCC $g:expr))
  | `(DCC #($t:term))                           => `($t)
  | `(DCC $idt:ident)                           => `($idt:term)
  | `(DCC ($t:expr))                            => `(DCC $t)

namespace Expr

def toFormat (e : Expr) : Std.Format :=
  match e with
  | (DCC `(β, x))       => "`(" ++ β.toFormat ++ ", " ++ x.toFormat ++ ")"
  | (DCC Id(α))         => "Id(" ++ α.toFormat ++ ")"
  | (DCC Sort m)        => s!"Sort {m}"
  | (DCC Fst(β))        => "Fst(" ++ β.toFormat ++ ")"
  | (DCC Snd'(α, β))    => "Snd'(" ++ α.toFormat ++ ", " ++ β.toFormat ++ ")"
  | (DCC Snd(β))        => "Snd(" ++ β.toFormat ++ ")"
  | (DCC App(β))        => "App(" ++ β.toFormat ++ ")"
  | (DCC Λ(α, e))       => "Λ(" ++ α.toFormat ++ ", " ++ e.toFormat ++ ")"
  | (DCC Π(m, α, β))    => "Π" ++ (.bracket "(" ((Std.format m) ++ ", " ++ α.toFormat ++ ", " ++ β.toFormat) ")")
  | (DCC ⟦β⟧⟨a, b⟩)     => (.bracket "⟦" β.toFormat "⟧") ++ (.bracket "⟨" (a.toFormat ++ ", " ++ b.toFormat) "⟩")
  | (DCC ⟦β⟧(a, b))     => (.bracket "⟦" β.toFormat "⟧") ++ (.bracket "(" (a.toFormat ++ ", " ++ b.toFormat) ")")
  | (DCC Σ(β))          => "Σ" ++ (.bracket "(" β.toFormat ")")
  | (DCC f ∘ g)         => (.bracket "(" (f.toFormat ++ " ∘ " ++ g.toFormat) ")")
  | (DCC (f x))         => .bracket "(" (f.toFormat ++ " " ++ x.toFormat) ")"

instance instToFormat : Std.ToFormat Expr := ⟨toFormat⟩
instance instToString : ToString Expr     := ⟨toString ∘ toFormat⟩

end Expr
