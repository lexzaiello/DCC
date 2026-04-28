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
  | sort   : Level → Expr
  | fst    : Expr  → Expr
  | snd    : Expr  → Expr
  | snd'   : Expr  → Expr  → Expr
  | comp   : Expr  → Expr  → Expr
  | pair   : Level → Expr  → Expr  → Expr → Expr → Expr → Expr
  -- Σ(β) is the usual sigma type
  | sigma  : Expr  → Expr
  | mk     : Expr  → Expr  → Expr  → Expr
  | pi     : Expr  → Expr  → Expr
  | curr   : Expr  → Expr  → Expr  → Expr
  | app'   : Expr  → Expr  → Expr
  | appl   : Level → Level → Expr  → Expr  → Expr
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

syntax "#(" term ")"                                             : expr
syntax "⊤"                                                       : expr
syntax "∗"                                                       : expr
syntax "⊥"                                                       : expr
syntax:max "`(" expr,* ")"                                       : expr
syntax:max "Id(" expr,* ")"                                      : expr
syntax:max "Fst(" expr,* ")"                                     : expr
syntax:max "Snd'(" expr,* ")"                                    : expr
syntax:max "App'(" expr,* ")"                                    : expr
syntax:max "App(" term "," term "," expr,* ")"          : expr
syntax:max "Snd(" expr,* ")"                                     : expr
syntax:max "Subst(" expr,* ")"                                   : expr
syntax "Σ(" expr ")"                                             : expr
syntax:max (priority := high) "Λ(" expr,* ")"                    : expr
syntax:max (priority := high) "Π(" expr,* ")"                    : expr
syntax expr "∘" expr                                             : expr
syntax:30 ident                                                  : expr
syntax "(" expr+ ")"                                             : expr
syntax:max "Sort" term                                           : expr
syntax (priority := high) "⟦" term "," expr,* "⟧" "⟨" expr,* "⟩"          : expr
syntax (priority := high) "⟦" expr,* "⟧" "(" expr,* ")"          : expr

syntax "DCC"  expr : term

macro_rules
  | `(DCC ⊤)                                     => `(Expr.top)
  | `(DCC ⊥)                                     => `(Expr.bot)
  | `(DCC ∗)                                     => `(Expr.tintro)
  | `(DCC ($f:expr $x:expr))                     => `(Expr.app   (DCC $f:expr)   (DCC $x:expr))
  | `(DCC ($f:expr $x:expr $xs:expr*))           => `(DCC (($f:expr $x:expr) $xs:expr*))
  | `(DCC `($β:expr, $x:expr))                   => `(Expr.quot (DCC $β) (DCC $x))
  | `(DCC Λ($α:expr, $β:expr, $e:expr))          => `(Expr.curr (DCC $α) (DCC $β) (DCC $e))
  | `(DCC Π($α:expr, $β:expr))                   => `(Expr.pi (DCC $α) (DCC $β))
  | `(DCC ⟦$m:term, $α:expr, $β:expr, $γ:expr⟧⟨$x:expr, $y:expr⟩) => `(Expr.pair $m (DCC $α) (DCC $β) (DCC $γ) (DCC $x) (DCC $y))
  | `(DCC ⟦$β:expr⟧($x, $y))                     => `(Expr.mk (DCC $β) (DCC $x) (DCC $y))
  | `(DCC Sort $m:term)                          => `(Expr.sort $m)
  | `(DCC Σ($β:expr))                            => `(Expr.sigma (DCC $β))
  | `(DCC Fst($β:expr))                          => `(Expr.fst (DCC $β))
  | `(DCC Snd($β:expr))                          => `(Expr.snd (DCC $β))
  | `(DCC Snd'($α:expr, $β:expr))                => `(Expr.snd' (DCC $α) (DCC $β))
  | `(DCC App'($α:expr, $β:expr))       => `(Expr.app' (DCC $α) (DCC $β))
  | `(DCC App($m, $n, $f_α:expr, $f_β:expr)) => `(Expr.appl $m $n (DCC $f_α) (DCC $f_β))
  | `(DCC Id($α:expr))                           => `(Expr.id (DCC $α))
  | `(DCC Subst($x:expr, $β:expr))               => `(Expr.subst (DCC $x) (DCC $β))
  | `(DCC $f:expr ∘ $g:expr)                     => `(Expr.comp (DCC $f:expr) (DCC $g:expr))
  | `(DCC #($t:term))                            => `($t)
  | `(DCC $idt:ident)                            => `($idt:term)
  | `(DCC ($t:expr))                             => `(DCC $t)

namespace Expr


def toFormat (e : Expr) : Std.Format :=
  let sepD (l : List Std.Format) (sep : Std.Format := ",") (indent : ℕ := 2) : Std.Format :=
    .nest indent (.fill (.joinSep l (sep ++ .line)))
  let paren (s : Std.Format) : Std.Format :=
    .bracket "(" (.fill s) ")"
  let angle (s : Std.Format) : Std.Format :=
    .bracket "⟨" (.fill s) "⟩"
  let bbracket (s : Std.Format) : Std.Format :=
    .bracket "⟦" (.fill s) "⟧"

  let comb (pre : Std.Format) (points : List Std.Format) : Std.Format :=
    .group (pre ++ (paren (sepD points (indent := pre.pretty.length))))

  match e with
  | (DCC ⊤)                   => "⊤"
  | (DCC ⊥)                   => "⊥"
  | (DCC ∗)                   => "∗"
  | (DCC `(β, x))             => comb "`" [β.toFormat, x.toFormat]
  | (DCC Id(α))               => comb "Id" [α.toFormat]
  | (DCC Subst(β, x))         => comb "Subst" [β.toFormat, x.toFormat]
  | (DCC Sort m)              => "Sort " ++ (Std.format m)
  | (DCC Fst(β))              => comb "Fst" [β.toFormat]
  | (DCC Snd(β))              => comb "Snd" [β.toFormat]
  | (DCC Snd'(α, β))          => comb "Snd'" [α.toFormat, β.toFormat]
  | (DCC App'(α, β))          => comb "App'" [α.toFormat, β.toFormat]
  | (DCC App(m, n, f_α, f_β)) => comb "App" [Std.format m, Std.format n, f_α.toFormat, f_β.toFormat]
  | (DCC Λ(α, β, e))          => comb "Λ" [α.toFormat, β.toFormat, e.toFormat]
  | (DCC Π(α, β))             => comb "Π" [α.toFormat, β.toFormat]
  | (DCC ⟦m, α, β, γ⟧⟨a, b⟩)  =>
    let pts := (bbracket (sepD [Std.format m, α.toFormat, β.toFormat, γ.toFormat]))
    let pts_length := match pts.pretty.splitOn "\n" |>.head? with
    | .some line => line.length
    | .none      => 0
    pts ++ (angle (sepD [a.toFormat, b.toFormat] (indent := pts_length)))
  | (DCC ⟦β⟧(a, b))           =>
    comb (bbracket (sepD [β.toFormat])) [a.toFormat, b.toFormat]
  | (DCC Σ(β))                => comb "Σ" [β.toFormat]
  | (DCC f ∘ g)               =>
    sepD [f.toFormat, g.toFormat] " ∘"
  | (DCC (f x))               => (paren (f.toFormat ++ (.indentD x.toFormat)))

instance instToFormat : Std.ToFormat Expr := ⟨toFormat⟩
instance instToString : ToString Expr     := ⟨toString ∘ toFormat⟩
instance instRepr : Repr Expr := ⟨Function.const _ ∘ toFormat⟩

instance instOptToFormat : Std.ToFormat (Option Expr) := ⟨fun me =>
  match me with
  | .none => Std.format me
  | .some e =>
    let l := "(some".length.succ
    .group ("(some " ++ (.fill (.nest l e.toFormat)) ++ ")")⟩

end Expr
