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
  | fst   : Expr  → Expr  → Expr
  | snd   : Expr  → Expr  → Expr
  | snd'  : Expr  → Expr  → Expr
  | comp  : Expr  → Expr  → Expr
  | pair  : Level → Expr  → Expr  → Expr  → Expr → Expr → Expr
  -- Σ(β) is the usual sigma type
  | sigma : Expr  → Expr
  | mk    : Expr  → Expr  → Expr  → Expr
  | pi    : Expr  → Expr  → Expr
  | curr  : Expr  → Expr  → Expr  → Expr
  | appl  : Expr  → Expr  → Expr
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
  | `(DCC ($f:expr $x:expr))                     => `(Expr.app   (DCC $f:expr)   (DCC $x:expr))
  | `(DCC ($f:expr $x:expr $xs:expr*))           => `(DCC (($f:expr $x:expr) $xs:expr*))
  | `(DCC `($β:expr, $x:expr))                   => `(Expr.quot (DCC $β) (DCC $x))
  | `(DCC Λ($α:expr, $β:expr, $e:expr))          => `(Expr.curr (DCC $α) (DCC $β) (DCC $e))
  | `(DCC Π($α:expr, $β:expr))                   => `(Expr.pi (DCC $α) (DCC $β))
  | `(DCC ⟦$m:term, $α:expr, $β:expr, $γ:expr⟧⟨$x:expr, $y:expr⟩) => `(Expr.pair $m (DCC $α) (DCC $β) (DCC $γ) (DCC $x) (DCC $y))
  | `(DCC ⟦$β:expr⟧($x, $y))                     => `(Expr.mk (DCC $β) (DCC $x) (DCC $y))
  | `(DCC Sort $m:term)                          => `(Expr.sort $m)
  | `(DCC Σ($β:expr))                            => `(Expr.sigma (DCC $β))
  | `(DCC Fst($α:expr, $β:expr))                 => `(Expr.fst (DCC $α) (DCC $β))
  | `(DCC Snd($α:expr, $β:expr))                 => `(Expr.snd (DCC $α) (DCC $β))
  | `(DCC Snd($β:expr))                          => `(Expr.snd (DCC $β))
  | `(DCC Snd'($α:expr, $β:expr))                => `(Expr.snd' (DCC $α) (DCC $β))
  | `(DCC App($α:expr, $β:expr))                 => `(Expr.appl (DCC $α) (DCC $β))
  | `(DCC Id($α:expr))                           => `(Expr.id (DCC $α))
  | `(DCC $f:expr ∘ $g:expr)                     => `(Expr.comp (DCC $f:expr) (DCC $g:expr))
  | `(DCC #($t:term))                            => `($t)
  | `(DCC $idt:ident)                            => `($idt:term)
  | `(DCC ($t:expr))                             => `(DCC $t)

namespace Expr

def toFormat (e : Expr) : Std.Format :=
  match e with
  | (DCC `(β, x))            => "`(" ++ β.toFormat ++ ", " ++ x.toFormat ++ ")"
  | (DCC Id(α))              => "Id(" ++ α.toFormat ++ ")"
  | (DCC Sort m)             => "Sort " ++ (Std.format m)
  | (DCC Fst(α, β))          => "Fst" ++ .bracket "(" (.joinSep [α.toFormat, β.toFormat] ", ") ")"
  | (DCC Snd(α, β))          => "Snd" ++ .bracket "(" (.joinSep [α.toFormat, β.toFormat] ", ") ")"
  | (DCC Snd'(α, β))         => "Snd'" ++ .bracket "(" (.joinSep [α.toFormat, β.toFormat] ", ") ")"
  | (DCC App(α, β))          => "App(" ++ α.toFormat ++ ", " ++ β.toFormat ++ ")"
  | (DCC Λ(α, β, e))         => "Λ(" ++ (.joinSep [α.toFormat, β.toFormat, e.toFormat] ", ") ++ ")"
  | (DCC Π(α, β))            => "Π" ++ (.bracket "(" (α.toFormat ++ ", " ++ β.toFormat) ")")
  | (DCC ⟦m, α, β, γ⟧⟨a, b⟩)    => (.bracket "⟦" (.joinSep [Std.format m, α.toFormat, β.toFormat, γ.toFormat] ", ") "⟧")
    ++ (.bracket "⟨" (a.toFormat ++ ", " ++ b.toFormat) "⟩")
  | (DCC ⟦β⟧(a, b))          => (.bracket "⟦" β.toFormat "⟧") ++ (.bracket "(" (a.toFormat ++ ", " ++ b.toFormat) ")")
  | (DCC Σ(β))               => "Σ" ++ (.bracket "(" β.toFormat ")")
  | (DCC f ∘ g)              => (.bracket "(" (f.toFormat ++ " ∘ " ++ g.toFormat) ")")
  | (DCC (f x))              => .bracket "(" (f.toFormat ++ " " ++ x.toFormat) ")"

instance instToFormat : Std.ToFormat Expr := ⟨toFormat⟩
instance instToString : ToString Expr     := ⟨toString ∘ toFormat⟩

/-
⟦β⟧(x, y) : Σ(Λ(Id(Sort m), β)) α <- β receives (α, x)
β : α → Sort n
-/

/-
β receives (x : α)

DCC (Σ(Λ(Sort m, Fst(`(Sort m, `(Sort m, α)), α), β)) α)
-/
def coup.type (α β : Expr) (m : Level) : Expr :=
  DCC (Σ(`(Sort m, β)) α)

/-
The main Fst is indexed by the environment map and the environment:

Fst(f_β, env).

Fstc is a derived version of Fst more closely aligned with traditional couples.

Fstc(α, β) ⟦β⟧(x, y) : α
Sndc(α, β) ⟦β⟧(x, y) : β (α, x)

Snd' is specifically for couples with this encoding.

Curry is also designed for couples with the (α, x) β encoding.
That is, β in ⟦β⟧(x, y) receives (α, x)
-/
def mk_fstc (α β : Expr) (m : Level) : Expr :=
  DCC Fst(`(Sort m, β), α)

def mk_sndc (α β : Expr) (m : Level) : Expr :=
  DCC Snd(`(Sort m, β), α)

syntax "Fstc(" term "," expr,* ")" : expr
syntax "Sndc(" term "," expr,* ")" : expr
syntax "Coup(" term "," expr,* ")" : expr

syntax "(" expr ":" expr ")" "→" expr : expr

macro_rules
  | `(DCC Fstc($m:term, $α:expr, $β:expr)) => `(mk_fstc (DCC $α) (DCC $β) $m)
  | `(DCC Sndc($m:term, $α:expr, $β:expr)) => `(mk_sndc (DCC $α) (DCC $β) $m)
  | `(DCC Coup($m:term, $α:expr, $β:expr)) => `(coup.type (DCC $α) (DCC $β) $m)

def arrow (α β : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), Λ(Sort m, Id(Sort m), `(Coup(m.succ, Sort m, Id(Sort m)), β))) α)

macro_rules
  | `(DCC ($α:expr : Sort $m) → $β:expr) => `(arrow (DCC $α) (DCC $β) $m)

/-
Version of quotation that is point-free with respect to x.

β is not dependent.
-/
def quot' (α β : Expr) (m : Level) : Expr :=
  DCC Λ(α, `(Coup(m.succ, Sort m, Id(Sort m)), β), Fstc(m, α, `(Coup(m.succ, Sort m, Id(Sort m)), β)))

syntax "Quot(" term "," expr,* ")" : expr

macro_rules
  | `(DCC Quot($m:term, $α:expr, $β:expr)) => `(quot' (DCC $α) (DCC $β) $m)

end Expr
