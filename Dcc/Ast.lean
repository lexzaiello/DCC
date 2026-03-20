import Mathlib.Data.Nat.Notation
open Std (ToFormat Format)
open Std.ToFormat (format)

-- Infinite sort universe hierarchy
abbrev Level := ℕ

-- Core computational combinators. Standard. K' for downgrading a dependent type to a nondependent one.
inductive Comb where
  | K'     : Level → Level → Comb
  | K      : Level → Level → Comb
  | S      : Level → Level → Level → Comb
deriving BEq, Repr, Lean.ToExpr, DecidableEq

/-
The type combinators are seperate from the term-level combinators.
They have no types, except when inferred under a Π binder.
Note that this is BCKI.
Size is guaranteed to decrease.
Can reduce all type transformations at once.
-/
inductive TyComb where
  | I : TyComb
  | 
deriving BEq, Repr, Lean.ToExpr, DecidableEq

inductive Expr where
  | tyhole : Expr   → Expr -- __ : τ. May not be necessary due to inference rule for BCKI. Vestigial.
  | tycomb : TyComb → Expr
  | Pi     : Expr   → Expr → Expr -- Binders. No →. Form → with Π + K*.
  | Srt    : Level  → Expr
  | comb   : Comb   → Expr
  | app    : Expr   → Expr → Expr
deriving BEq, Repr, Lean.ToExpr, DecidableEq

/-
DSL:
  Type combinators:
  - K* = Expr.tycomb .next
  - B = Expr.tycomb .comp
  - I = Expr.tycomb .read
  - C = Expr.tycomb .flip

  Types:
  - Π α, β = Expr.Pi (SK α) (SK β)
  - Sort m = Expr.Srt m

  Core:
  - S.{[m, n, o]} = .comb (.S m n o)
    Where m, n, o refer to universe levels.
  - K'.{[m, n]} = .comb (.K' m n )
    Where m, n refer to universe levels.
  - K.{[m, n]} = .comb (.K m n)
    Where m, n refer to universe levels.
  - (f x_1 ... x_n) = (.app (SK f) (SK x_1)).app ...

  Utility macros (not corresponding to AST elements directly):
  - Arrow macro:
    - α → β = (Π α, K* β)
  - Arg macro:
    - (arg 0 f) = B f I
    - (arg (n + 1) f) = K* (arg n f)
    This macro allows discarding `n` arguments under a Π binder, then applying a function to the selected argument to it.
    Kind of simulates Debruijn Indices: (arg 1 I) a b = I b.
  - Ret macro:
    - (ret 0) = I
    - (ret (n + 1)) = (B K* (ret n))
    This macro is the inverse of arg. It discards `m` arguments after a "selected" argument:
    (arg 1 (ret 1)) a b c = b
-/

namespace dsl

declare_syntax_cat expr

syntax "Π" expr "," expr : expr

declare_syntax_cat levels
declare_syntax_cat comb

syntax ".{" term "}" : levels

syntax "K" : comb
syntax "K'" : comb
syntax "S" : comb

syntax "arg" num expr : expr
syntax "ret" num : expr

syntax expr "∘" expr : expr
syntax comb levels : expr
syntax "#(" term ")" : expr
syntax "(" expr* ")" : expr
syntax "Type" term  : expr
syntax "B" : expr
syntax "C" : expr
syntax "K*" : expr
syntax "I" : expr
syntax "Sort" term : expr
syntax expr "∶" expr : expr
syntax expr "→" expr : expr
syntax ident : expr

syntax "SK" expr : term

macro_rules
  | `(SK #($t:term)) => `($t)
  | `(SK $f:expr ∘ $g:expr) => `(SK (B $f:expr $g:expr))
  | `(SK $idt:ident) => `($idt:term)
  | `(SK K.{[$m:term, $n:term]}) => `(Expr.comb (Comb.K $m:term $n:term))
  | `(SK K'.{[$m:term, $n:term]}) => `(Expr.comb (Comb.K' $m:term $n:term))
  | `(SK S.{[$m:term, $n:term, $o:term]}) => `(Expr.comb (Comb.S $m:term $n:term $o:term))
  | `(SK B) => `(Expr.tycomb (TyComb.comp))
  | `(SK C) => `(Expr.tycomb (TyComb.flip))
  | `(SK K*) => `(Expr.tycomb (TyComb.next))
  | `(SK I) => `(Expr.tycomb (TyComb.read))
  | `(SK Sort $m:term) => `(Expr.Srt $m)
  | `(SK Type $n:term) => `(Expr.Srt ($n + 1))
  | `(SK ($e:expr)) => `(SK $e)
  | `(SK ($f:expr $x:expr)) => `(Expr.app (SK $f:expr) (SK $x:expr))
  | `(SK __ ∶ $t:expr) => `(Expr.tyhole (SK $t))
  | `(SK ($f:expr $x:expr $xs:expr*)) => `(SK (($f:expr $x:expr) $xs:expr*))
  | `(SK Π $α:expr, $β:expr) => `(Expr.Pi (SK $α) (SK $β))
  | `(SK $α:expr → $β:expr) => `(SK Π ($α:expr), (K* $β:expr))
  | `(SK arg $n:num $fn:expr) =>
    match n.getNat with
    | .zero => `(SK (B $fn I))
    | .succ n =>
      let n' := Lean.Syntax.mkNatLit n
      `(SK arg $n' (K* $fn))
  | `(SK ret $n:num) =>
    match n.getNat with
    | .zero => `(SK I)
    | .succ n =>
      let n' := Lean.Syntax.mkNatLit n
      `(SK (B K* (ret $n')))

end dsl

namespace Expr

def toFormat : Expr → Format
  | SK Sort m => s!"Sort {m}"
  | SK B => "B"
  | SK C => "C"
  | SK I => "I"
  | SK K* => "K*"
  | SK K'.{[m, n]} => "K'.{" ++ (format [m, n]) ++ "}"
  | SK K.{[m, n]} => "K.{" ++ (format [m, n]) ++ "}"
  | SK S.{[m, n, o]} => "S.{" ++ (format [m, n, o]) ++ "}"
  | SK Π α, β => .paren <| "Π " ++ α.toFormat ++ ", " ++ β.toFormat
  | SK (f x) => .bracket "(" (f.toFormat ++ (.nest 2 <| .line ++ x.toFormat)) ")"
  | SK __ ∶ t => "__ : " ++ t.toFormat

instance : ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨toString ∘ toFormat⟩

end Expr
