import Mathlib.Data.Nat.Notation
import Batteries.Data.String.Matcher
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
  | next   : TyComb
  | read   : TyComb
  | comp   : TyComb
  | flip   : TyComb
deriving BEq, Repr, Lean.ToExpr, DecidableEq

inductive Expr where
  | tyhole : Expr   → Expr -- __ : τ. May not be necessary due to inference rule for BCKI. Vestigial.
  | tycomb : TyComb → Expr
  | cons   : Expr
  | Srt    : Level  → Expr
  | comb   : Comb   → Expr
  | app    : Expr   → Expr → Expr
deriving BEq, Repr, Lean.ToExpr, DecidableEq

namespace dsl

declare_syntax_cat expr

declare_syntax_cat levels
declare_syntax_cat comb

syntax "cons" : expr

syntax "⟨" expr,* "⟩" : expr

syntax ".{" term "}" : levels

syntax "K" : comb
syntax "K'" : comb
syntax "S" : comb

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
syntax "arg" num expr : expr
syntax "ret" num : expr

syntax "SK" expr : term

macro_rules
  | `(SK cons) => `(Expr.cons)
  | `(SK ⟨$a:expr, $xs:expr,*⟩) => `(SK (cons $a:expr ⟨$xs:expr,*⟩))
  | `(SK ⟨$e:expr⟩) => `(SK $e)
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
  | SK cons => "cons"
  | SK B => "B"
  | SK C => "C"
  | SK I => "I"
  | SK K* => "K*"
  | SK K'.{[m, n]} => "K'.{" ++ (format [m, n]) ++ "}"
  | SK K.{[m, n]} => "K.{" ++ (format [m, n]) ++ "}"
  | SK S.{[m, n, o]} => "S.{" ++ (format [m, n, o]) ++ "}"
  | SK (f x) => .bracket "(" (f.toFormat ++ (.nest 2 <| .line ++ x.toFormat)) ")"
  | SK __ ∶ t => "__ : " ++ t.toFormat

instance : ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨toString ∘ toFormat⟩

/-
init Γ

I, each argument we add we do

apply Γ to head.

each argument we add, we do

(B (C I arg) Γ) head


-/
