import Mathlib.Data.Nat.Notation
open Std (ToFormat Format)
open Std.ToFormat (format)

abbrev Level := ℕ

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
  | tyhole : Expr   → Expr
  | tycomb : TyComb → Expr
  | Pi     : Expr   → Expr → Expr
  | Srt    : Level  → Expr
  | comb   : Comb   → Expr
  | app    : Expr   → Expr → Expr
deriving BEq, Repr, Lean.ToExpr, DecidableEq

namespace Expr

syntax:max "#" num : term

syntax term "∘'" term : term
syntax "K" ".{" term "}" : term
syntax "K'" ".{" term "}" : term
syntax "S" ".{" term "}" : term
syntax "B" : term
syntax "C" : term
syntax "K*" : term
syntax "I" : term
syntax "Π'" term "," term : term
syntax "⸨" term* "⸩" : term
syntax "Ty" term  : term
syntax "Srt" term : term
syntax "__" "∶" term : term
syntax term "~>" term : term

macro_rules
  | `(B) => `(Expr.tycomb (TyComb.comp))
  | `(C) => `(Expr.tycomb (TyComb.flip))
  | `(K*) => `(Expr.tycomb (TyComb.next))
  | `(I) => `(Expr.tycomb (TyComb.read))
  | `(Π' $α:term, $β:term) => `(Expr.Pi $α $β)
  | `(K.{[$m, $n]}) => `(Expr.comb (Comb.K $m $n))
  | `(K'.{[$m, $n]}) => `(Expr.comb (Comb.K' $m $n))
  | `(S.{[$m, $n, $o]}) => `(Expr.comb (Comb.S $m $n $o))
  | `(Srt $m) => `(Expr.Srt $m)
  | `(Ty $n) => `(Expr.Srt ($n + 1))
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f:term $x:term)
  | `(__ ∶ $t:term) => `(Expr.tyhole $t)
  | `(⸨$f:term $x:term $xs:term*⸩) => `(⸨⸨$f:term $x:term⸩ $xs:term*⸩)
  | `(#$n:num) =>
    match n.getNat with
    | 0 => `(I)
    | .succ n =>
      let n' := Lean.Syntax.mkNatLit n
      `(⸨B ⸨B K* (#$n':num)⸩⸩)
  | `($α:term ~> $β:term) => `(Π' $α, ⸨K* $β⸩)

#eval ⸨# 0 I⸩

def toFormat : Expr → Format
  | Srt m => s!"(Srt {m})"
  | B => "B"
  | C => "C"
  | I => "I"
  | K* => "K*"
  | K'.{[m, n]} => "K'.{" ++ (format [m, n]) ++ "}"
  | K.{[m, n]} => "K.{" ++ (format [m, n]) ++ "}"
  | S.{[m, n, o]} => "S.{" ++ (format [m, n, o]) ++ "}"
  | Π' α, β => .paren <| "Π'" ++ (.nest 2 <| (.paren <| α.toFormat) ++ ", " ++ β.toFormat)
  | ⸨f x⸩ => .bracket "⸨" (f.toFormat ++ (.nest 2 <| .line ++ x.toFormat)) "⸩"
  | __ ∶ t => "__ : " ++ t.toFormat

instance : ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨toString ∘ toFormat⟩

macro_rules
  | `($f:term ∘' $g:term) => `(⸨B $f $g⸩)

abbrev assert_n (n : ℕ) (fn : Expr) : Expr :=
  (List.replicate n K*).foldr (fun e acc => ⸨B e acc⸩) fn

end Expr
