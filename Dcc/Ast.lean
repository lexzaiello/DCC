import Mathlib.Data.Nat.Notation
open Std (ToFormat Format)
open Std.ToFormat (format)

abbrev Level := ℕ

inductive Comb where
  | K'     : Level → Level → Comb
  | K      : Level → Level → Comb
  | S      : Level → Level → Level → Comb
  | next   : Comb
  | read   : Comb
  | app'   : Comb
deriving BEq, Repr, Lean.ToExpr, DecidableEq

inductive Expr where
  | Pi     : Expr → Expr → Expr
  | Srt    : Level → Expr
  | comb   : Comb  → Expr
  | app    : Expr  → Expr → Expr
deriving BEq, Repr, Lean.ToExpr, DecidableEq

namespace Expr

syntax num term : term

syntax term "∘'" term : term
syntax "K" ".{" term "}" : term
syntax "K'" ".{" term "}" : term
syntax "S" ".{" term "}" : term
syntax "Π'" term "," term : term
syntax "next" : term
syntax "read" : term
syntax "$" : term
syntax "${" term "}" : term
syntax "⸨" term* "⸩" : term
syntax "Ty" term  : term
syntax "Srt" term : term
syntax "_?" : term
syntax term "~>" term : term

macro_rules
  | `(Π' $α:term, $β:term) => `(Expr.Pi $α $β)
  | `(K.{[$m, $n]}) => `(Expr.comb (Comb.K $m $n))
  | `(K'.{[$m, $n]}) => `(Expr.comb (Comb.K' $m $n))
  | `(S.{[$m, $n, $o]}) => `(Expr.comb (Comb.S $m $n $o))
  | `(next) => `(Expr.comb Comb.next)
  | `(read) => `(Expr.comb Comb.read)
  | `($) => `(Expr.comb Comb.app')
  | `(Srt $m) => `(Expr.Srt $m)
  | `(Ty $n) => `(Expr.Srt ($n + 1))
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f:term $x:term)
  | `(⸨$f:term $x:term $xs:term*⸩) => `(⸨⸨$f:term $x:term⸩ $xs:term*⸩)
  | `($n:num $fn:term) =>
    match n.getNat with
    | 0 => `($fn:term)
    | .succ n =>
      let n' := Lean.Syntax.mkNatLit n
      `(⸨next ($n':num $fn)⸩)
  | `($α:term ~> $β:term) => `(Π' $α, ⸨next $β⸩)

def toFormat : Expr → Format
  | Srt m => s!"(Srt {m})"
  | K'.{[m, n]} => "K'.{" ++ (format [m, n]) ++ "}"
  | K.{[m, n]} => "K.{" ++ (format [m, n]) ++ "}"
  | S.{[m, n, o]} => "S.{" ++ (format [m, n, o]) ++ "}"
  | Π' α, β => .paren <| "Π'" ++ (.nest 2 <| (.paren <| α.toFormat) ++ ", " ++ β.toFormat)
  | ⸨f x⸩ => .bracket "⸨" (f.toFormat ++ (.nest 2 <| .line ++ x.toFormat)) "⸩"
  | $ => "$"
  | next => "next"
  | read => "read"

instance : ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨toString ∘ toFormat⟩

abbrev comp (f g : Expr) : Expr :=
  ⸨$ read ⸨next f⸩ g⸩

macro_rules
  | `($f:term ∘' $g:term) => `(comp $f $g)

abbrev assert_n (n : ℕ) (fn : Expr) : Expr :=
  (List.replicate n next).foldr (fun e acc => (e ∘' acc)) fn

end Expr
