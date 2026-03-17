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

declare_syntax_cat debruijn
declare_syntax_cat expr

syntax "{" num+ "}" : debruijn
syntax "(" expr ")" : debruijn
syntax "Π" debruijn "," debruijn : debruijn
syntax "Π" expr "," debruijn : debruijn
syntax "Π" expr "," expr : debruijn
syntax "Π" debruijn "," expr : debruijn

syntax "d⟪" debruijn "⟫" : term

declare_syntax_cat levels
declare_syntax_cat comb

syntax ".{" term "}" : levels

syntax "K" : comb
syntax "K'" : comb
syntax "S" : comb

syntax expr "∘" expr : expr
syntax comb levels : expr
syntax "(" expr* ")" : expr
syntax "Ty" term  : expr
syntax "B" : expr
syntax "C" : expr
syntax "K*" : expr
syntax "I" : expr
syntax "Srt" term : expr
syntax "__" "∶" expr : expr
syntax expr "~>" expr : expr
syntax ident : expr

syntax debruijn : expr

syntax "SK" expr : term

macro_rules
  | `(SK $f:expr ∘ $g:expr) => `(SK (B $f:expr $g:expr))
  | `(SK $idt:ident) => `($idt:term)
  | `(SK K.{[$m:term, $n:term]}) => `(Expr.comb (Comb.K $m:term $n:term))
  | `(SK K'.{[$m:term, $n:term]}) => `(Expr.comb (Comb.K' $m:term $n:term))
  | `(SK S.{[$m:term, $n:term, $o:term]}) => `(Expr.comb (Comb.S $m:term $n:term $o:term))
  | `(SK B) => `(Expr.tycomb (TyComb.comp))
  | `(SK C) => `(Expr.tycomb (TyComb.flip))
  | `(SK K*) => `(Expr.tycomb (TyComb.next))
  | `(SK I) => `(Expr.tycomb (TyComb.read))
  | `(SK Srt $m:term) => `(Expr.Srt $m)
  | `(SK Ty $n:term) => `(Expr.Srt ($n + 1))
  | `(SK $d:debruijn) => `(d⟪$d:debruijn⟫)
  | `(SK ($e:expr)) => `(SK $e)
  | `(SK ($f:expr $x:expr)) => `(Expr.app (SK $f:expr) (SK $x:expr))
  | `(SK __ ∶ $t:expr) => `(Expr.tyhole (SK $t))
  | `(SK ($f:expr $x:expr $xs:expr*)) => `(SK (($f:expr $x:expr) $xs:expr*))
  | `(d⟪($t:expr)⟫) => `(SK $t:expr)
  | `(d⟪{$n:num}⟫) =>
    match n.getNat with
    | 0 => `(SK I)
    | .succ n =>
      let n' := Lean.Syntax.mkNatLit n
      `(SK (B K* {$n':num}))
  | `(d⟪{$n:num $nxs:num*}⟫) =>
    let nxs' := nxs.map (Lean.Syntax.mkNatLit ∘ (· - 1) ∘ Lean.TSyntax.getNat)
    `(SK ((B ({$nxs':num*})) ({$n:num})))
  | `(d⟪Π $α:debruijn, $β:debruijn⟫) => `(Expr.Pi d⟪$α⟫ d⟪$β⟫)
  | `(d⟪Π $α:expr, $β:debruijn⟫) => `(Expr.Pi (SK $α) d⟪$β⟫)
  | `(d⟪Π $α:expr, $β:expr⟫) => `(Expr.Pi (SK $α) (SK $β))
  | `(d⟪Π $α:debruijn, $β:expr⟫) => `(Expr.Pi (d⟪$α⟫) (SK $β))
  | `(SK $α:expr ~> $β:expr) => `(d⟪Π ($α:expr), (K* $β:expr)⟫)

#eval SK ({0} I)

def toFormat : Expr → Format
  | SK Srt m => s!"(Srt {m})"
  | SK B => "B"
  | SK C => "C"
  | SK I => "I"
  | SK K* => "K*"
  | SK K'.{[m, n]} => "K'.{" ++ (format [m, n]) ++ "}"
  | SK K.{[m, n]} => "K.{" ++ (format [m, n]) ++ "}"
  | SK S.{[m, n, o]} => "S.{" ++ (format [m, n, o]) ++ "}"
  | SK Π α, β => .paren <| "Π" ++ (.nest 2 <| (.paren <| α.toFormat) ++ ", " ++ β.toFormat)
  | SK (f x) => .bracket "(" (f.toFormat ++ (.nest 2 <| .line ++ x.toFormat)) ")"
  | SK __ ∶ t => "__ : " ++ t.toFormat

instance : ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨toString ∘ toFormat⟩

abbrev assert_n (n : ℕ) (fn : Expr) : Expr :=
  (List.replicate n (SK K*)).foldr (fun e acc => (SK (B e acc))) fn

end Expr
