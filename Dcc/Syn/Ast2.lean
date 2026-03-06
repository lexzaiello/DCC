import Mathlib.Data.Nat.Notation
open Std (ToFormat Format)

abbrev Level := ℕ

inductive Expr where
  | Srt    : Level → Expr
  | Syntax : Expr
  | K'     : Level → Level → Expr
  | K      : Level → Level → Expr
  | S      : Level → Level → Level → Expr
  | Pi     : Expr
  | I      : Level → Expr
  -- head fn (quot (f x)) = fn (quot f)
  | head   : Expr → Expr
  -- tail fn (quot (f x)) = fn (quot x)
  | tail   : Expr → Expr
  | quot   : Expr → Expr
  | app'   : Expr → Expr → Expr -- quotation application. ($ f x) (quot e) = ($ (f e) (x e))
  | app    : Expr → Expr → Expr
deriving BEq, Repr, DecidableEq

open Expr

syntax num term : term

syntax "$" "(" term,* ")" : term
syntax "Π'" term "," term : term
syntax "(Π')" : term
syntax "⸨" term* "⸩" : term
syntax "Ty" term : term

macro_rules
  | `(Ty $n) => `(Expr.sort ($n + 1))
  | `($n:num $fn:term) =>
    match n.getNat with
    | 0 => `(Expr.head $fn)
    | .succ n =>
      let n' := Lean.Syntax.mkNatLit n
      `(Expr.tail ($n':num $fn))
  | `($ ($f:term, $x:term)) => `((Expr.app' $f $x))
  | `($ ($f:term, $x:term, $xs:term,*)) => `($ ($ ($f, $x), $xs,*))
  | `((Π')) => `(Expr.Pi)
  | `(Π' $α, $β) => `(⸨(Π') $α $β⸩)
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f:term $x:term)
  | `(⸨$f:term $x:term $xs:term*⸩) => `(⸨⸨$f:term $x:term⸩ $xs:term*⸩)

example :  ⸨(Srt 0) (Srt 1) (Srt 2)⸩ = Expr.app (Expr.app (Expr.Srt 0) (Expr.Srt 1)) (Expr.Srt 2) := rfl

-- Syntax id
abbrev Syntax.id : Expr := ⸨(I 1) Syntax⸩

abbrev Syntax.const : Expr := ⸨(K' 1 1) Syntax Syntax⸩

def Expr.toFormat : Expr → Format
  | Srt m => s!"(Srt {m})"
  | quot e => .paren <| "quot" ++ (.nest 2 <| .line ++ e.toFormat)
  | K' m n => s!"(K' {m} {n})"
  | K m n => s!"(K' {m} {n})"
  | S m n o => s!"(S {m} {n} {o})"
  | app' a b => "$ " ++ (.paren <| .nest 2 <| a.toFormat ++ .line ++ b.toFormat)
  | Π' α, β => .paren <| "Π' " ++ α.toFormat ++ "," ++ .line ++ β.toFormat
  | Pi => "Π'"
  | I m => s!"(I {m})"
  | Syntax => "Syntax"
  | head fn => .paren <| "head" ++ (.nest 2 <| .line ++ fn.toFormat)
  | tail fn => .paren <| "tail" ++ (.nest 2 <| .line ++ fn.toFormat)
  | .app f x => .bracket "⸨" (f.toFormat ++ (.nest 2 <| .line ++ x.toFormat)) "⸩"

instance : ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨toString ∘ toFormat⟩
