import Mathlib.Data.Nat.Notation

abbrev Level := ℕ

inductive Expr where
  | Srt    : Level → Expr
  | Syntax : Expr
  | K'     : Level → Level → Expr
  | K      : Level → Level → Expr
  | S      : Level → Level → Level → Expr
  | Pi     : Expr
  -- quotation identity. id (quot e) = (quot e)
  | I      : Level → Expr
  -- head fn (quot (f x)) = fn (quot f)
  | head   : Expr
  -- tail fn (quot (f x)) = fn (quot x)
  | tail   : Expr
  | app'   : Expr -- quotation application. ($ f x) (quot e) = ($ (f e) (x e))
  | quot   : Expr → Expr
  | app    : Expr → Expr → Expr

open Expr

syntax "$" "(" term,* ")" : term
syntax "($)"              : term
syntax "Π'" term "," term : term
syntax "(Π')" : term
syntax "⸨" term* "⸩" : term
macro_rules
  | `($ ($f:term, $x:term)) => `(⸨($) $f $x⸩)
  | `($ ($f:term, $x:term, $xs:term,*)) => `($ (($ ($f, $x)), $xs,*))
  | `(($)) => `(Expr.app')
  | `((Π')) => `(Expr.Pi)
  | `(Π' $α, $β) => `(⸨(Π') $α $β⸩)
  | `(⸨$f:term $x:term $xs:term*⸩) => `(⸨(Expr.app $f $x) $xs*⸩)
  | `(⸨$e:term⸩) => `($e)

example :  ⸨(Srt 0) (Srt 1) (Srt 2)⸩ = Expr.app (Expr.app (Expr.Srt 0) (Expr.Srt 1)) (Expr.Srt 2) := rfl

-- Syntax id
abbrev Syntax.id : Expr := ⸨(I 1) Syntax⸩

abbrev Syntax.const : Expr := ⸨(K' 1 1) Syntax Syntax⸩
