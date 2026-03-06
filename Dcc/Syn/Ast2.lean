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
  | id     : Expr
  -- head fn (quot (f x)) = fn (quot f)
  | head   : Expr
  -- tail fn (quot (f x)) = fn (quot x)
  | tail   : Expr
  | app'   : Expr -- quotation application. ($ f x) (quot e) = ($ (f e) (x e))
  | app    : Expr → Expr → Expr

open Expr

notation "$" => Expr.app'

syntax "⸨" term* "⸩" : term
macro_rules
  | `(⸨$f:term $x:term $xs:term*⸩) => `(⸨(Expr.app $f $x) $xs*⸩)
  | `(⸨$e:term⸩) => `($e)

example :  ⸨(Srt 0) (Srt 1) (Srt 2)⸩ = Expr.app (Expr.app (Expr.Srt 0) (Expr.Srt 1)) (Expr.Srt 2) := rfl
