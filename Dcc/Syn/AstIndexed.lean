import Mathlib.Data.Nat.Notation
open Std (ToFormat Format)

abbrev Level := ℕ

inductive Expr where
  | Srt    : Level → Expr
  | Syntax : Expr  → Expr -- (quot (e : t)) : Syntax t
  | Pi     : Expr  → Expr  → Expr -- Pi (α : Syntax (Sort m)) (β : Sort n) : (Sort n)
  | K'     : Level → Level → Expr
  | K      : Level → Level → Expr
  | S      : Level → Level → Level → Expr
  | I      : Level → Expr
  | hole   :  Expr -- I (Syntax _) (quot (f x))
  -- head fn (quot (f x)) = fn (quot f)
  | head   : Expr → Expr
  -- tail fn (quot (f x)) = fn (quot x)
  | tail   : Expr → Expr
  | unquot : Expr → Expr -- (unquot α ((quot e) : Syntax α)) = e
  | quot   : Expr → Expr -- (quot (e : α)) : Syntax α
  | app'   : Expr → Expr → Expr -- quotation application. ($ f x) (quot e) = ((f e) (x e))
  | app    : Expr → Expr → Expr
deriving BEq, Repr, DecidableEq

open Expr

syntax num term : term

syntax "$" "(" term,* ")" : term
syntax "Π'" term "," term : term
syntax "(Π')" : term
syntax "⸨" term* "⸩" : term
syntax "Ty" term : term
syntax "?_" : term

macro_rules
  | `(Ty $n) => `(Expr.sort ($n + 1))
  | `(?_) => `(Expr.hole)
  | `($n:num $fn:term) =>
    match n.getNat with
    | 0 => `(Expr.head $fn)
    | .succ n =>
      let n' := Lean.Syntax.mkNatLit n
      `(Expr.tail ($n':num $fn))
  | `($ ($f:term, $x:term)) => `((Expr.app' $f $x))
  | `($ ($f:term, $x:term, $xs:term,*)) => `($ ($ ($f, $x), $xs,*))
  | `(Π' $α, $β) => `(Expr.Pi $α $β)
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f:term $x:term)
  | `(⸨$f:term $x:term $xs:term*⸩) => `(⸨⸨$f:term $x:term⸩ $xs:term*⸩)

example :  ⸨(Srt 0) (Srt 1) (Srt 2)⸩ = Expr.app (Expr.app (Expr.Srt 0) (Expr.Srt 1)) (Expr.Srt 2) := rfl

-- Syntax id
abbrev Syntax.id (α : Expr := ?_) : Expr := ⸨(I 1) (Syntax α)⸩

abbrev Syntax.const (α : Expr := ?_) (β : Expr := ?_) : Expr := ⸨(K' 1 1) (Syntax α) (Syntax β)⸩

def Expr.toFormat : Expr → Format
  | Srt m => s!"(Srt {m})"
  | quot e => .paren <| "quot" ++ (.nest 2 <| .line ++ e.toFormat)
  | K' m n => s!"(K' {m} {n})"
  | K m n => s!"(K' {m} {n})"
  | S m n o => s!"(S {m} {n} {o})"
  | app' a b => "$ " ++ (.paren <| .nest 2 <| a.toFormat ++ .line ++ b.toFormat)
  | Π' α, β => .paren <| "Π' " ++ α.toFormat ++ "," ++ .line ++ β.toFormat
  | I m => s!"(I {m})"
  | Syntax α => .paren <| "Syntax " ++ α.toFormat
  | unquot e => .paren <| "unquot " ++ e.toFormat
  | hole => "?_"
  | head fn => .paren <| "head" ++ (.nest 2 <| .line ++ fn.toFormat)
  | tail fn => .paren <| "tail" ++ (.nest 2 <| .line ++ fn.toFormat)
  | .app f x => .bracket "⸨" (f.toFormat ++ (.nest 2 <| .line ++ x.toFormat)) "⸩"

instance : ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨toString ∘ toFormat⟩
