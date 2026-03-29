import Mathlib.Data.Nat.Notation
import Batteries.Data.String.Matcher
import Mathlib.Tactic
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

inductive Expr where
  | tyhole : Expr   → Expr
  | Srt    : Level  → Expr
  | comb   : Comb   → Expr
  | app    : Expr   → Expr → Expr
  | App    : Expr
  | compe  : Expr
  | nil    : Expr
  | quot   : Expr
  | flip   : Expr
  | id     : Expr
  | fst    : Expr
  | snd    : Expr
  | curr   : Expr
  | coupe  : Expr
  | dpair  : Expr
  | lense  : Expr
deriving BEq, Repr, Lean.ToExpr, DecidableEq

namespace dsl

declare_syntax_cat expr

declare_syntax_cat levels
declare_syntax_cat comb

syntax ".{" term "}" : levels

syntax "K" : comb
syntax "K'" : comb
syntax "S" : comb

syntax "App" : expr
syntax "(∘)" : expr
syntax expr "∘" expr : expr
syntax comb levels : expr
syntax "#(" term ")" : expr
syntax "(" expr* ")" : expr
syntax "fst" : expr
syntax "quot" : expr
syntax "flip" : expr
syntax "id" : expr
syntax "snd" : expr
syntax "(Λ)" : expr
syntax "{" expr "," expr "}" : expr
syntax "lens" : expr
syntax "Λ" "(" expr ")" : expr
syntax "(" expr "," expr ")" : expr
syntax "pair" : expr
syntax "coup" : expr
syntax "⟨" expr "," expr "⟩" : expr
syntax "nil" : expr
syntax "Type" term  : expr
syntax "Sort" term : expr
syntax expr "∶" expr : expr
syntax expr "→" expr : expr
syntax ident : expr

syntax "SK" expr : term

macro_rules
  | `(SK App) => `(Expr.App)
  | `(SK id) => `(Expr.id)
  | `(SK flip) => `(Expr.flip)
  | `(SK quot) => `(Expr.quot)
  | `(SK pair) => `(Expr.dpair)
  | `(SK lens) => `(Expr.lense)
  | `(SK {$a:expr, $b:expr}) => `(SK (lens $a $b))
  | `(SK ⟨$a:expr, $b:expr⟩) => `(SK (pair $a $b))
  | `(SK coup) => `(Expr.coupe)
  | `(SK ($a:expr, $b:expr)) => `(SK (coup $a $b))
  | `(SK nil) => `(Expr.nil)
  | `(SK fst) => `(Expr.fst)
  | `(SK snd) => `(Expr.snd)
  | `(SK Λ($f:expr)) => `(Expr.app Expr.curr (SK $f))
  | `(SK (Λ)) => `(Expr.curr)
  | `(SK (∘)) => `(Expr.compe)
  | `(SK $f ∘ $g) => `(SK ((∘) $f $g))
  | `(SK #($t:term)) => `($t)
  | `(SK $idt:ident) => `($idt:term)
  | `(SK K.{[$m:term, $n:term]}) => `(Expr.comb (Comb.K $m:term $n:term))
  | `(SK K'.{[$m:term, $n:term]}) => `(Expr.comb (Comb.K' $m:term $n:term))
  | `(SK S.{[$m:term, $n:term, $o:term]}) => `(Expr.comb (Comb.S $m:term $n:term $o:term))
  | `(SK Sort $m:term) => `(Expr.Srt $m)
  | `(SK Type $n:term) => `(Expr.Srt ($n + 1))
  | `(SK ($e:expr)) => `(SK $e)
  | `(SK ($f:expr $x:expr)) => `(Expr.app (SK $f:expr) (SK $x:expr))
  | `(SK __ ∶ $t:expr) => `(Expr.tyhole (SK $t))
  | `(SK ($f:expr $x:expr $xs:expr*)) => `(SK (($f:expr $x:expr) $xs:expr*))

end dsl

namespace Expr

def toFormat (e : Expr) : Format :=
  match e with
  | SK App => "App"
  | SK id => "id"
  | SK dpair => "pair"
  | SK flip => "flip"
  | SK quot => "quot"
  | SK nil => "nil"
  | SK Sort m => s!"Sort {m}"
  | SK f ∘ g => f.toFormat ++ " ∘ " ++ g.toFormat
  | SK (∘) => "(∘)"
  | SK (Λ) => "(Λ)"
  | SK fst => "fst"
  | SK snd => "snd"
  | SK coup => "coup"
  | SK lens => "lens"
  | SK {a, b} => .bracket "{" (a.toFormat ++ "," ++ b.toFormat) "}"
  | SK (a, b) => .paren <| a.toFormat ++ ", " ++ b.toFormat
  | SK ⟨a, b⟩ => .bracket "⟨" (a.toFormat ++ ", " ++ b.toFormat) "⟩"
  | SK Λ(x) => "Λ" ++ (.paren x.toFormat)
  | SK K'.{[m, n]} => "K'.{" ++ (format [m, n]) ++ "}"
  | SK K.{[m, n]} => "K.{" ++ (format [m, n]) ++ "}"
  | SK S.{[m, n, o]} => "S.{" ++ (format [m, n, o]) ++ "}"
  | SK (f x) => .bracket "(" (f.toFormat ++ (.nest 2 <| .line ++ x.toFormat)) ")"
  | SK __ ∶ t => .paren <| "__ ∶ " ++ t.toFormat

instance : ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨toString ∘ toFormat⟩
