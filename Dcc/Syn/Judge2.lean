import Dcc.Syn.Ast2
import Mathlib.Logic.Relation

namespace Expr

inductive red : Expr → Expr → Prop
  | I     : red ⸨(I m) α x⸩ x
  | K     : red ⸨(K m n) α β x y⸩ x
  | K'    : red ⸨(K' m n) α β x y⸩ x
  | S     : red ⸨(S m n o) α β γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  /-
    Quotation manipulation
  -/
  | head  : red ⸨head fn ⸨quot ⸨f x⸩⸩⸩ ⸨fn ⸨quot f⸩⸩
  | tail  : red ⸨tail fn ⸨quot ⸨f x⸩⸩⸩ ⸨fn ⸨quot x⸩⸩
  | app'  : red ⸨$ f x ⸨quot e⸩⸩ ⸨$ ⸨f ⸨quot e⸩⸩ ⸨x ⸨quot e⸩⸩⸩
  | left  : red f f' → red ⸨f x⸩ ⸨f' x⸩
  | right : red x x' → red ⸨f x⸩ ⸨f x'⸩

def eq : Expr → Expr → Prop := Relation.EqvGen red

instance instSetoid : Setoid Expr where
  r := eq
  iseqv := Relation.EqvGen.is_equivalence red

def I.type (m : Level) : Expr :=
  ⸨

inductive judge : Expr → Expr → Prop
  | sort : judge (Srt m.succ) (Srt m)
  | 
  | conv : judge t₁ x
    → t₁ ≈ t₂
    → judge t₂ x

end Expr
