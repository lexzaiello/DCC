import Dcc.Syn.Ast2
import Mathlib.Logic.Relation

namespace Expr

inductive red : Expr → Expr → Prop
  | I     : red ⸨(I m) α x⸩ x
  | K     : red ⸨(K m n) α β x y⸩ x
  | K'    : red ⸨(K' m n) α β x y⸩ x
  | S     : red ⸨(S m n o) α β γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | Pi    : red (Π' α, ⸨β x⸩) (Π' ⸨α x⸩, ⸨β x⸩)
  /-
    Quotation manipulation
  -/
  | head  : red ⸨head fn (quot ⸨f x⸩)⸩ ⸨fn (quot f)⸩
  -- Not sure about this one: want to be able to partially apply nested tail
  | tail  : red ⸨tail fn (quot ⸨f x⸩)⸩ ⸨fn (quot x)⸩
  | app'  : red ⸨$ f x (quot e)⸩ ⸨$ ⸨f (quot e)⸩ ⸨x (quot e)⸩⸩
  | left  : red f f' → red ⸨f x⸩ ⸨f' x⸩
  | right : red x x' → red ⸨f x⸩ ⸨f x'⸩

def eq : Expr → Expr → Prop := Relation.EqvGen red

instance instSetoid : Setoid Expr where
  r := eq
  iseqv := Relation.EqvGen.is_equivalence red

syntax term "~>" term : term
macro_rules
  | `($α ~> $β) => `(Π' $α, $β)

def I.type (m : Level) : Expr :=
  (Π' (quot (Srt m)), Π' ⸨tail Syntax.id⸩, ⸨head ⸨tail Syntax.id⸩⸩)

def K.type (m n : Level) : Expr :=
   (Π' (quot (Srt m))
  , Π' (⸨tail Syntax.id⸩ ~> (quot (Srt n)))
  , Π' ⸨head ⸨tail Syntax.id⸩⸩
  , Π' ⸨$ ⸨⸨head ⸨tail Syntax.id⸩⸩ ⸨tail Syntax.id⸩⸩⸩
  , ⸨head ⸨head ⸨tail Syntax.id⸩⸩⸩)

inductive judge : Expr → Expr → Prop
  | sort : judge (Srt m.succ) (Srt m)
  | app  : judge ⸨Π' (quot α) cod⸩ f
    → judge α x
    → judge ⸨cod x⸩ ⸨f x⸩
  | conv : judge t₁ x
    → t₁ ≈ t₂
    → judge t₂ x

end Expr
