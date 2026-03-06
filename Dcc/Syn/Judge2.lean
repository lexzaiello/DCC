import Dcc.Syn.Ast2
import Mathlib.Logic.Relation

namespace Expr

inductive red : Expr → Expr → Prop
  | I     : red ⸨(I m) α x⸩ x
  | K     : red ⸨(K m n) α β x y⸩ x
  | K'    : red ⸨(K' m n) α β x y⸩ x
  | S     : red ⸨(S m n o) α β γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | Pi    : red ⸨(Π' α, β) x⸩ (Π' ⸨α x⸩, ⸨β x⸩)
  /-
    Quotation manipulation
  -/
  | head  : red ⸨fn (quot f)⸩ f'
    → red ⸨(head fn) (quot ⸨f x⸩)⸩ f'
  -- Not sure about this one: want to be able to partially apply nested tail
  | tail  : red ⸨fn (quot x)⸩ x'
    → red ⸨(tail fn) (quot ⸨f x⸩)⸩ x'
  | app'  : red ⸨$ (f, x) e⸩ ($ (⸨f e⸩, ⸨x e⸩))
  | left  : red f f' → red ⸨f x⸩ ⸨f' x⸩
  | right : red x x' → red ⸨f x⸩ ⸨f x'⸩

def eq : Expr → Expr → Prop := Relation.EqvGen red

instance instSetoid : Setoid Expr where
  r := eq
  iseqv := Relation.EqvGen.is_equivalence red

end Expr

open Expr

syntax term "~>" term : term
macro_rules
  | `($α ~> $β) => `(Π' (quot $α), (quot $β))

def I.type (m : Level) : Expr :=
  (Π' (quot (Srt m)), Π' (tail Syntax.id), (head (tail Syntax.id)))

def K.type (m n : Level) : Expr :=
   (Π' (quot (Srt m))
  , Π' (Π' (tail Syntax.id), (quot (Srt n)))
  , Π' (head (tail Syntax.id))
  , Π' ($ ((head (tail Syntax.id)), (tail Syntax.id)))
  , (head (head (tail Syntax.id))))

def K'.type (m n : Level) : Expr :=
  (Π' (quot (Srt m))
 , Π' (quot (Srt n))
 , Π' (head (tail Syntax.id))
 , Π' (head (head (tail Syntax.id)))
 , (head (head (head (tail Syntax.id)))))

def S.type (m n o : Level) : Expr :=
  (Π' (quot (Srt m))
  , Π' (Π' (tail Syntax.id), (quot (Srt n)))
  , Π' (Π' (head (tail Syntax.id))
      , Π' ($ ((tail Syntax.id), ⸨Syntax.const (tail Syntax.id)⸩))
      , (quot (Srt o)))
  , Π' (Π' (head (head (tail Syntax.id)))
      , Π' ($ ((head (tail Syntax.id)), ⸨Syntax.const (tail Syntax.id)⸩))
      , ($ ((tail Syntax.id), ⸨Syntax.const (head (tail Syntax.id))⸩, ⸨Syntax.const (head Syntax.id)⸩)))
  , Π' (Π' ((head (head (head (tail Syntax.id))))), ($ ((head (head (tail Syntax.id))), ⸨Syntax.const (tail Syntax.id)⸩)))
  , Π' ((head (head (head (head (tail Syntax.id)))))), ($ ((head (head (tail Syntax.id))), (tail Syntax.id), ($ ((head (tail Syntax.id)), (tail Syntax.id))))))

def Syntax.type : Expr := Srt 0

def Pi.type : Expr := ((Syntax ~> Syntax) ~> ((Syntax ~> Syntax) ~> (Srt 1)))

namespace Expr

def eval (e : Expr) : Option Expr :=
  match e with
  | ⸨(I _m) _α x⸩ => (eval x).getD x
  | ⸨(K _m _n) _α _β x _y⸩
  | ⸨(K' _m _n) _α _β x _y⸩ => eval x
  | ⸨(S _m _n _o) _α _β _γ x y z⸩ => pure ⸨(⸨x z⸩.eval.getD ⸨x z⸩) (⸨y z⸩.eval.getD ⸨y z⸩)⸩
  | ⸨(Π' α, β) x⸩ => pure (Π' ((eval ⸨α x⸩).getD α), ((eval ⸨β x⸩).getD β))
  | ⸨(head fn) (quot ⸨f _x⸩)⸩ => eval ⸨fn (quot f)⸩
  | ⸨(tail fn) (quot ⸨_f x⸩)⸩ => eval ⸨fn (quot x)⸩
  | ⸨$ (f, x) e⸩ => pure ($ ((eval ⸨f e⸩).getD ⸨f e⸩, (eval ⸨x e⸩).getD ⸨x e⸩))
  | ⸨f x⸩ => (do pure <| ⸨(← f.eval) (← x.eval)⸩) <|> ((·.app x) <$> eval f) <|> (f.app <$> eval x)
  | _ => .none

def eval' (e : Expr) : Expr :=
  match e with
  | (quot e) => (eval' e)
  | ($ (f, x)) => (eval ⸨f.eval' x.eval'⸩).getD ⸨f.eval' x.eval'⸩
  | e => e.eval.getD e

def infer (e : Expr) : Except String Expr :=
  match e with
  | (I m) => pure <| I.type m
  | (K m n) => pure <| K.type m n
  | (K' m n) => pure <| K'.type m n
  | (S m n o) => pure <| S.type m n o
  | Syntax => pure <| Srt 0
  | (quot _e) => pure <| Syntax
  | ($) => pure <| (Syntax ~> Syntax) ~> ((Syntax ~> Syntax) ~> (Syntax ~> Syntax))
  | (Π') => pure <| Pi.type
  | (tail fn)
  | (head fn) => infer fn
  | Srt m => pure <| Srt m.succ
  | ⸨f x⸩ => match (eval' ⸨· (quot ⸨f x⸩)⸩) <$> infer f, eval' <$> infer x with
    | .ok (Π' α, β), .ok α₂ =>
      let α' := eval' α
      if α' == α₂ then
        return β
      else
        .error s!"argument type mismatch. expected {repr α'}, but found {repr α₂}"
    | t, _ => .error s!"{repr t} is not a function type"

#eval infer ⸨(K' 2 2) (Srt 1) (Srt 1) (Srt 0) (Srt 0)⸩
#eval infer ⸨(K 3 2) (Srt 2) ⸨(I 3) (Srt 2)⸩ (Srt 1) (Srt 0)⸩
#eval eval' ⸨(Expr.head (Expr.tail (Expr.app (Expr.I 1) (Expr.Syntax)))) (Srt 1)⸩

end Expr

inductive judge : Expr → Expr → Prop
  | I    : judge (I.type m) (I m)
  | S    : judge (S.type m n o) (S m n o)
  | K    : judge (K.type m n) (K m n)
  | K'   : judge (K'.type m n) (K m n)
  | sort : judge (Srt m.succ) (Srt m)
  | app  : judge (Π' (quot α), cod) f
    → judge α x
    → judge ⸨cod x⸩ ⸨f x⸩
  | conv : judge t₁ x
    → t₁ ≈ t₂
    → judge t₂ x

