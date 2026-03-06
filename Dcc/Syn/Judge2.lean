import Dcc.Syn.Ast2
import Mathlib.Logic.Relation

open Std (Format)
open Std.ToFormat (format)

namespace Expr

inductive red : Expr → Expr → Prop
  | I     : red ⸨(I m) α x⸩ x
  | K     : red ⸨(K m n) α β x y⸩ x
  | K'    : red ⸨(K' m n) α β x y⸩ x
  | S     : red ⸨(S m n o) α β γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | Pi    : red ⸨(Π' α, β) x⸩ (Π' ⸨α x⸩, β) -- nest Π here
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
  | `($α ~> ($β ~> $γ)) => `(Π' (quot $α), $β ~> $γ)
  | `($α ~> $β) => `(Π' (quot $α), (quot $β))

def I.type (m : Level) : Expr :=
  (Π' (quot (Srt m)), Π' (tail Syntax.id), (head (tail Syntax.id)))

def K.type (m n : Level) : Expr :=
   (Π' (quot (Srt m))
  , Π' (Π' (tail Syntax.id), (quot (Srt n)))
  , Π' (head (tail Syntax.id))
  , Π' ($ ((head (tail Syntax.id)), (tail Syntax.id)))
  , (head (head (head (tail Syntax.id)))))

def K'.type (m n : Level) : Expr :=
  (Π' (quot (Srt m))
 , Π' (quot (Srt n))
 , Π' (head (tail Syntax.id))
 , Π' (head (tail Syntax.id))
 , (head (head (head (tail Syntax.id)))))

def S.type (m n o : Level) : Expr :=
  (Π' (quot (Srt m))
  , Π' (Π' (tail Syntax.id), (quot (Srt n)))
  , Π' ($ ((quot (Π')), (head (tail Syntax.id))
      , ($ ((quot (Π')), ($ ((tail Syntax.id), ⸨Syntax.const (tail Syntax.id)⸩)), (quot (Srt o))))))
  , Π' (Π' (head (head (tail Syntax.id)))
      , Π' ($ ((head (tail Syntax.id)), ⸨Syntax.const (tail Syntax.id)⸩))
      , ($ ((tail Syntax.id), ⸨Syntax.const (head (tail Syntax.id))⸩, ⸨Syntax.const (head Syntax.id)⸩)))
  , Π' (Π' ((head (head (head (tail Syntax.id))))), ($ ((head (head (tail Syntax.id))), ⸨Syntax.const (tail Syntax.id)⸩)))
  , Π' ((head (head (head (head (tail Syntax.id)))))), ($ ((head (head (tail Syntax.id))), (tail Syntax.id), ($ ((head (tail Syntax.id)), (tail Syntax.id))))))

def Syntax.type : Expr := Srt 0

def Pi.type : Expr := ((Syntax ~> Syntax) ~> ((Syntax ~> Syntax) ~> (Srt 1)))

namespace Expr

def eval (e : Expr) : Except Format Expr :=
  match e with
  | ⸨(quot e) _x⸩ => pure (quot e)
  | ⸨(I _m) _α x⸩ => (eval x) <|> (pure x)
  | ⸨(K _m _n) _α _β x _y⸩
  | ⸨(K' _m _n) _α _β x _y⸩ => (eval x) <|> (pure x)
  | ⸨(S _m _n _o) _α _β _γ x y z⸩ => pure ⸨(⸨x z⸩.eval.toOption.getD ⸨x z⸩) (⸨y z⸩.eval.toOption.getD ⸨y z⸩)⸩
  | ⸨(Π' α, β) x⸩ => do pure <| (Π' (← ⸨α x⸩.eval), β)
  | ⸨(head fn) (quot ⸨f _x⸩)⸩ => eval ⸨fn (quot f)⸩
  | ⸨(tail fn) (quot ⸨_f x⸩)⸩ => eval ⸨fn (quot x)⸩
  | ⸨$ (f, x) e⸩ => pure ($ ((eval ⸨f e⸩).toOption.getD f, (eval ⸨x e⸩).toOption.getD x))
  | ⸨f x⸩ => (do pure <| ⸨(← f.eval) (← x.eval)⸩) <|> ((·.app x) <$> eval f) <|> (f.app <$> eval x)
  | e => .error <| "stuck: " ++ (format e)

def eval' (e : Expr) : Expr :=
  match e with
  | (quot e') => eval' e'
  | ($ (f, x)) => (eval ⸨(eval' f) (eval' x)⸩).toOption.getD ⸨(eval' f) (eval' x)⸩
  | e => (eval e).toOption.getD e

def eq' (t₁ t₂ in_e : Expr) : Except Format Unit := do
  match eval' t₁, eval' t₂ with
  | (Π' α₁, cod₁), (Π' α₂, cod₂) =>
    let t₁' := Π' (eval' α₁), eval' ⸨cod₁ (quot ⸨in_e (Srt 0)⸩)⸩
    let t₂' := Π' (eval' α₂), eval' ⸨cod₂ (quot ⸨in_e (Srt 0)⸩)⸩
    if t₁' == t₂' then
      .ok ()
    else
      Except.error <| (.text "argument type mismatch. expected")
        ++ (.nest 2 <| Format.line
        ++ (format t₁'))
        ++ (.text ", but found")
        ++ (.nest 2 <| Format.line
        ++ (format t₂'))
  | quot t₁, t₂
  | t₁, quot t₂
  | t₁, t₂ =>
    if eval' t₁ == eval' t₂ then
      pure ()
    else
      .error <| "argument type mismatch. expected" ++ (.nest 2 <| .line ++ (format (eval' t₁)) ++ .line ++ (.paren (format t₁))) ++ ", but found" ++ (.nest 2 <| .line ++ (format (eval' t₂)) ++ .line ++ (.paren (format t₂)))

def infer (e : Expr) : Except Format Expr :=
  let rec do_infer (e : Expr) : Except Format Expr :=
    match e with
    | (I m) => pure <| I.type m
    | (K m n) => pure <| K.type m n
    | (K' m n) => pure <| K'.type m n
    | (S m n o) => pure <| S.type m n o
    | Syntax => pure <| Srt 0
    | (quot _e) => pure <| (Syntax ~> Syntax)
    | ($ (_a, _b)) => pure <| (Syntax ~> Syntax)
    | (Π') => pure <| Pi.type
    | (tail fn)
    | (head fn) => infer fn
    | Srt m => pure <| Srt m.succ
    | ⸨f x⸩ =>
      match (eval ⸨· (quot e)⸩) =<< infer f, infer x with
      | .ok (Π' α, β), .ok α₂ => do
        let _ ← eq' α α₂ x
        eval ⸨β (quot e)⸩
      | _t, .error err => .error s!"argument not well-typed: {err}"
      | t, _ => do .error s!"{(← t)} not a function type"
  match do_infer e with
  | .error err => .error <| "type error in" ++ (.nest 2 <| .line ++ (format e)) ++ .line ++ err
  | .ok e => .ok e

#eval infer ⸨(K' 2 2) (Srt 1) (Srt 1) (Srt 0) (Srt 0)⸩
#eval infer ⸨(K 3 2) (Srt 2) ⸨(I 3) (Srt 2)⸩ (Srt 1) (Srt 0)⸩
#eval eval' ⸨(Expr.head (Expr.tail (Expr.app (Expr.I 1) (Expr.Syntax)))) (Srt 1)⸩

#eval format <| eval' ⸨(Π' ⸨⸨⸨⸨(K' 3 1) (Srt 2)⸩ (Srt 0)⸩ (Srt 1)⸩ ⸨⸨⸨(K' 1 1) Syntax⸩ Syntax⸩ (tail ⸨(I 1) Syntax⸩)⸩⸩, (Srt 1))
    (quot
     ⸨⸨⸨⸨(K' 1 1) (Π' (quot (Srt 1)), (quot (Srt 1)))⸩ (Srt 0)⸩ ⸨⸨⸨(K' 2 2) (Srt 1)⸩ (Srt 1)⸩ (Srt 0)⸩⸩
      (Srt 0)⸩)⸩

def mk_I (α : Expr) (m : Level) : Expr :=
  let α := α
  let y := ⸨(K' 2 m) (Srt 1) α (Srt 0)⸩
  let x := ⸨(K' m 2) α (Srt 1)⸩

  let β := ⸨(K' 3 m) (Srt 2) α (Srt 1)⸩
  let γ := ⸨(K' 1 1) (Srt 1 ~> Srt m) α ⸨(K' m.succ 2) (Srt m) (Srt 1) α⸩⸩

  ⸨(S m 2 m) α β γ x y⸩

#eval infer ⸨(K' 3 1) (Srt 2) (Srt 0) (Srt 1)⸩
#eval infer (Π' (quot (Srt 2)), (quot (Srt 1)))
#eval infer (mk_I (Srt 0) 1)
#eval eval' (Expr.app
  (Expr.head (Expr.head (Expr.head (Expr.tail (Expr.app (Expr.I 1) (Expr.Syntax))))))
  (Expr.quot
    (Expr.app (Expr.app (Expr.app (Expr.app (Expr.K' 3 1) (Expr.Srt 2)) (Expr.Srt 0)) (Expr.Srt 1)) (Expr.Srt 0))))
#eval infer (Π' (quot (Srt 2)), (quot (Srt 1)))
#eval infer ⸨⸨⸨(K' 2 1) (Π' (quot (Srt 2)), (quot (Srt 1)))⸩ (Srt 0)⸩ ⸨⸨⸨(K' 2 3) (Srt 1)⸩ (Srt 2)⸩ (Srt 0)⸩⸩
#eval infer (Srt 1 ~> Srt 2)

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

