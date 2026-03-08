import Mathlib.Data.Nat.Notation
open Std (ToFormat Format)
open Std.ToFormat (format)

abbrev Level := ℕ

/-
Purpose of syntax identification is so that we can detect the universe levels of Pi.
we can just add an explicit universe argument to Pi, remove syntax identification.

unquot should not be a combinator, I think. It feels quite unsafe.
Come to think of it, what is the purpose of quotation?
Quotation is totally unnecessary.
But then the question is how do you type-check ∀ / Π?

the argument to Π itself is the type-check.

- do not include function f in quotation.

- syntax may not be necessary.

- we might be able to do debruijn combinators without a context list.

each applied argument to the combinator just decrements it until it hits zero.
then it accepts it.

(next (next (next read))) a = (next (next read)) b

No quotation nonsense.

assert x y = x

This is fine because Π type-checks itself.

What about substitution?
Assume α has already been substituted?

but what about type-checking next?
Should not have to type-check it. Π will handle it.
-/

inductive Expr where
  | Srt    : Level → Expr
  | Pi     : Expr  → Expr  → Expr -- Pi (α : Syntax (Sort m)) (β : Sort n) : (Sort n)
  | K'     : Level → Level → Expr
  | K      : Level → Level → Expr
  | S      : Level → Level → Level → Expr
  | I      : Level → Expr
  | next   : Expr
  | read   : Expr
  | assert : Expr
  | app'   : Expr
  | app    : Expr  → Expr → Expr
deriving BEq, Repr, DecidableEq

open Expr

syntax num term : term

syntax "$" "⸨" term* "⸩" : term
syntax "Π'" term "," term : term
syntax "(Π')" : term
syntax "⸨" term* "⸩" : term
syntax "Ty" term : term
syntax "?_" : term

macro_rules
  | `(Ty $n) => `(Expr.Srt ($n + 1))
  | `(?_) => `(Expr.hole)
  | `($n:num $fn:term) =>
    match n.getNat with
    | 0 => `($fn)
    | .succ n =>
      let n' := Lean.Syntax.mkNatLit n
      `(Expr.next ($n':num $fn))
  | `($ ⸨$f:term $x:term⸩) => `(⸨Expr.app' $f $x⸩)
  | `($ ⸨$f:term $x:term $xs:term*⸩) => `($⸨$⸨$f $x⸩ $xs*⸩)
  | `(Π' $α, $β) => `(Expr.Pi $α $β)
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f:term $x:term)
  | `(⸨$f:term $x:term $xs:term*⸩) => `(⸨⸨$f:term $x:term⸩ $xs:term*⸩)

example :  ⸨(Srt 0) (Srt 1) (Srt 2)⸩ = Expr.app (Expr.app (Expr.Srt 0) (Expr.Srt 1)) (Expr.Srt 2) := rfl

def Expr.toFormat : Expr → Format
  | Srt m => s!"(Srt {m})"
  | K' m n => s!"(K' {m} {n})"
  | K m n => s!"(K {m} {n})"
  | S m n o => s!"(S {m} {n} {o})"
  | Π' α, β => .paren <| "Π' " ++ α.toFormat ++ "," ++ .line ++ β.toFormat
  | I m => s!"(I {m})"
  | .app f x => .bracket "⸨" (f.toFormat ++ (.nest 2 <| .line ++ x.toFormat)) "⸩"
  | .app' => "$"
  | .assert => "assert"
  | .next => "next"
  | .read => "read"

instance : ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨toString ∘ toFormat⟩

namespace Expr

def eval (e : Expr) : Except Format Expr :=
  match e with
  | ⸨(I _m) _α x⸩ => eval x <|> pure x
  | ⸨(K _m _n) _α _β x _y⸩ => eval x <|> (pure x)
  | ⸨(K' _m _n) _α _β x _y⸩ => eval x <|> (pure x)
  | ⸨(S _m _n _o) _α _β _γ x y z⸩ => (do return ⸨(← ⸨x z⸩.eval) (← ⸨y z⸩.eval)⸩) <|>
     (do return ⸨(← ⸨x z⸩.eval) ⸨y z⸩⸩) <|>
     (do return ⸨⸨x z⸩ (← ⸨y z⸩.eval)⸩) <|>
     (do return ⸨⸨x z⸩ ⸨y z⸩⸩)
  | ⸨(Π' α, β) x⸩ => return Π' ⸨α x⸩, ⸨β x⸩
  | ⸨next f _x⸩ => pure f
  | ⸨read e⸩ => pure e
  | ⸨assert e _x⸩ => pure e
  | ⸨$⸨f g⸩ x⸩ => pure ⸨⸨f x⸩ ⸨g x⸩⸩
  | ⸨f x⸩ => (do return ⸨(← f.eval) (← x.eval)⸩) <|> ((·.app x) <$> (f.eval)) <|> (f.app <$> (x.eval))
  | e => .error <| "stuck: " ++ (format e)

def I.type (m : Level) : Expr :=
  Π' (Srt m), Π' (0 read), (0 assert)

end Expr
