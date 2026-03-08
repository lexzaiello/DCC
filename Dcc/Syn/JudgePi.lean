import Mathlib.Data.Nat.Notation
open Std (ToFormat Format)
open Std.ToFormat (format)

abbrev Level := ℕ

inductive Expr where
  | Srt    : Level → Expr
  | Pi     : Expr  → Expr  → Expr -- Pi (α : Syntax (Sort m)) (β : Sort n) : (Sort n)
  | K'     : Level → Level → Expr
  | K      : Level → Level → Expr
  | S      : Level → Level → Level → Expr
  | I      : Level → Expr
  | hole   : Expr
  | next   : Expr
  | read   : Expr
  | assert : Expr
  | app'   : Expr
  | app    : Expr  → Expr → Expr
deriving BEq, Repr, DecidableEq

open Expr

syntax num term : term

syntax "$" : term
syntax "${" term "}" : term
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
      `(⸨Expr.next ($n':num $fn)⸩)
  | `(${ $t:term }) => `(⸨$ $t⸩)
  | `($) => `(Expr.app')
  | `(Π' $α, $β) => `(Expr.Pi $α $β)
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f:term $x:term)
  | `(⸨$f:term $x:term $xs:term*⸩) => `(⸨⸨$f:term $x:term⸩ $xs:term*⸩)

example :  ⸨(Srt 0) (Srt 1) (Srt 2)⸩ = Expr.app (Expr.app (Expr.Srt 0) (Expr.Srt 1)) (Expr.Srt 2) := rfl

def Expr.toFormat : Expr → Format
  | .hole => "?_"
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
  | ⸨(Π' α, β) x⸩ => return Π' ((⸨α x⸩.eval).toOption.getD ⸨α x⸩), ((⸨β x⸩.eval).toOption.getD ⸨β x⸩)
  | ⸨next f _x⸩ => pure f
  | ⸨read e⸩ => pure e
  | ⸨assert e _x⸩ => pure e
  | ⸨${π} f g x⸩ => pure ⸨π ⸨f x⸩ ⸨g x⸩⸩
  | ⸨f x⸩ => (do return ⸨(← f.eval) (← x.eval)⸩) <|> ((·.app x) <$> (f.eval)) <|> (f.app <$> (x.eval))
  | e => .error <| "stuck: " ++ (format e)

abbrev comp (f g : Expr) : Expr :=
  ⸨${read} ⸨assert f⸩ g⸩

infix:30 "∘'" => comp

abbrev assert_n (n : ℕ) (fn : Expr) : Expr :=
  (List.replicate n assert).foldr (fun e acc => (e ∘' acc)) fn

def I.type (m : Level) : Expr :=
  Π' (Srt m), Π' (0 read), (0 assert)

def K.type (m n : Level) : Expr :=
    Π' (Srt m)
  , Π' (Π' (0 read), (1 ⸨assert (Srt n)⸩))
  , Π' (0 assert)
  , Π' ⸨${${read}} (1 assert) (2 read)⸩
  , (assert_n 3 read)

def norm (e : Expr) (gas : ℕ := 100) :=
  match gas with
  | .zero => e
  | .succ n =>
    match e with
    | Π' α, β =>
      Π' (norm α n), (norm β n)
    | e =>
      norm ((eval e).toOption.getD e) n

def defeq (α β : Expr) (gas : ℕ := 100) : Except Format Unit :=
  match α, β with
  | (Π' α₁, β₁), (Π' α₂, β₂) => do
    let _ ← defeq α₁ α₂
    defeq β₁ β₂
  | e₁, e₂ =>
    if norm e₁ gas == norm e₂ gas then
      pure ()
    else
      .error <| (format α) ++ " ≠ " ++ (format β)

def infer : Expr → Except Format Expr
  | (I m) => return I.type m
  | K m n => return K.type m n
  | Srt m => return Srt m.succ
  | ⸨f x⸩ => do match ← norm <$> infer f, ← norm <$> infer x with
    | (Π' α₁, β), α₂ => do
      let _ ← defeq α₁ α₂
      pure <| norm ⸨β x⸩
    | t₁, _t₂ =>
      .error <| "not a function type: " ++ (.nest 2 <| .line ++ (format t₁))
  | e => .error <| "not well-typed: " ++ (.nest 2 <| .line ++ (format e))

#eval infer ⸨(I 2) (Srt 1) (Srt 0)⸩
#eval infer ⸨(K 3 2) (Srt 2) ⸨(I 3) (Srt 2)⸩ (Srt 1) (Srt 0)⸩

end Expr
