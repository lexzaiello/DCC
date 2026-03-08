import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation
open Std (ToFormat Format)
open Std.ToFormat (format)
open Relation

abbrev Level := ℕ

inductive Expr where
  | Srt    : Level → Expr
  | Pi     : Level → Expr → Expr → Expr -- Pi (α : Syntax (Sort m)) (β : Sort n) : (Sort n)
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
syntax "(Π'" term ")" term "," term : term
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
  | `((Π' $m) $α, $β) => `(Expr.Pi $m $α $β)
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f:term $x:term)
  | `(⸨$f:term $x:term $xs:term*⸩) => `(⸨⸨$f:term $x:term⸩ $xs:term*⸩)

example :  ⸨(Srt 0) (Srt 1) (Srt 2)⸩ = Expr.app (Expr.app (Expr.Srt 0) (Expr.Srt 1)) (Expr.Srt 2) := rfl

def Expr.toFormat : Expr → Format
  | .hole => "?_"
  | Srt m => s!"(Srt {m})"
  | K' m n => s!"(K' {m} {n})"
  | K m n => s!"(K {m} {n})"
  | S m n o => s!"(S {m} {n} {o})"
  | (Π' m) α, β => .paren <| "Π' " ++ (.paren (format m)) ++ " " ++ α.toFormat ++ "," ++ .line ++ β.toFormat
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
  | ⸨(I _m) _α x⸩ => pure x
  | ⸨(K _m _n) _α _β x _y⸩ => pure x
  | ⸨(K' _m _n) _α _β x _y⸩ => pure x
  | ⸨(S _m _n _o) _α _β _γ x y z⸩ => return ⸨⸨x z⸩ ⸨y z⸩⸩
  | ⸨((Π' m) α, β) x⸩ => return (Π' m) ⸨α x⸩, ⸨β x⸩
  | ⸨next f _x⸩ => pure f
  | ⸨read e⸩ => pure e
  | ⸨assert e _x⸩ => pure e
  | ⸨${π} f g x⸩ => pure ⸨π ⸨f x⸩ ⸨g x⸩⸩
  | ⸨f x⸩ => do return ⸨(← f.eval) x⸩
  | e => .error <| "stuck: " ++ (format e)

abbrev comp (f g : Expr) : Expr :=
  ⸨${read} ⸨assert f⸩ g⸩

infix:30 "∘'" => comp

abbrev assert_n (n : ℕ) (fn : Expr) : Expr :=
  (List.replicate n assert).foldr (fun e acc => (e ∘' acc)) fn

def I.type (m : Level) : Expr :=
  (Π' m) (Srt m), (Π' m) (0 read), (0 assert)

def K'.type (m n : Level) : Expr :=
  (Π' m) (Srt m), (Π' m) ⸨assert (Srt n)⸩, (Π' m) (0 assert), (Π' m) (1 assert), (assert_n 3 (0 read))

def K.type (m n : Level) : Expr :=
    (Π' m) (Srt m)
  , (Π' m) ((Π' n.succ) (0 read), (1 ⸨assert (Srt n)⸩))
  , (Π' m) (0 assert)
  , (Π' m) ⸨${${read}} (1 assert) (2 read)⸩
  , (assert_n 3 read)

def S.type (m n o : Level) : Expr :=
    (Π' o) (Srt m)
  , (Π' o) ((Π' n.succ) (0 read), (1 ⸨assert (Srt n)⸩))
  , (Π' o) ((Π' o.succ) (0 assert)
      , (Π' o.succ) (1 read)
      , (3 ⸨assert (Srt o)⸩))
  , (Π' o) ((Π' o) (assert_n 2 (0 read))
      , (Π' o) (1 assert)
      , (2 read))
   , (Π' o) ((Π' n) (assert_n 3 (0 read))
       , (1 (assert ∘' assert)))
   , (Π' o) (assert_n 4 (0 read))
   , (2 (${read} ∘' assert))

def norm (e : Expr) (gas : ℕ := 100) :=
  match gas with
  | .zero => e
  | .succ n =>
    match e with
    | (Π' m) α, β =>
      (Π' m) (norm α n), (norm β n)
    | e =>
      norm ((eval e).toOption.getD e) n

def defeq (α β : Expr) (gas : ℕ := 100) : Except Format Unit :=
  match gas, α, β with
  | .succ n, ((Π' _m₁) α₁, β₁), ((Π' _m₂) α₂, β₂) => do
    let _ ← (defeq α₁ α₂ n).mapError (fun e => "while checking Π domain: " ++ e)
    (defeq (norm ⸨β₁ ?_⸩) (norm ⸨β₂ ?_⸩) n).mapError (fun e => "while checking Π codomain: " ++ e)
  | .succ n, ⸨assert e₁⸩, ⸨assert e₂⸩ => defeq e₁ e₂ n
  | _, e₁, e₂ =>
    if norm e₁ gas == norm e₂ gas then
      pure ()
    else
      .error <| (format α) ++ " ≠ " ++ (format β)

def infer : Expr → Except Format Expr
  | I m => return I.type m
  | K m n => return K.type m n
  | K' m n => return K'.type m n
  | S m n o => return S.type m n o
  | Srt m => return Srt m.succ
  | (Π' m) _α, _β => return Srt m
  | ⸨f x⸩ => do match ← norm <$> infer f, ← norm <$> infer x with
    | ((Π' _m) α₁, β), α₂ => do
      let _ ← (defeq α₁ α₂).mapError
        (fun e => "argument mismatch in app " ++ (format ⸨f x⸩) ++ ":" ++ .line ++ e)
      pure <| norm ⸨β x⸩
    | t₁, _t₂ =>
      .error <| "not a function type: " ++ (.nest 2 <| .line ++ (format t₁))
  | e => .error <| "not well-typed: " ++ (.nest 2 <| .line ++ (format e))

#eval infer ⸨(I 2) (Srt 1) (Srt 0)⸩
#eval infer ⸨(K 3 2) (Srt 2) ⸨(I 3) (Srt 2)⸩ (Srt 1) (Srt 0)⸩

syntax "(" "~>" term ")" term "," term : term

macro_rules
  | `((~> $m:term) $α:term, $β:term) => `((Π' $m) $α, ⸨assert $β⸩)

def mk_I (α : Expr) (m : Level) : Expr :=
  let α := α
  let y := ⸨(K' 2 m) (Srt 1) α (Srt 0)⸩
  let x := ⸨(K' m 2) α (Srt 1)⸩

  let β := ⸨(K' 3 m) (Srt 2) α (Srt 1)⸩
  let γ := ⸨(K' m.succ m) ((~> m.succ) (Srt 1), (Srt m)) α ⸨(K' m.succ 2) (Srt m) (Srt 1) α⸩⸩

  ⸨(S m 2 m) α β γ x y⸩

#eval infer <| mk_I (Srt 1) 2
#eval infer <| ⸨(mk_I (Srt 1) 2) (Srt 0)⸩

inductive red : Expr → Expr → Prop
  | I      : red ⸨(I _m) _α x⸩ x
  | K      : red ⸨(K _m _n) _α _β x _y⸩ x
  | K'     : red ⸨(K' _m _n) _α _β x _y⸩ x
  | S      : red ⸨(S _m _n _o) _α _β _γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | Pi     : red ⸨((Π' m) α, β) x⸩ ((Π' m) ⸨α x⸩, ⸨β x⸩)
  | next   : red ⸨next f _x⸩ f
  | read   : red ⸨read e⸩ e
  | assert : red ⸨assert e _x⸩ e
  | app'   : red ⸨${π} f g x⸩ ⸨π ⸨f x⸩ ⸨g x⸩⸩
  | left   : red f f' → red ⸨f x⸩ ⸨f' x⸩

inductive deq : Expr → Expr → Prop
  | red    : red a b  → deq a b
  | right  : deq x x' → deq ⸨f x⸩ ⸨f x'⸩
  | leftp  : deq α α' → deq ((Π' m) α, β) ((Π' m) α', β)
  | rightp : deq β β' → deq ((Π' m) α, β) ((Π' m) α, β')

def red.rel : Expr → Expr → Prop := Relation.EqvGen red
def red.iseqv := Relation.EqvGen.is_equivalence red

def deq.rel : Expr → Expr → Prop := Relation.EqvGen deq
def deq.iseqv := Relation.EqvGen.is_equivalence deq

instance instSetoid : Setoid Expr where
  r := deq.rel
  iseqv := deq.iseqv

inductive judge : Expr → Expr → Prop
  | I   : judge (I.type m) (I m)
  | K   : judge (K.type m n) (K m n)
  | K'  : judge (K'.type m n) (K' m n)
  | S   : judge (S.type m n o) (S m n o)
  | Srt : judge (Srt m.succ) (Srt m)
  | Pi  : judge (Srt m) ((Π' m) _α, _β)
  | app : judge ((Π' _m) α, β) f
    → judge α x
    → judge ⸨β x⸩ ⸨f x⸩
  | conv : judge t₁ x → t₁ ≈ t₂ → judge t₂ x

example : judge (Srt 1) ⸨(I 2) (Srt 1) (Srt 0)⸩ := by
  apply judge.conv
  apply judge.app
  apply judge.conv
  apply judge.app
  apply judge.I
  exact judge.Srt
  apply EqvGen.rel
  apply deq.red
  apply red.Pi
  apply judge.conv
  apply judge.Srt
  apply Setoid.symm
  apply EqvGen.rel
  apply deq.red
  apply red.read
  apply EqvGen.rel
  apply deq.red
  apply red.assert

theorem judge_I_par {h_t_α : judge (Srt m) α} : judge ((Π' m) α, ⸨assert α⸩) ⸨(I m) α⸩ := by
  apply judge.conv
  apply judge.app
  apply judge.I
  assumption
  apply EqvGen.trans
  apply EqvGen.rel
  apply deq.red
  apply red.Pi
  apply EqvGen.rel
  apply deq.leftp
  apply deq.red
  apply red.read

theorem judge_I {h_t_α : judge (Srt m) α} {h_t_x : judge α x} : judge α ⸨(I m) α x⸩ := by
  apply judge.conv
  apply judge.app
  apply judge.conv
  apply judge.app
  apply judge.I
  exact h_t_α
  apply EqvGen.rel
  apply deq.red
  apply red.Pi
  apply judge.conv
  assumption
  apply Setoid.symm
  apply EqvGen.rel
  apply deq.red
  apply red.read
  apply EqvGen.rel
  apply deq.red
  apply red.assert

end Expr
