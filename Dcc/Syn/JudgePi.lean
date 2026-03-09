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
syntax "_?" : term

macro_rules
  | `(Ty $n) => `(Expr.Srt ($n + 1))
  | `(_?) => `(Expr.hole)
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
  | .hole => "_?"
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
  | e => .error <| "stuck: " ++ (format e)

end Expr

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

inductive Comb : Expr → Prop where
  | I₀      : Comb (I m)
  | K₀      : Comb (K m n)
  | K'₀     : Comb (K' m n)
  | S₀      : Comb (S m n o)
  | next₀   : Comb next
  | app'₀   : Comb $
  | read    : Comb read
  | assert₀ : Comb assert

inductive Atom : Expr → Prop where
  | comb    : Comb e → Atom e
  | Srt     : Atom (Srt m)

inductive Whnf : Expr → Prop where
  | hole    : Whnf _?
  | atom    : Atom c → Whnf c
  | I₁      : Whnf ⸨(I m) α⸩
  | K₁      : Whnf ⸨(K m n) α⸩
  | K₂      : Whnf ⸨(K m n) α β⸩
  | K₃      : Whnf ⸨(K m n) α β x⸩
  | K'₁     : Whnf ⸨(K' m n) α⸩
  | K'₂     : Whnf ⸨(K' m n) α β⸩
  | K'₃     : Whnf ⸨(K' m n) α β x⸩
  | S₁      : Whnf ⸨(S m n o) α⸩
  | S₂      : Whnf ⸨(S m n o) α β⸩
  | S₃      : Whnf ⸨(S m n o) α β γ⸩
  | S₄      : Whnf ⸨(S m n o) α β γ x⸩
  | S₅      : Whnf ⸨(S m n o) α β γ x y⸩
  | Pi      : Whnf ((Π' m) α, β)
  | next₁   : Whnf ⸨next f⸩
  | assert₁ : Whnf ⸨assert e⸩
  | app'₁   : Whnf ⸨$ a⸩
  | app'₂   : Whnf ⸨$ a b⸩
  | app'₃   : Whnf ⸨$ a b c⸩

inductive Red : Expr → Expr → Prop
  | I      : Red ⸨(I _m) _α x⸩ x
  | K      : Red ⸨(K _m _n) _α _β x _y⸩ x
  | K'     : Red ⸨(K' _m _n) _α _β x _y⸩ x
  | S      : Red ⸨(S _m _n _o) _α _β _γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | Pi     : Red ⸨((Π' m) α, β) x⸩ ((Π' m) ⸨α x⸩, ⸨β x⸩)
  | next   : Red ⸨next f _x⸩ f
  | read   : Red ⸨read e⸩ e
  | assert : Red ⸨assert e _x⸩ e
  | app'   : Red ⸨${π} f g x⸩ ⸨π ⸨f x⸩ ⸨g x⸩⸩

abbrev RedStar := Relation.ReflTransGen Red
abbrev RedStar.tail {a b c : Expr} := Relation.ReflTransGen.tail (r := Red) (a := a) (b := b) (c := c)
abbrev RedStar.refl {a : Expr} := Relation.ReflTransGen.refl (r := Red) (a := a)

inductive ParRed : Expr → Expr → Prop where
  | refl_K'     : ParRed (K' m n) (K' m n)
  | refl_K      : ParRed (K m n) (K m n)
  | refl_S      : ParRed (S m n o) (S m n o)
  | refl_I      : ParRed (I m) (I m)
  | refl_hole   : ParRed (_?) (_?)
  | refl_Srt    : ParRed (Srt m) (Srt m)
  | refl_next   : ParRed next next
  | refl_read   : ParRed read read
  | refl_assert : ParRed assert assert
  | refl_app'   : ParRed $ $
  | I           : ParRed x x' → ParRed ⸨(I _m) _α x⸩ x'
  | K           : ParRed x x' → ParRed ⸨(K _m _n) _α _β x _y⸩ x'
  | K'          : ParRed x x' → ParRed ⸨(K' _m _n) _α _β x _y⸩ x'
  | S           : ParRed ⸨⸨x z⸩ ⸨y z⸩⸩ s'
    → ParRed ⸨(S _m _n _o) _α _β _γ x y z⸩ s'
  | Pi          : ParRed ((Π' m) ⸨α x⸩, ⸨β x⸩) P' → ParRed ⸨((Π' m) α, β) x⸩ P'
  | Pival       : ParRed α α' → ParRed β β' → ParRed ((Π' m) α, β) ((Π' m) α', β')
  | next        : ParRed f f' → ParRed ⸨next f _x⸩ f'
  | read        : ParRed e e' → ParRed ⸨read e⸩ e'
  | assert      : ParRed e e' → ParRed ⸨assert e _x⸩ e'
  | app'        : ParRed ⸨π ⸨f x⸩ ⸨g x⸩⸩ P'
    → ParRed ⸨${π} f g x⸩ P'
  | app         : ParRed f f'
    → ParRed x x'
    → ParRed ⸨f x⸩ ⸨f' x'⸩

inductive Judge : Expr → Expr → Prop
  | I   : Judge (I.type m) (I m)
  | K   : Judge (K.type m n) (K m n)
  | K'  : Judge (K'.type m n) (K' m n)
  | S   : Judge (S.type m n o) (S m n o)
  | Srt : Judge (Srt m.succ) (Srt m)
  | Pi  : Judge (Srt m) ((Π' m) _α, _β)
  | app : Judge ((Π' _m) α, β) f
    → Judge α x
    → Judge ⸨β x⸩ ⸨f x⸩
  | conv : Judge A x → (∃ C, ParRed A C ∧ ParRed B C) → Judge B x

theorem Step.sound (e₁ e₂) : Red e₁ e₂ → eval e₁ = .ok e₂ := by
  intro h_r
  induction h_r
  repeat rfl

theorem Step.complete (e₁ e₂) : eval e₁ = .ok e₂ → Red e₁ e₂ := by
  intro h_e
  unfold eval at h_e
  induction e₁
  repeat simp at h_e
  case app f x ih =>
    rename_i a
    split at h_e
    rename_i heq
    cases heq
    cases h_e
    exact Red.I
    rename_i heq
    cases heq
    cases h_e
    exact Red.K
    rename_i heq
    cases heq
    cases h_e
    exact Red.K'
    rename_i heq
    cases heq
    cases h_e
    exact Red.S
    rename_i heq
    cases heq
    cases h_e
    exact Red.Pi
    rename_i heq
    cases heq
    cases h_e
    exact Red.next
    rename_i heq
    cases heq
    cases h_e
    exact Red.read
    rename_i heq
    cases heq
    cases h_e
    exact Red.assert
    rename_i heq
    cases heq
    cases h_e
    exact Red.app'
    simp_all

namespace Judge

theorem inv : Judge ((Π' m) α, β) f → Judge α x → Judge ⸨β x⸩ ⸨f x⸩ := by
  apply Judge.app

end Judge

namespace ParRed

theorem refl : ParRed e e := by
  induction e
  exact ParRed.refl_Srt
  apply ParRed.Pival
  repeat assumption
  apply ParRed.refl_K'
  apply ParRed.refl_K
  apply ParRed.refl_S
  apply ParRed.refl_I
  apply ParRed.refl_hole
  apply ParRed.refl_next
  apply ParRed.refl_read
  apply ParRed.refl_assert
  apply ParRed.refl_app'
  apply ParRed.app
  repeat assumption

end ParRed

example : Judge (Srt 1) ⸨(I 2) (Srt 1) (Srt 0)⸩ := by
  apply Judge.conv
  apply Judge.app
  apply Judge.conv
  apply Judge.app
  apply Judge.I
  exact Judge.Srt
  use (Π' 2) ⸨read (Srt 1)⸩, ⸨assert (Srt 1)⸩
  constructor
  apply ParRed.Pi
  exact ParRed.refl
  apply ParRed.refl
  apply Judge.conv
  exact Judge.Srt
  exact ⟨Srt 1, ParRed.refl, ParRed.read ParRed.refl⟩
  exact ⟨Srt 1, .assert ParRed.refl, ParRed.refl⟩
