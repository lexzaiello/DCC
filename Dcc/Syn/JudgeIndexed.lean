import Dcc.Syn.AstIndexed

open Std (Format)
open Std.ToFormat (format)

/-
Another change:
dom in apps receive the entire quoted app
-/

namespace Expr

inductive red : Expr → Expr → Prop
  | I      : red ⸨(I m) α x⸩ x
  | K      : red ⸨(K m n) α β x y⸩ x
  | K'     : red ⸨(K' m n) α β x y⸩ x
  | S      : red ⸨(S m n o) α β γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | Pi     : red ⸨(Π' α, β) x⸩ ⸨β x⸩ -- stepping Π does not substitute binders. we assume here we have the full app
  | head   : red ⸨(head fn) (quot ⸨f x⸩)⸩ ⸨fn (quot f)⸩
  | tail   : red ⸨(tail fn) (quot ⸨f x⸩)⸩ ⸨fn (quot x)⸩
  | app'   : red ⸨$ (f, x) e⸩ ⸨⸨f e⸩ ⸨x e⸩⸩ -- this is fine, since ($ can infer what kind of Syntax α
  | unquot : red ⸨(unquot _α) (quot e)⸩ e
  | left   : red f f' → red ⸨f x⸩ ⸨f' x⸩
  | right  : red x x' → red ⸨f x⸩ ⸨f x'⸩

/-
Helpers
-/
def then_const (n_const : ℕ) (fn : Expr := Syntax.id) : Expr := match n_const with
  | .succ n => $ (Syntax.const, (then_const (fn := fn) n))
  | .zero => fn

syntax term "~>" term : term
macro_rules
  | `($α:term ~> $β:term) => `(Π' (Syntax.const $α:term), (Syntax.const $β:term))

/-
Types for quotation combinators
-/
def Syntax.type (_t : Expr) (m : Level) := (Ty m)

def quot.type (α _e : Expr) := (Syntax α)

def unquot.type (α : Expr) := (Syntax α) ~> α

def Pi.type : Expr → Expr := id

def app'.type (_f x : Expr) (α γ : Expr) := (Π' α, ($ (γ, tail (unquot α), $ (x, tail (unquot α)))))

-- head (quot (f x)) = head (quot f)
-- fn : ∀ (x : Syntax β), γ x
-- (x : α)
-- (f x : β x)
def head.type (_fn β γ : Expr) : Expr := Π' ($ (Syntax.const β, head Syntax.id))
                                             , ($ (Syntax.const γ, head Syntax.id))

def tail.type (_fn β γ : Expr) : Expr := Π' ($ (Syntax.const β, tail Syntax.id))
                                             , ($ (Syntax.const γ, tail Syntax.id))

def hole.type : Expr → Expr := id

def Srt.type (m : Level) : Expr := (Ty m)

/-
Types for the core combinators:
-/
def I.type (m : Level) : Expr :=
    Π' (Ty m)
  , Π' (head (tail Syntax.id))
  , (head (tail Syntax.id))

/-
Def infer / eval for prototyping:
-/

def infer (e : Expr) : Except Format Expr :=
  let norm : Expr → Expr := id

  let not_fn (t : Expr) := .error <| "not a function type: " ++ (format t)

  let mismatch (expected actual : Expr) := .error <| (format expected) ++ " ≠ " ++ (format actual)

  let defeq : Expr → Expr → Bool
    | (Syntax ?_), (Syntax _α) => true
    | t₁, t₂ => t₁ == t₂

  match e with
  | I m => return I.type m
  | Srt m => return Srt.type m
  | quot e => (quot.type · e) <$> infer e
  | unquot α => return unquot.type α
  | Π' _α, Π' β, γ => Pi.type <$> infer (Π' β, γ)
  | Π' _α, β => do match ← norm <$> infer β with
    | (Π' _α', γ) => pure ⸨γ ?_⸩
    | t => not_fn t
  | Syntax t => do match ← norm <$> infer t with
    | (Ty m) => return Syntax.type t m
    | t => .error <| "not a type: " ++ (format t)
  | app' f x => do match ← norm <$> infer f with
    | (Π' α, Π' _β, γ) => return app'.type f x α γ
    | t => not_fn t
  | tail fn => do match ← norm <$> infer fn with
    | Π' β, γ => return tail.type fn β γ
    | t => not_fn t
  | head fn => do match ← norm <$> infer fn with
    | Π' β, γ => return head.type fn β γ
    | t => not_fn t
  | app f x => do match ← norm <$> infer f, ← norm <$> infer x with
    | Π' α, (β@(Π' _γ, _δ)), α₂ =>
      let α' := norm ⸨α ⸨f x⸩⸩
      if defeq α α₂ then
        return β
      else
        mismatch α' α₂
    | Π' α, β, α₂ =>
      let α' := norm ⸨α ⸨f x⸩⸩
      if defeq α α₂ then
        return norm ⸨β ⸨f x⸩⸩
      else
        mismatch α' α₂
    | t, _ => not_fn t
  | e => .error <| "not well-typed: " ++ (format e)

end Expr
