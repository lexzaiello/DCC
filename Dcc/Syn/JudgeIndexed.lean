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
  | Pi     : red ⸨(Π' α, β) x⸩ (Π' ⸨α x⸩, ⸨β x⸩) -- stepping Π does not substitute binders. we assume here we have the full app
  | head   : red ⸨(head fn) (quot ⸨f x⸩)⸩ ⸨fn (quot f)⸩
  | tail   : red ⸨(tail fn) (quot ⸨f x⸩)⸩ ⸨fn (quot x)⸩
  | app'   : red ⸨$ (f, x) e⸩ ⸨⸨f e⸩ ⸨x e⸩⸩ -- this is fine, since ($ can infer what kind of Syntax α
  | unquot : red ⸨(unquot _α) (quot e)⸩ e
  | left   : red f f' → red ⸨f x⸩ ⸨f' x⸩
  | right  : red x x' → red ⸨f x⸩ ⸨f x'⸩

/-
Helpers
-/
def Syntax.then_const (n_const : ℕ) (fn : Expr := Syntax.id) : Expr := match n_const with
  | .succ n => $ (Syntax.const, (Syntax.then_const (fn := fn) n))
  | .zero => fn

def Syntax.const_n (n_const : ℕ) (e : Expr) := match n_const with
  | .succ n => ⸨Syntax.const (Syntax.const_n n e)⸩
  | .zero => e

syntax term "~>" term : term
macro_rules
  | `($α:term ~> $β:term) => `(Π' ⸨Syntax.const $α:term⸩, ⸨Syntax.const $β:term⸩)

/-
Types for quotation combinators
-/
abbrev Syntax.type (_t : Expr) (m : Level) := (Srt m)

abbrev quot.type (α _e : Expr) := (Syntax α)

abbrev unquot.type (α : Expr) := (Syntax α) ~> α

abbrev Pi.type : Expr → Expr := id

abbrev app'.type (_f x : Expr) (α γ : Expr) := (Π' α, ($ (γ, tail (unquot α), $ (x, tail (unquot α)))))

-- head (quot (f x)) = head (quot f)
-- fn : ∀ (x : Syntax β), γ x
-- (x : α)
-- (f x : β x)
abbrev head.type (_fn β γ : Expr) : Expr := Π' ($ (⸨Syntax.const β⸩, head Syntax.id))
                                             , ($ (⸨Syntax.const γ⸩, head Syntax.id))

abbrev tail.type (_fn β γ : Expr) : Expr := Π' ($ (⸨Syntax.const β⸩, tail Syntax.id))
                                             , ($ (⸨Syntax.const γ⸩, tail Syntax.id))

abbrev hole.type : Expr → Expr := id

abbrev Srt.type (m : Level) : Expr := (Ty m)

/-
Types for the core combinators:
-/
abbrev I.type (m : Level) : Expr :=
    Π' ⸨Syntax.const (Srt m)⸩
  , Π' (head (tail (unquot ?_)))
  , (head (tail (unquot ?_)))

/-
Def infer / eval for prototyping:
-/

def eval (e : Expr) : Except Format Expr :=
  match e with
  | ⸨(I _m) _α x⸩ => eval x <|> pure e
  | ⸨(K _m _n) _α _β x _y⸩ => eval x <|> (pure x)
  | ⸨(K' _m _n) _α _β x _y⸩ => eval x <|> (pure x)
  | ⸨(S _m _n _o) _α _β _γ x y z⸩ => (do return ⸨(← ⸨x z⸩.eval) (← ⸨y z⸩.eval)⸩) <|>
     (do return ⸨(← ⸨x z⸩.eval) ⸨y z⸩⸩) <|>
     (do return ⸨⸨x z⸩ (← ⸨y z⸩.eval)⸩) <|>
     (do return ⸨⸨x z⸩ ⸨y z⸩⸩)
  | ⸨(Π' α, β) x⸩ => return Π' ⸨α x⸩, ⸨β x⸩
  | ⸨(head fn) (quot ⸨f _x⸩)⸩ => eval ⸨fn (quot f)⸩
  | ⸨(tail fn) (quot ⸨_f x⸩)⸩ => eval ⸨fn (quot x)⸩
  | ⸨$ (f, x) e⸩ => (do return ⸨(← ⸨f e⸩.eval) (← ⸨x e⸩.eval)⸩) <|>
     (do return ⸨(← ⸨f e⸩.eval) ⸨x e⸩⸩) <|>
     (do return ⸨⸨f e⸩ (← ⸨x e⸩.eval)⸩) <|>
     (do return ⸨⸨f e⸩ ⸨x e⸩⸩) -- this is fine, since ($ can infer what kind of Syntax α
  | ⸨(unquot _α) (quot e)⸩ => eval e <|> (pure e)
  | ⸨f x⸩ => (do return ⸨(← f.eval) (← x.eval)⸩) <|> ((·.app x) <$> (f.eval)) <|> (f.app <$> (x.eval))
  | e => .error <| "stuck: " ++ (format e)

def infer (e : Expr) (gas : ℕ := 100) : Except Format Expr :=
  let rec norm (e : Expr) (gas : ℕ := gas) : Expr :=
    match gas with
    | .zero => e
    | .succ n => norm ((eval e).toOption.getD e) n

  let not_fn (t : Expr) := .error <| "not a function type: " ++ (format t)

  let mismatch (expected actual : Expr) := .error <| (format expected) ++ " ≠ " ++ (format actual)

  let rec defeq : Expr → Expr → Except Format Expr
    | (Syntax ?_), t@(Syntax _α) => pure t
    | t₁, t₂ => if t₁ == t₂ ∨ (norm ⸨(unquot ?_) t₁⸩ gas) == (norm ⸨(unquot ?_) t₂⸩ gas) then
      pure t₁
    else
      mismatch  t₁ t₂

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
    | (Srt m) => return Syntax.type t m
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
    | Π' (Syntax ?_), (β@(Π' _γ, _δ)), (Syntax α₂@α)
    | Π' α, (β@(Π' _γ, _δ)), α₂ =>
      let _ ← defeq ⸨α (quot ⸨f x⸩)⸩ α₂
      return β
    | Π' (Syntax ?_), β, (Syntax α₂@α)
    | Π' α, β, α₂ =>
      let _ ← defeq ⸨α (quot ⸨f x⸩)⸩ α₂
      return norm ⸨β (quot ⸨f x⸩)⸩
    | t, _ => not_fn t
  | e => .error <| "not well-typed: " ++ (format e)

theorem infer_quot (h_t : infer e = .ok α) : (infer (quot e)) = (.ok (Syntax α)) := by
  induction e
  cases h_t
  rfl
  repeat (unfold infer; simp [h_t]; rfl)

#eval infer ⸨(I 2) (Srt 1) (Srt 0)⸩

end Expr
