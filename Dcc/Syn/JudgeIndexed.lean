import Dcc.Syn.AstIndexed

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

def Pi.type (_α _β t_β : Expr) := t_β

def app'.type (_f x : Expr) (α γ : Expr) := (Π' α, ($ (γ, tail Syntax.id, $ (x, tail Syntax.id))))

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

end Expr
