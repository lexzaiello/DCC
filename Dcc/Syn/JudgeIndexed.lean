import Dcc.Syn.AstIndexed

syntax term "~>" term : term
macro_rules
  | `($α:term ~> $β:term) => `(Π' (Syntax.const $α:term), (Syntax.const $β:term))

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

def quot_const (n_const : ℕ) : Expr := match n_const with
  | .succ n => $ (Syntax.const, (quot_const n))
  | .zero => Syntax.id

def Syntax.type (_t : Expr) (m : Level) := (Ty m)

def quot.type (t _e : Expr) := (Syntax t)

def unquot.type (α : Expr) := (Syntax α) ~> α

end Expr
