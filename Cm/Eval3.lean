/-
Optimizing for ZK design:
- List-oriented language is potentially ideal
- reducing currying

- spine register
- arguments register
- may also want a type register

- When do we combine the arguments registers?
This is mainly a problem in both.
both should probably combine by default.
-/

inductive Expr where
  | cons   : Expr
    → Expr
    → Expr
  | π      : Expr
  | id     : Expr
  | const  : Expr
  | both   : Expr
  | nil    : Expr
  | symbol : String
    → Expr
deriving Repr, BEq

def Expr.toString : Expr → String
  | .cons a@(.cons a₁ a₂) b@(.cons b₁ b₂) => s!":: ({a.toString}) ({b.toString})"
  | .cons a b@(.cons b₁ b₂) => s!":: {a.toString} ({b.toString})"
  | .cons a@(.cons a₁ a₂) b => s!":: ({a.toString}) {b.toString}"
  | .cons a b => s!":: {a.toString} {b.toString}"
  | .π => "π"
  | .id => "id"
  | .const => "const"
  | .both => "both"
  | .nil => "nil"
  | .symbol s => s!"symbol {s}"

instance Expr.instToString : ToString Expr where
  toString := Expr.toString

open Expr

notation "::" => Expr.cons

def step (e : Expr) : Option Expr :=
  match e with
  | :: (:: both (:: a b)) l => do
    let a' ← step (:: a l)
    let b' ← step (:: b l)
    pure <| :: a' b'
  | :: (:: π (:: a nil)) (:: x xs) => step (:: a x)
  | :: (:: π (:: nil b)) (:: x xs) => step (:: b xs)
  | :: (:: π (:: a b)) (:: x xs) => do
    pure <| :: (← step (:: a x)) (← step (:: b xs))
  | :: .id x => pure x
  | :: (:: .const (:: x nil)) _l => pure x
  | :: f x => do
    let f' ← step f
    pure <| :: f' x
  | _ => .none

def k_untyped : Expr :=
  :: π (:: id nil)

#eval step <| :: k_untyped (:: (symbol "a") (symbol "b"))

def s_untyped : Expr :=
  let z := :: π (:: nil id)
  .cons π (:: id (:: both (:: z (:: π (:: id id)))))

#eval step <| :: s_untyped (:: (symbol "a") (:: (symbol "b") (symbol "c")))
#eval (step <=< step) <| :: s_untyped (:: k_untyped (:: k_untyped (symbol "a")))
