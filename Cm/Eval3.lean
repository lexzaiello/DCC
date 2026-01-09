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
  | quote  : Expr
    → Expr
  | symbol : String
    → Expr
deriving Repr, BEq

def Expr.toString : Expr → String
  | .quote e => s!"'{e.toString}"
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

def step (e : Expr) : Option Expr := do
  match e with
  | :: (:: both (:: _a _b)) nil => .none
  | :: (:: both (:: a b)) (:: l nil)
  | :: (:: both (:: a b)) l => do
    pure <| :: (← step (:: a l)) (← step (:: b l))
  | :: (:: π (:: nil b)) (:: x nil) => .none
  | :: (:: π (:: a b)) (:: x nil)
  | :: (:: π (:: a nil)) (:: x xs) => step (:: a x)
  | :: (:: π (:: nil b)) (:: x xs) => step (:: b xs)
  | :: (:: π (:: a b)) (:: x xs) => do
    pure <| :: (← step (:: a x)) (← step (:: b xs))
  | :: .id nil => .none
  | :: .id (:: x nil)
  | :: .id x => pure x
  | :: (:: .const (:: x nil)) _l => pure x
  | :: (:: f args) x => do
    -- This is some other curried function
    let f' ← step (:: f args)
    pure <| :: f' x
  | _ => .none

def k_untyped : Expr :=
  :: π (:: id nil)

#eval step <| :: k_untyped (:: (symbol "a") (:: (symbol "b") nil))

def s_untyped : Expr :=
  let z := :: π (:: nil id)
  .cons π (:: id (:: both (:: z (:: π (:: id id)))))

#eval (step <=< step) <| :: s_untyped (:: k_untyped (:: k_untyped (:: (symbol "a") nil)))
#eval (step <=< step <=< step) <| :: (:: s_untyped (:: k_untyped (:: k_untyped nil))) (symbol "a")

#eval (step <=< step) <| (:: (:: s_untyped (:: k_untyped k_untyped)) (:: (symbol "a") nil))

namespace church_example

def zero := k_untyped

--def succ := 

end church_example
