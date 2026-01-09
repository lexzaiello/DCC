import Mathlib.Data.Nat.Notation

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

def step (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if with_logs then
    dbg_trace e
  match e with
  --| :: (:: both (:: _a _b)) nil => .none
  | :: (:: both (:: a b)) (:: l nil)
  | :: (:: both (:: a b)) l => do
    pure <| :: (← step (:: a l)) (← step (:: b l))
  | :: (:: π (:: a nil)) (:: x xs) => step (:: a x)
  | :: (:: π (:: nil b)) (:: x xs) =>
    step (:: b xs)
  | :: (:: π (:: a b)) (:: x nil) =>
    let x' ← step (:: a x)
    pure (:: both (:: (:: const (:: x' nil)) b))
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

def try_step_n (n : ℕ) (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if n = 0 then
    pure e
  else
    let e' ← step e with_logs
    (try_step_n (n - 1) e' with_logs) <|> (pure e')

def do_step (e : Expr) (with_logs : Bool := false):= try_step_n 20 e with_logs

def k_untyped : Expr :=
  :: π (:: id nil)

#eval step <| :: k_untyped (:: (symbol "a") (:: (symbol "b") nil))

def s_untyped : Expr :=
  let z := :: π (:: nil id)
  .cons π (:: id (:: both (:: z (:: π (:: id id)))))

def i_untyped : Expr :=
  (:: s_untyped (:: k_untyped (:: k_untyped nil)))

#eval (step <=< step) <| :: s_untyped (:: k_untyped (:: k_untyped (:: (symbol "a") nil)))
#eval (step <=< step <=< step) <| :: (:: s_untyped (:: k_untyped (:: k_untyped nil))) (symbol "a")
#eval (step <=< step <=< step) <| :: i_untyped (:: (symbol "a") nil)
#eval (step <=< step <=< step) <| (:: (:: s_untyped (:: k_untyped k_untyped)) (:: (symbol "a") nil))

namespace church_example

def tre  := k_untyped
def flse := :: k_untyped (:: i_untyped nil)

#eval do_step i_untyped
#eval do_step (:: flse (:: i_untyped (:: (symbol "b") nil))) true
#eval do_step (:: tre (:: i_untyped (:: (symbol "b") nil))) true

def zero := flse

/-
S(S(KS)K)

S(S(KS)K) n f x
=
(S(KS)K) f
(n f)

S (K f) (n f) x

f (n f x)
-/

def succ := :: s_untyped (:: (:: s_untyped (:: (:: k_untyped (:: s_untyped nil)) (:: k_untyped nil))) nil)

def succ' := :: (symbol "S") (:: (:: (symbol "S") (:: (:: (symbol "K") (:: (symbol "S") nil)) (:: (symbol "K") nil))) nil)

#eval (Expr.toString succ')

def my_example : Option Expr :=
  let my_f := k_untyped
  let my_v := symbol "hi"
  do_step (:: (:: zero (:: my_f nil)) (:: my_v nil))

/-
Discards n arguments
-/

def mk_church : ℕ → Expr
  | .zero => zero
  | .succ n => (:: succ (:: (mk_church n) nil))

#eval my_example
#eval do_step (:: succ (:: zero (:: i_untyped (:: (symbol "hi") nil))))
#eval do_step (:: (:: succ (:: zero nil)) (:: i_untyped (:: (symbol "hi") nil)))
--#eval do_step (:: succ (:: zero (:: i_untyped (:: (symbol "hi") nil))))
--#eval do_step (:: (mk_church 0) (:: k_untyped (:: (symbol "hi") nil)))

end church_example
