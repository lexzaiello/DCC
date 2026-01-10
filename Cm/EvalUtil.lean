import Mathlib.Data.Nat.Notation

def try_step_n {α ε : Type} (f : α → Except ε α) (n : ℕ) (e : α) (with_logs : Bool := false) : Except ε α := do
  if n = 0 then
    pure e
  else
    let e' ← f e
    (try_step_n f (n - 1) e' with_logs) <|> (pure e')

def do_step {α ε : Type} (f : α → Except ε α) (e : α) (with_logs : Bool := false):= try_step_n f 20 e with_logs
