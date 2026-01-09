import Mathlib.Data.Nat.Notation

open Std (Format)
open Std (ToFormat)

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

def Expr.unquote_once : Expr → Expr
  | quote e => e
  | e => e

def Expr.fmt (e : Expr) : Format :=
  match e with
  | .cons (.cons a b) (.cons c d) =>
    ":: " ++ (.group <| .nest 2 <| (.paren (Expr.cons a b).fmt) ++ Format.line ++ (.paren (Expr.cons c d).fmt))
  | .cons x@(.cons a b) xs =>
    ":: " ++ (.group <| .nest 2 <| (.paren (Expr.cons a b).fmt) ++ Format.line ++ xs.fmt)
  | .cons x (.cons a b) =>
    ":: " ++ (.group <| .nest 2 <| x.fmt ++ Format.line ++ (.paren (Expr.cons a b).fmt))
  | .cons x xs =>
    ":: " ++ (.group <| .nest 2 <| x.fmt ++ Format.line ++ xs.fmt)
  | .π => "π"
  | .id => "id"
  | .const => "const"
  | .both => "both"
  | .nil => "nil"
  | .quote e => "'" ++ e.fmt
  | symbol s => "symbol " ++ s

instance Expr.instToFormat : ToFormat Expr where
  format := Expr.fmt

instance Expr.instToString : ToString Expr where
  toString := toString ∘ Expr.fmt

open Expr

notation "::" => Expr.cons

def Expr.push_back (val : Expr) : Expr → Option Expr
  | nil => val
  | :: x xs => do pure <| :: x (← push_back val xs)
  | _ => .none

def Expr.push_arg (arg in_e : Expr) : Option Expr :=
  dbg_trace s!"push {arg} in {in_e}"
  match in_e with
  | :: both _xs => .none
  | :: π _xs => .none
  | :: .id _ => .none
  | :: .const _ => .none
  | :: f (:: x nil) => do pure <| :: f (:: x (:: arg nil))
  | :: f args => do pure <| :: f (← Expr.push_back arg args)
  | _ => .none

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
  | :: (:: π (:: a b)) (:: x nil) => .none
  | :: (:: π (:: a b)) (:: x xs) => do
    pure <| :: (← step (:: a x)) (← step (:: b xs))
  | :: .id nil => .none
  | :: .id (:: x nil)
  | :: .id x => pure x
  | :: (:: .const x) _l => pure x
  | :: (:: f args) x => (do
    let f' ← step (:: f args) with_logs
    pure <| :: f' x)
  | _ => .none

def try_step_n (n : ℕ) (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if n = 0 then
    pure e
  else
    let e' ← .unquote_once <$> step e with_logs
    (try_step_n (n - 1) e' with_logs) <|> (pure e')

def do_step (e : Expr) (with_logs : Bool := false):= try_step_n 20 e with_logs

def k_untyped : Expr :=
  :: π (:: id nil)

#eval step <| :: (:: π (:: id (:: const nil))) (:: (symbol "a") (:: (symbol "b") nil))

#eval step <| :: k_untyped (:: (symbol "a") (:: (symbol "b") nil))

def s_untyped : Expr :=
  let z := :: π (:: nil id)
  .cons π (:: id (:: both (:: z (:: π (:: id id)))))

def i_untyped : Expr :=
  (:: s_untyped (:: k_untyped (:: k_untyped nil)))

#eval do_step (:: i_untyped (:: (symbol "hi") nil)) true

#eval (step <=< step) <| :: s_untyped (:: k_untyped (:: k_untyped (:: (symbol "a") nil)))
#eval (step <=< step <=< step) <| :: (:: s_untyped (:: k_untyped (:: k_untyped nil))) (symbol "a")
#eval (step <=< step <=< step) <| :: i_untyped (:: (symbol "a") nil)
#eval (step <=< step <=< step) <| (:: (:: s_untyped (:: k_untyped k_untyped)) (:: (symbol "a") nil))

namespace church_example

def tre  := k_untyped
def flse := :: k_untyped (:: i_untyped nil)

#eval do_step i_untyped
#eval do_step (:: flse (:: i_untyped (:: (symbol "b") nil)))
#eval do_step (:: tre (:: i_untyped (:: (symbol "b") nil)))

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

def pretty_print_comb (e : Expr) : Expr :=
  if e == i_untyped then
    symbol "I"
  else if e == s_untyped then
    symbol "S"
  else if e == k_untyped then
    symbol "K"
  else match e with
    | :: a b => :: (pretty_print_comb a) (pretty_print_comb b)
    | e => e

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

def my_test : Option Expr := do
  let f ← push_arg i_untyped (← push_arg zero succ)
  dbg_trace ToFormat.format f
  do_step (:: f (:: (symbol "hi") nil))

#eval ToFormat.format <$> my_test
#eval do_step (:: (:: (:: π id) (:: (symbol "I") (:: (:: (symbol "K") (:: (symbol "I") nil)) (symbol "I")))) (:: (symbol "hi") nil))

#eval my_example

#eval ToFormat.format <$> do_step (:: (:: succ (:: zero nil)) (:: i_untyped (:: (symbol "hi") nil)))
#eval ToFormat.format <$> do_step (:: succ (:: zero (:: i_untyped (:: (symbol "hi") nil))))
#eval do_step (:: (:: succ (:: zero nil)) (:: i_untyped (:: (symbol "hi") nil)))
--#eval do_step (:: succ (:: zero (:: i_untyped (:: (symbol "hi") nil))))
--#eval do_step (:: (mk_church 0) (:: k_untyped (:: (symbol "hi") nil)))

end church_example
