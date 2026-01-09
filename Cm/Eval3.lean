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
  | head   : Expr
  | cons   : Expr
    → Expr
    → Expr
  | π      : Expr
    → Expr
    → Expr
  | read   : Expr
  | const  : Expr
  | both   : Expr
    → Expr
    → Expr
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
  | .head => "head"
  | .cons (.cons a b) (.cons c d) =>
    ":: " ++ (.group <| .nest 2 <| (.paren (Expr.cons a b).fmt) ++ Format.line ++ (.paren (Expr.cons c d).fmt))
  | .cons x@(.cons a b) xs =>
    ":: " ++ (.group <| .nest 2 <| (.paren (Expr.cons a b).fmt) ++ Format.line ++ xs.fmt)
  | .cons x (.cons a b) =>
    ":: " ++ (.group <| .nest 2 <| x.fmt ++ Format.line ++ (.paren (Expr.cons a b).fmt))
  | .cons x xs =>
    ":: " ++ (.group <| .nest 2 <| x.fmt ++ Format.line ++ xs.fmt)
  | .π f g => "π " ++ (.group <| .nest 2 <| (.paren f.fmt) ++ Format.line ++ (.paren g.fmt))
  | .read => "read"
  | .const => "const"
  | .both f g => "both " ++ (.group <| .nest 2 <| (.paren f.fmt) ++ Format.line ++ (.paren g.fmt))
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
  match in_e with
  | both _f _g => .none
  | π _a _b => .none
  | :: .read _ => .none
  | :: .const _ => .none
  | nil => arg
  | :: f args => do pure <| :: f (← Expr.push_back arg args)
  | _ => .none

def step (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if with_logs then
    dbg_trace e
  match e with
  --| :: (:: both (:: _a _b)) nil => .none
  | :: head (:: x xs) => pure x
  --| :: (both a b) (:: l nil)
  | :: (both a b) l => do
    pure <| :: (← step (:: a l) with_logs) (← step (:: b l) with_logs)
  | :: (π a nil) (:: x xs) => step (:: a x)
  | :: (π nil b) (:: x xs) =>
    step (:: b xs)
  | :: (π a b) (:: x nil) => .none
  | :: (π a b) (:: x xs) => do
    pure <| :: (← step (:: a x) with_logs) (← step (:: b xs) with_logs)
  | :: .read nil => .none
  | :: .read (:: x nil)
  | :: .read x => pure x
  | :: (:: .const x) _l => pure x
  | :: (:: f args) x => (do
    let f' ← step (:: f args) with_logs
    pure <| :: f' x) <|> push_arg x (:: f args)
  | _ => .none

def try_step_n (n : ℕ) (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if n = 0 then
    pure e
  else
    let e' ← .unquote_once <$> step e with_logs
    (try_step_n (n - 1) e' with_logs) <|> (pure e')

def do_step (e : Expr) (with_logs : Bool := false):= try_step_n 20 e with_logs

def k_untyped : Expr :=
  π read nil

#eval step <| :: (π read (:: const nil)) (:: (symbol "a") (:: (symbol "b") nil))

#eval step <| :: k_untyped (:: (symbol "a") (:: (symbol "b") nil))

def s_untyped : Expr :=
  let z := π nil read
  π read (both z (π read read))

def i_untyped : Expr :=
  (:: s_untyped (:: k_untyped (:: k_untyped nil)))

#eval do_step =<< push_arg (symbol "hi") i_untyped
#eval do_step (:: i_untyped (:: (symbol "hi") nil)) true

#eval (step <=< step) <| :: s_untyped (:: k_untyped (:: k_untyped (:: (symbol "a") nil)))
#eval (step <=< step <=< step) <| :: (:: s_untyped (:: k_untyped (:: k_untyped nil))) (symbol "a")
#eval (step <=< step <=< step) <| :: i_untyped (:: (symbol "a") nil)

namespace church_example

def tre  := k_untyped
def flse := :: k_untyped (:: i_untyped nil)

#eval do_step (:: flse (:: i_untyped (:: (symbol "b") nil)))
#eval do_step (:: tre (:: i_untyped (:: (symbol "b") nil)))
  >>= (fun e => pure <| e == i_untyped)

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

def mk_church : ℕ → Option Expr
  | .zero => zero
  | .succ n =>
    match succ with
    | :: f (:: x nil) => do
      pure <| :: f (:: x (:: (← mk_church n) nil))
    | _ => .none

def my_test : Option Expr := do
  let t' ← match succ with
  | :: f (:: x nil) =>
    do_step <| :: f (:: x (:: zero (:: i_untyped nil)))
  | _ => .none
  do_step (:: t' (:: (symbol "hi") nil) )

def my_test' (n : Nat) : Option Expr := do
  let t' := (:: (← push_arg i_untyped (← mk_church n)) (:: (symbol "hi") nil))
  try_step_n 100 t'

def succ' : Expr :=
  let nfx := π read (π read (both head (:: const nil)))
  both (π nil head) (both nfx (:: const nil))

def zero' : Expr :=
  π nil head

#eval do_step (:: zero' (:: (symbol "f") (:: (symbol "x") nil)))
#eval do_step (:: (:: succ' (:: zero' nil)) (:: (symbol "f") (:: (:: (symbol "a") (:: (symbol "x") nil)) nil)))

def test_succ' : Option Expr :=
  let my_id := read
  do_step (:: (:: succ' (:: (:: succ' (:: zero' nil)) nil)) (:: my_id (:: (symbol "hi") nil))) true

#eval test_succ'

def test_succ'' : Option Expr :=
  let my_id := read
  let n := (:: succ' (:: (:: succ' (:: (:: succ' (:: zero' nil)) nil)) nil))
  do_step (:: n (:: my_id (:: (symbol "hi") nil)))

#eval test_succ''

def mk_church' (n : ℕ) : Option Expr :=
  match n with
  | .zero => zero'
  | .succ n => do
    let inner ← mk_church' n

    pure <| (:: succ' (:: inner nil))

def test_succ''' (n : ℕ) : Option Expr := do
  let my_id := read
  let n ← mk_church' n
  do_step (:: n (:: my_id (:: (symbol "hi") nil)))

#eval test_succ''' 3

def get_index (n : ℕ) (l : Expr) : Option Expr :=
  match n with
  | .zero => do_step (:: head l)
  | n => do
    do_step (:: (← mk_church' n) (:: (π nil read) (:: l nil))) true


#eval get_index 1 (:: (symbol "hi") (:: (symbol "a") (:: (symbol "b") nil)))

/-
λ m n f x => m f (n f x)
-/
def plus' : Expr :=
  π read succ'

#eval test_succ'' >>= do_step

#eval ToFormat.format <$> do_step (:: succ' (:: (symbol "n") (:: (symbol "f") (:: (symbol "x") nil)))) true

#eval ToFormat.format <$> my_test
#eval ToFormat.format <$> my_test' 1
-- (succ (succ zero)) I
#eval ToFormat.format <$> my_test' 2

#eval my_example

#eval ToFormat.format <$> do_step (:: (:: succ (:: zero nil)) (:: i_untyped (:: (symbol "hi") nil)))
#eval ToFormat.format <$> do_step (:: succ (:: zero (:: i_untyped (:: (symbol "hi") nil))))
#eval do_step (:: (:: succ (:: zero nil)) (:: i_untyped (:: (symbol "hi") nil)))
--#eval do_step (:: succ (:: zero (:: i_untyped (:: (symbol "hi") nil))))
--#eval do_step (:: (mk_church 0) (:: k_untyped (:: (symbol "hi") nil)))

end church_example
