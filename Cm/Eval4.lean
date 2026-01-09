import Mathlib.Data.Nat.Notation

open Std (Format)
open Std (ToFormat)

inductive Expr where
  | nat    : ℕ
    → Expr
  | cons   : Expr
    → Expr
    → Expr
  | next   : Expr
  | read   : Expr
  | π      : Expr
    → Expr
    → Expr
  | const  : Expr
  | append : Expr
  | both   : Expr
    → Expr
    → Expr
  | nil    : Expr
  | symbol : String
    → Expr
deriving Repr, BEq

def Expr.fmt (e : Expr) : Format :=
  match e with
  | .append => "append"
  | .π f g => .paren ("π " ++ f.fmt ++ Format.line ++ g.fmt)
  | .next => "next"
  | .nat n => ToFormat.format n
  | .cons (.cons a b) (.cons c d) =>
    ":: " ++ (.group <| .nest 2 <| (.paren (Expr.cons a b).fmt) ++ Format.line ++ (.paren (Expr.cons c d).fmt))
  | .cons (.cons a b) xs =>
    ":: " ++ (.group <| .nest 2 <| (.paren (Expr.cons a b).fmt) ++ Format.line ++ xs.fmt)
  | .cons x (.cons a b) =>
    ":: " ++ (.group <| .nest 2 <| x.fmt ++ Format.line ++ (.paren (Expr.cons a b).fmt))
  | .cons x xs =>
    ":: " ++ (.group <| .nest 2 <| x.fmt ++ Format.line ++ xs.fmt)
  | .read => "read"
  | .const => "const"
  | .both f g => .paren ("both " ++ (.group <| .nest 2 <| (.paren f.fmt) ++ Format.line ++ (.paren g.fmt)))
  | .nil => "nil"
  | symbol s => .paren ("symbol " ++ ("\"" ++ s ++ "\""))

instance Expr.instToFormat : ToFormat Expr where
  format := Expr.fmt

instance Expr.instToString : ToString Expr where
  toString := toString ∘ Expr.fmt

open Expr

notation "::" => Expr.cons

/-
We should design step with deref in mind.
But, this clashes with K for example.

We want to be able just curry nicely,
but then we can't distinguish K discarding its argument.
-/

def Expr.push_back (val : Expr) : Expr → Option Expr
  | nil => val
  | :: x xs => do pure <| :: x (← push_back val xs)
  | _ => .none

def advance (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if with_logs then
    dbg_trace e
  match e with
  | :: (:: append a) b => Expr.push_back b a
  | :: (:: next f) (:: _x xs) => advance (:: f xs)
  | :: .read (:: x _xs) => pure x
  | :: (:: .const x) _l => pure x
  | :: (both f g) l => do
    :: (← advance (:: f l)) (← advance (:: g l))
  | _ => .none

/-
Potentially nicer way than push_back:
Create a new lambda function that concats
the new argument to the old args

both (:: const g) append
-/

def advance' (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if with_logs then
    dbg_trace e
  match e with
  | :: (:: append a) b => Expr.push_back b a
  | :: (:: next f) (:: _x xs) => advance' (:: f xs)
  | :: .read (:: x _xs) => pure x
  | :: (:: .const x) _l => pure x
  | _ => .none

def step'' (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if with_logs then
    dbg_trace e

  let mk_append (f args : Expr) : Option Expr :=
    both (:: const f) (:: append args)

  match e with
  | :: _ nil => .none
  | :: (:: append a) b => Expr.push_back b a
  | :: .read (:: x _xs) => pure x
  | :: (:: .const x) _l => pure x
  | :: (:: next f) (:: _x nil) => .none
  | :: (:: next f) (:: _x xs) => step'' (:: f xs) with_logs
  | :: (both f g) l => do
    match step'' (:: f l), step'' (:: g l) with
    | .some f', .some g' =>
      :: f' g'
    | .some f', .none => do
      both (:: const f') (← mk_append g l)
    | .none, .some g' => do
      both (← mk_append f l) (:: const g')
    | .none, .none => .none
  | :: f x => (do
    (do pure <| :: (← step'' f) (← step'' x))) <|>
      (do pure <| :: (← step'' f) x) <|> (do pure <| :: f (← step'' x))
  | _ => .none

#eval step'' (:: (both read (:: next read)) (:: (symbol "a") nil))
  >>= (fun e => step'' (:: e (:: (symbol "b") nil)))
  >>= step''

def step' (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if with_logs then
    dbg_trace e
  match e with
  | :: (both f g) l => do
    match advance (:: f l), advance (:: g l) with
    | .some f', .some g' =>
      :: f' g'
    | .some f', .none =>
      :: (both (:: const f') g) l
    | .none, .some g' =>
      :: (both f (:: const g')) l
    | .none, .none => .none
  | :: f x => advance e <|> (do
    let f' ← step' f
    pure <| :: f' x) <|> Expr.push_back x f
  | _ => .none

def step (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if with_logs then
    dbg_trace e
  match e with
  | :: (:: next f) (:: _x nil) => pure f
  | :: (:: next f) (:: _x xs) => step (:: f xs)
  | :: (both (:: next f) (:: next g)) (:: _x nil) =>
    pure <|  both f g
  | :: (both f (:: next g)) (:: x nil) => do
    let f' ← step (:: f (:: x nil))
    both (:: const f') g
  | :: (both (:: next f) g) (:: x nil) => do
    let g' ← step (:: g (:: x nil))
    both f (:: const g')
  | :: (both a b) l => do
    :: (← step (:: a l)) (← step (:: b l))
  | :: .read (:: x _xs) => pure x
  | :: (:: .const x) _l => pure x
  | :: f x => do
    let f' ← step f
    pure <| :: f' x
  | _ => .none

def try_step_n (f : Expr → Option Expr) (n : ℕ) (e : Expr) (with_logs : Bool := false) : Option Expr := do
  if n = 0 then
    pure e
  else
    let e' ← f e
    (try_step_n f (n - 1) e' with_logs) <|> (pure e')

def do_step (f : Expr → Option Expr) (e : Expr) (with_logs : Bool := false):= try_step_n f 20 e with_logs

/-
succ n f x = f (n f x)
-/
def succ : Expr :=
  let n := read
  let f := (:: next read)
  let x := (:: next (:: next read))

  let fx  := (both f (both x (:: const nil)))
  let nfx := (both (both n fx) (:: const nil))

  (both f nfx)

/-
zero f x = x
-/
def zero : Expr :=
  (:: next read)

def test_succ'' (f : Expr → Option Expr) : Option Expr :=
  let my_id := read

  do_step f (:: succ (:: zero (:: my_id (:: (:: (symbol "hi") nil) nil)))) true

def test_succ'''' (f : Expr → Option Expr) : Option Expr :=
  let my_id := read

  do_step f (:: (:: succ (:: zero nil)) (:: my_id (:: (:: (symbol "hi") nil) nil)))

#eval test_succ'''' step''

#eval test_succ'' step''

def mk_church' (n : ℕ) : Option Expr :=
  match n with
  | .zero => zero
  | .succ n => do
    let inner ← mk_church' n

    pure <| (:: succ (:: inner nil))

def test_succ''' (n : ℕ) : Option Expr := do
  let my_id := read
  let n ← mk_church' n
  do_step step' (:: n (:: next (:: (:: (symbol "hi") (:: (symbol "hi") nil)) nil)))

#eval test_succ''' 1

def get_index (n : ℕ) (l : Expr) : Option Expr :=
  match n with
  | .zero => do_step step' (:: read l)
  | n => do
    try_step_n step' 100 (:: (← mk_church' n) (:: next nil))


#eval get_index 1 (:: (symbol "hi") (:: (symbol "a") (:: (symbol "b") nil)))
