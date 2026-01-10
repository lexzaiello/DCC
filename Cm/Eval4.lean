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
  | quote  : Expr
    → Expr
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
  | .quote e => "quote " ++ e.fmt
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
  | :: x nil => do pure <| :: x val
  | :: x xs => do pure <| :: x (← push_back val xs)
  | _ => .none

def mk_app (f x : Expr) : Option Expr :=
  Expr.push_back (:: x nil) f

def mk_app' (f : Option Expr) (x : Expr) : Option Expr := do
  Expr.push_back (:: x nil) (← f)

notation "f*" => mk_app'
notation "f$" => mk_app

example : Expr.push_back (:: (symbol "zero") nil) (:: (symbol "succ") nil) =
  (:: (symbol "succ") (:: (symbol "zero") nil)) := rfl

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
  | :: (:: append a) b =>
    match (step'' a).getD a, (step'' b).getD b with
    | a@(:: x xs), b =>
      Expr.push_back b a
    | v, b => :: (:: append v) b
  | :: .read (:: x xs) => pure x
  | :: (:: .const x) _l => pure x
  | :: (:: next f) (:: _x nil) => .none
  | :: (:: next f) (:: _x xs) => step'' (:: f xs) with_logs
  | :: b@(both f nil) l@(:: _x _xs) => do
    match step'' (:: f l) with_logs with
    | .some f' =>
      :: f' nil
    | .none => do
      both (← mk_append f l) nil
  | :: b@(both f g) l@(:: _x _xs) => do
    match step'' (:: f l) with_logs, step'' (:: g l) with_logs with
    | .some f', .some g' =>
      :: f' g'
    | .some f', .none => do
      both (:: const f') (← mk_append g l)
    | .none, .some g' => do
      both (← mk_append f l) (:: const g')
    | .none, .none => .none
  | :: f x => (do pure <| :: (← step'' f) (← step'' x)) <|> (do pure <| :: (← step'' f) x) <|> (do pure <| :: f (← step'' x))
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
    pure <| :: f' x)
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

def succ.n : Expr := read

def succ.f : Expr :=
  (:: next read)

def succ.x : Expr :=
  (:: next (:: next read))

def succ.fx : Expr :=
  (:: next (both read (:: next read)))

def succ.nfx : Expr :=
  (both succ.n succ.fx)

/-
Big note:
order of operations.

We need to sequence these in a smarter way.

Or we could just encode succ in a smarter way.

Both seems problematic in general.
There is no notion of sequence.

Why can't we just wrap nfx in nil?
Why can't we just eval what's inside read?

Maybe the problem is that zero doesn't have its function?
-/
def succ : Expr :=
  (both succ.f (both succ.nfx nil))

/-
zero f x = x
-/
def zero : Expr :=
  (:: next read)

--#eval ToFormat.format <$> do_step (step'' (with_logs := true)) (:: (:: append (:: succ (:: zero nil))) (:: read (:: (:: (symbol "x") (:: (symbol "y") nil)) nil)))
--#eval do_step step'' (:: (:: append (:: succ (:: zero nil))) (:: read (:: (:: (symbol "hi") nil) nil)))
#eval do_step (step'' (with_logs := true)) (:: succ (:: zero (:: read (:: (:: (symbol "hi") nil) nil))))
#eval do_step (step'' (with_logs := true)) =<< (f$ (:: succ (:: zero (:: read nil))) (:: (symbol "hi") nil))
#eval do_step (step'' (with_logs := true)) =<< (f* (f$ (:: succ (:: zero nil)) read) (:: (symbol "hi") nil))
#eval ToFormat.format <$> (do_step ((step'' <=< step'' (with_logs := true))) =<< (f* (f* (:: succ (:: zero nil)) read) (:: (symbol "hi") nil)))
#eval do_step (step'' (with_logs := true)) (:: (:: append (:: succ (:: zero (:: read nil))))
  (:: (:: (symbol "hi") nil) nil))
#eval do_step (step'' (with_logs := true)) (:: (:: append (:: (:: append (:: succ (:: zero nil)))
  (:: read nil))) (:: (:: (symbol "hi") nil) nil))
#eval do_step (step'' (with_logs := true)) (:: (:: append (:: (:: append (:: succ (:: zero nil)))
  (:: (:: (symbol "hi") nil) nil))) (:: read nil))
#eval do_step (step'' (with_logs := true)) (:: (:: append (:: succ (:: zero nil)))
  (:: (:: (symbol "hi") nil) nil))
#eval do_step (step'' (with_logs := true)) (::
  (:: append (:: (:: append (:: succ (:: zero nil))) (:: read nil)))
  (:: (:: (symbol "hi") nil) nil))
#eval do_step (step'' (with_logs := true)) (::
  (:: succ (:: zero nil))
  (:: read (:: (:: (symbol "hi") nil) nil)))
#eval do_step step'' (:: zero (:: read (:: (:: (symbol "hi") nil) nil)))

#eval do_step step'' (:: (:: next read) (:: read (:: (:: (symbol "hi") nil) nil)))

def test_succ'' (f : Expr → Option Expr) : Option Expr :=
  let my_id := read

  do_step f (:: succ (:: zero (:: my_id (:: (:: (symbol "hi") nil) nil)))) true

def test_succ_next (f : Expr → Option Expr) : Option Expr :=
  let my_f := (:: next read)
  do_step f (:: (:: append (:: succ (:: zero nil))) (:: (symbol "f") (:: (:: (symbol "hi") (:: (symbol "b") nil)) nil))) true

#eval do_step step'' (:: (:: append (:: succ (:: (:: succ (:: zero nil)) nil))) (:: (symbol ("f")) (:: (:: (symbol "hi") (:: (symbol "b") (:: (symbol "c") nil))) nil))) true

#eval ToFormat.format <$> test_succ_next (step'' (with_logs := true))

def test_succ_curry (f : Expr → Option Expr) : Option Expr :=
  let my_id := read

  do_step f (:: (:: succ zero) (:: my_id (:: (:: (symbol "hi") (:: (symbol "b") nil)) nil))) true

#eval do_step (step'' (with_logs := true)) (:: succ (:: zero nil))
#eval test_succ_curry (step'' (with_logs := true))

def test_succ'''' (f : Expr → Option Expr) : Option Expr :=
  let my_id := read

  let n := (:: succ (:: zero nil))

  (push_back (:: my_id (:: (:: (symbol "hi") nil) nil)) n) >>= do_step f

#eval do_step step'' (:: succ (:: zero nil))
#eval test_succ'''' step''

#eval test_succ'' step''

def mk_church' (n : ℕ) : Option Expr :=
  match n with
  | .zero => zero
  | .succ n => do
    let inner ← mk_church' n

    pure <| (:: append (:: succ inner))

def test_succ_next (n : ℕ) : Option Expr := do
  let my_id := read
  let n ← mk_church' n
  do_step step'' (:: n (:: next (:: (:: (symbol "hi") (:: (symbol "hi") nil)) nil)))

#eval test_succ_next 1

def get_index (n : ℕ) (l : Expr) : Option Expr :=
  match n with
  | .zero => do_step step'' (:: read l)
  | n => do
    do_step step'' (:: (← mk_church' n) (:: next (:: (:: l nil) nil)))

#eval get_index 1 (:: (symbol "hi") (:: (symbol "a") (:: (symbol "b") nil)))
