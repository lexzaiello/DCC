import Mathlib.Data.Nat.Notation
import Cm.EvalUtil

open Std (Format)
open Std (ToFormat)
open Std.ToFormat (format)

inductive Expr where
  | cons   : Expr
    → Expr
    → Expr
  | apply  : Expr
  | π      : Expr
  | id     : Expr
  | const  : Expr
  | both   : Expr
  | nil    : Expr
  | symbol : String
    → Expr
deriving Repr, BEq

inductive Error where
  | stuck      : Expr → Error
  | no_rule    : Expr → Error
  | cant_curry : Expr → Error

open Expr

def Expr.fmt (e : Expr) : Format :=
  match e with
  | .apply => "apply"
  | .π => "π"
  | .cons (.cons a b) (.cons c d) =>
    ":: " ++ (.group <| .nest 2 <| (.paren (Expr.cons a b).fmt) ++ Format.line ++ (.paren (Expr.cons c d).fmt))
  | .cons (.cons a b) xs =>
    ":: " ++ (.group <| .nest 2 <| (.paren (Expr.cons a b).fmt) ++ Format.line ++ xs.fmt)
  | .cons x (.cons a b) =>
    ":: " ++ (.group <| .nest 2 <| x.fmt ++ Format.line ++ (.paren (Expr.cons a b).fmt))
  | .cons x xs =>
    ":: " ++ (.group <| .nest 2 <| x.fmt ++ Format.line ++ xs.fmt)
  | id => "id"
  | .const => "const"
  | .both => "both"
  | .nil => "nil"
  | symbol s => .paren ("symbol " ++ ("\"" ++ s ++ "\""))

def Error.fmt : Error → Format
  | .stuck e => "got stuck evaluating: " ++ .line ++ e.fmt
  | .cant_curry e => "couldn't curry: " ++ .line ++ e.fmt
  | .no_rule e => "no rule to evaluate: " ++ .line ++ e.fmt

instance Expr.instToFormat : ToFormat Expr where
  format := Expr.fmt

instance Error.instToFormat : ToFormat Error where
  format := Error.fmt

instance Error.isntToString : ToString Error where
  toString := toString ∘ Error.fmt

instance Expr.instToString : ToString Expr where
  toString := toString ∘ Expr.fmt

notation "::" => Expr.cons

/-
Wraps f and x as singleton values,
then applies.
-/
def mk_apply_now (f x : Expr) : Expr :=
  :: apply (:: (:: f nil) (:: (:: x nil) nil))

notation "f$" => mk_apply_now

/-
Singleton values: how necessary are they?
Should π work on singletons or actual lists?
-/

def step_apply (e : Expr) (with_logs : Bool := false) : Except Error Expr := do
  if with_logs then
    dbg_trace e

  match e with
  | :: .id x => pure x
  | :: (:: π (:: a nil)) (:: x nil) =>
    pure <| :: (:: apply (:: (:: a nil) x)) nil
  | :: (:: π (:: a b)) (:: x xs) => do
    let a' := :: apply (:: (:: a nil) x)
    let b' := :: apply (:: (:: b nil) xs)

    pure <| :: a' b'
  | :: (:: const (:: x nil)) _ => pure x
  | :: (:: both (:: f g)) l =>
    pure <| :: (:: apply (:: (:: f nil) l)) (:: apply (:: (:: g nil) l))
  | e => .error <| .no_rule e

def run (e : Expr) (with_logs : Bool := false) : Except Error Expr := do
  if with_logs then
    dbg_trace e

  /-
    If this instruction can be done without nested applications, do it.
    Otherwise, handle the applications.
  -/
  /-
    Applications can happen at the top level,
    or they can be deeply nested.
    We will assume that applications have the
    requisite arguments.
  -/
  match e with
  /-
    Apply calls accept a function and an arguments list.
    NOTE: apply should always have the function as a singleton
    so as to be clear.
  -/
  | :: apply (:: (:: f nil) x) => do
    let eval_arg_first : Except Error Expr := do
      let x' ← run x
      pure <| :: apply (:: (:: f nil) x')
    let eval_f_first : Except Error Expr := do
      let f' ← run f
      pure <| :: apply (:: (:: f' nil) x)
    let step_whole : Except Error Expr := do
      step_apply (:: f x) with_logs

    eval_arg_first <|> eval_f_first <|> step_whole
  | :: x xs => (do
    let x' ← run x with_logs
    let xs' ← run xs with_logs
    pure <| :: x' xs') <|> (do
    let xs' ← run xs with_logs
    pure <| :: x xs') <|> (do
    let x' ← run x with_logs
    pure <| :: x' xs)
  | e => .error <| .no_rule e

def apply_later : Expr :=
  (:: const (:: apply nil))

/-
Skips the tail element in a projection.
-/
def skip : Expr :=
  (:: const (:: nil nil))

/-
Notes on this design:
- we expect that all values with no arguments are singleton lists. e.g.,
(symbol "hi") is incorrect. (:: (symbol "hi") nil) is correct.
-/

namespace church

def singleton_later : Expr :=
  :: both (:: id (:: const (:: nil nil)))

/-
zero f x = x
(:: zero (:: (:: (symbol "f") nil) (:: (:: (symbol "x") nil) nil)))
== (:: (symbol "x") nil)
-/
def zero : Expr :=
  :: both (:: apply_later <| (:: π (:: (:: const (:: (:: id nil) nil)) (:: π (:: id nil)))))

/-
zero, but it doesn't stop at the second argumnet.
discards all after f.
-/
def succ.f_root : Expr :=
  :: both (:: apply_later <| (:: π (:: (:: const (:: (:: id nil) nil)) (:: π (:: id (:: const (:: nil nil)))))))

#eval do_step run (:: apply (:: (:: zero nil) (:: (symbol "f") (:: (symbol "x") nil))))

/-
succ n f x = f (n f x)

n is in position 0,
f is in position 1,
and x is in position 2

zero has a similar signature, so we can use
it to get f.

The rest is essentially in the order we got
the expression, just pattern matching
to ensure we got the right number of arguments,
and inserting an apply.
-/

#eval do_step (run (with_logs := true)) (:: (:: π (:: id (:: π (:: id nil)))) (:: (symbol "a") (:: (symbol "b") nil)))

def succ.select_nfx : Expr :=
  (:: π (:: singleton_later (:: π (:: id (:: π (:: id nil))))))

#eval do_step (run (with_logs := true)) (:: apply (:: (:: succ.select_nfx nil) (:: (symbol "n") (:: (symbol "f") (:: (symbol "x") nil)))))

def succ.nfx : Expr :=
  :: both (:: apply_later succ.select_nfx)

#eval do_step (run (with_logs := true)) (:: apply (:: (:: succ.nfx nil) (:: (symbol "n") (:: (symbol "f") (:: (symbol "x") nil)))))

/-
The entire succ also needs an apply,
since f (n(f, x))
-/
def succ : Expr :=
  :: both (:: apply_later (:: both (:: succ.f_root succ.nfx)))

#eval do_step run (:: apply (:: (:: succ nil) (:: (symbol "n") (:: (symbol "f") (:: (symbol "x") nil)))))

end church

namespace tests

open church

/-
succ zero =>
:: apply (:: (:: (symbol "f") nil) (:: (symbol "x") nil))

Looks perfect.
-/
#eval do_step run (:: apply (:: (:: succ nil) (:: zero (:: (symbol "f") (:: (symbol "x") nil)))))

/-
succ zero (const (const "f")) "x" => (const (symbol "f"))
-/
#eval do_step run (:: apply (:: (:: succ nil) (:: zero (:: (:: const (:: (:: const (:: (symbol "f") nil)) nil)) (:: (symbol "x") nil)))))

end tests

/-
prepend with_val onto

π (:: both (:: const (:: both nil)) id) id

π (:: both id prepend_to) nil
-/
def prepend : Expr :=
  :: π (:: (:: both (:: (:: const (:: both nil)) id)) id)

namespace curry

/-
Combines a list of arguments with a single argument / partial application.

(curry (:: f x) (:: arg₁ ...)) = (:: f nil) (:: x (:: arg₁ ...))
-/
def curry_easy : Expr :=
  -- strip args from f
  -- gives :: f nil
  let f_bare := (:: π (:: (:: π (:: id (:: const (:: nil nil)))) (:: const (:: nil nil))))

  -- get just x argument from (:: f x)
  -- :: x nil
  let x_app := church.zero
  let rst := Expr.id

  -- how to nicely prepend x_app?
  -- both (:: const (:: x_app_val nil)) id

  Expr.cons both (:: apply_later (:: both (:: f_bare (:: π (:: x_app rst)))))

#eval do_step run
  (::
    apply
    (::
      (:: curry_easy nil)
      (::
        (:: (symbol "f") (:: (symbol "x") nil))
        (:: (:: (symbol "arg₁") nil) nil))))

def n_arguments_π : Expr → Except Error ℕ
  | :: π (:: _a nil) => pure 1
  | const => pure 1
  | (:: const (:: _v nil)) => pure 1
  | .id => pure 1
  | :: both (:: f g) => do
    let n_f ← (n_arguments_π f)
    let n_g ← (n_arguments_π g)
    pure <| max n_f n_g
  | symbol _s
  | nil => pure 0
  | :: π (:: _a b) => do pure <| 1 + (← n_arguments_π b)
  | apply => .error <| .cant_curry apply
  | e => .error <| .cant_curry e

#eval n_arguments_π church.zero

/-
  In a curried π a b call,
  a must be applied to the current argument and inserted as
  a const.
  :: (both (:: const (:: const nil)) a) arg =
      ((:: const (:: const nil)) arg) (a arg)
      const (:: a arg)
-/
def π.const_a_call (a : Expr) : Expr :=
  :: both (:: (:: const (:: const nil)) a)

/-
:: const (:: apply (:: (:: (symbol "a") nil) (:: (symbol "arg") nil)))
-/
#eval do_step run (:: apply (:: (:: (π.const_a_call (symbol "a")) nil) (:: (symbol "arg") nil)))

/-
curr only does one round of currying.
(curr f)(x)

The next argument it expects is the remaining arguments.
So, we are just cons'ing our immediate argument.
-/

/-def curr : Expr :=
  let my_f := π id nil
  let my_arg := π (:: const (:: (:: id nil) nil)) (π id nil)

  -- const both is like currying?
  both (:: const -/

end curry
