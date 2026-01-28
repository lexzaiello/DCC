import Mathlib.Data.Nat.Notation

open Std (Format)
open Std (ToFormat)
open Std.ToFormat (format)

abbrev Level := ℕ

inductive Expr where
  -- for debugging
  | symbol : String → Expr
  -- for projecting on cons
  -- for forming "lists"
  /-
    Cons doesn't need explicit type arguments, since it
    corresponds to uncurried apply, which doesn't take type arguments either.
  -/
  | cons   : Expr
  | app    : Expr → Expr → Expr
  -- type universe hierarchy
  | ty     : Level → Expr
  -- for forming cons types
  | unit   : Expr
  | nil    : Level → Expr -- nil {α : Type} : α → Ty m
  -- the core combinators: const, id, eq, both
  -- these have explicit universe level arguments
  | id     : Level → Expr
  | eq     : Level → Level → Expr
  -- dependent and nondependent const.
  | const  : Level → Level → Expr
  | const' : Level → Level → Expr
  -- Dependent and nondependent :: both, respectively
  | both   : Level → Level → Level → Expr
  | both'  : Level → Level → Level → Expr
  -- For bootstrapping types by running infer first. TODO: remove this once combinator types are determined
  | hole   : Expr
deriving BEq, DecidableEq, Repr

open Expr

syntax ident ".{" term,* "}" : term
syntax "::[" term,+ "]"      : term
syntax "($" term,+ ")"       : term
syntax (name := atDollar) "@$" term:max term:max term:max term:max term:max term:max : term

macro_rules
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.app (Expr.app Expr.cons $x) ::[$xs,*])
  | `(($ $x:term) ) => `($x)
  | `(($ $f:term, $x:term )) => `(Expr.app $f $x)
  | `(($ $f, $x:term, $args:term,* )) =>
    `(($ (Expr.app $f $x), $args,*))

#eval ::[symbol "a", symbol "b", symbol "c"]

notation "?" => Expr.hole
notation "Ty" => Expr.ty

inductive Error where
  | stuck        : Expr → Error
  | no_rule      : Expr → Error
  | mismatch_arg : Expr
    → Expr
    → Error
deriving BEq, DecidableEq

open Expr

/-
This pushes a value to the end of a list
that isn't nil delimited.
-/
def Expr.push (l with_val : Expr) : Option Expr :=
  match l with
  | ::[x, xs] => (::[x, ·]) <$>Expr.push xs with_val
  | .nil _m => .none
  | x => ::[x, with_val]

/-
Foldls cons'd pairs / lists
-/
def Expr.foldl! {α : Type} (f : α → Expr → α) (init : α) : Expr → α
  | ::[x, xs] => xs.foldl! f (f init x)
  | x => f init x

partial def Expr.fmt (e : Expr) : Format :=
  match e with
  | ::[x, xs] =>
    "::[" ++
      (.group
        <| .nest 2
        <| Format.joinSep
          (xs.foldl! (fun (acc : List Std.Format) e => acc ++ [(Expr.fmt e)]) [x.fmt])
          ((format ",") ++ Format.line))
    ++ "]"
  | .symbol s => .paren s!"symbol \"{s}\""
  | .hole => "_"
  | .app f x => "f$ " ++ (.group <| .nest 2 <| f.fmt.paren ++ .line ++ x.fmt.paren)
  | .eq m n => "eq.{" ++ [m, n].toString ++ "}"
  | .cons => "cons"
  | id m => "id.{" ++ [m].toString ++ "}"
  | const m n => "const.{" ++ [m, n].toString ++ "}"
  | const' m n => "const'.{" ++ [m, n].toString ++ "}"
  | both m n o => "both.{" ++ [m, n, o].toString ++ "}"
  | both' m n o => "both'.{" ++ [m, n, o].toString ++ "}"
  | .nil m => "nil.{" ++ [m].toString ++ "}"
  | unit => "Unit"
  | Ty n => s!"Ty {n}"

#eval ::[symbol "a", symbol "b", symbol "c"].fmt

def Error.fmt : Error → Format
  | .mismatch_arg expected actual => s!"expected {Expr.fmt expected} but found {Expr.fmt actual}"
  | .stuck e   => "got stuck evaluating: " ++ .line ++ e.fmt
  | .no_rule e => "no rule to evaluate: " ++ .line ++ e.fmt

instance Expr.instToFormat : ToFormat Expr where
  format := Expr.fmt

instance Error.instToFormat : ToFormat Error where
  format := Error.fmt

instance Error.isntToString : ToString Error where
  toString := toString ∘ Error.fmt

instance Expr.instToString : ToString Expr where
  toString := toString ∘ Expr.fmt

def unwrap_with {α : Type} (e : Error) (o : Option α) : Except Error α :=
  (o.map Except.ok).getD (.error e)

def Expr.head! : Expr → Expr
  | ::[a, _b] => a
  | e => e

def Expr.tail! : Expr → Expr
  | ::[_a, b] => b
  | e => e
