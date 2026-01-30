import Mathlib.Data.Nat.Notation

abbrev Level := ℕ

inductive Expr where
  | app    : Expr → Expr → Expr
  | ty     : ℕ → Expr
  -- Sigmas ::[a, b]
  | cons   : Expr → Expr → Expr
  /-
    nil α x = α. Closes the loop of dependency in sigma.
    ::[α, nil α] x = α
  -/
  | nil    : Level → Expr
  /-
    Dependent and nondependent versions of K.
  -/
  | const  : Level → Level → Expr
  | const' : Level → Level → Expr
  /-
    Dependent and extra nondependent versions of S.
    both' does not accept β and γ arguments.
    both' is used inside sigma types to form expressions.
    both'.{[m, n, o]} α (f : α → Type n)
      (g : α → Type o)
      (x : α) : (Type (max n o)).succ
    both is the usual S combinator.
  -/
  | both   : Level → Level → Level → Expr
  | both'  : Level → Level → Level → Expr
  | id     : Level → Expr
deriving BEq, DecidableEq

syntax ident ".{" term,* "}" : term
syntax "::[" term,+ "]"      : term
syntax "($" term,+ ")"       : term
syntax (name := atDollar) "@$" term:max term:max term:max term:max term:max term:max : term

macro_rules
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.cons $x ::[$xs,*])
  | `(($ $x:term) ) => `($x)
  | `(($ $f:term, $x:term )) => `(Expr.app $f $x)
  | `(($ $f, $x:term, $args:term,* )) =>
    `(($ (Expr.app $f $x), $args,*))

notation "Ty" => Expr.ty

#eval ::[Ty 0, Ty 1, Ty 2]

inductive Error where
  | stuck        : Expr → Error
  | no_rule      : Expr → Error
  | mismatch_arg : Expr
    → Expr
    → Error
deriving BEq, DecidableEq

open Expr


