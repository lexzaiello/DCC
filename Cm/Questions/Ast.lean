import Mathlib.Data.Nat.Notation

/-
Since we have proven in SigmaCorr that:
- S is derivable from both and id
- Projection is universal (captures fst and snd)
  and is equivalent to application

Our AST can be quite minimal.
-/

inductive Expr where
  | app    : Expr → Expr → Expr
  | cons   : Expr → Expr → Expr
  | sigma  : Expr
  | π      : Expr
  | fst    : Expr
  | snd    : Expr
  | both   : Expr
  | const  : Expr
  | const' : Expr
  | id     : Expr
  -- downgrades a term to a type
  | nil    : Expr
  | ty     : Expr
  -- Notation for type of a sigma pair

syntax ident ".{" term,* "}"  : term
syntax "::[" term,+ "]"       : term
syntax "($" term,+ ")"        : term

macro_rules
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.cons $x ::[$xs,*])
  | `(($ $x:term) ) => `($x)
  | `(($ $f:term, $x:term )) => `(Expr.app $f $x)
  | `(($ $f, $x:term, $args:term,* )) =>
    `(($ (Expr.app $f $x), $args,*))

notation "Σ'" => Expr.sigma
notation "Ty" => Expr.ty

