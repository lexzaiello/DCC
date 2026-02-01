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
  /- List-like objects
     They come with built-in projection.
     They are the mirror image of application "as data". -/
  | cons   : Expr → Expr → Expr
  /-
    ::[x, xs] lists are a special case. They are the mirror
    image of application as data. They internalize a projector
    argument π.
  -/
  | prod   : Expr → Expr → Expr
  /-
    Our representation of curried function types.
  -/
  | sigma  : Expr → Expr
  | both   : Expr
  | const  : Expr
  | const' : Expr
  | id     : Expr
  -- downgrades a term to a type
  | nil    : Expr
  | ty     : Expr

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

notation "Ty" => Expr.ty


