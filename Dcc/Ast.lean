import Mathlib.Data.Nat.Notation

open Lean.Quote (quote)

abbrev Level := ℕ
abbrev Ident := String

/-
Normal SK
-/

inductive Comb where
  | mk : Ident → List Level → Comb
deriving BEq, Repr

inductive TAtom where
  | Sort  : Level → TAtom
  | Pi    : Level → Level → TAtom
deriving BEq, Repr

inductive Expr where
  | M       : Expr → Expr
  | comb    : Comb → Expr
  | TAtom   : TAtom → Expr
  | app     : Expr → Expr → Expr
deriving BEq, Repr

declare_syntax_cat op
declare_syntax_cat comb

syntax:max ident                        : comb
syntax:max ident  ".{" term "}"         : comb
syntax "Π" ".{" term "}"                : comb
syntax "M" comb                         : comb
syntax "Sort" term                       : comb
syntax:max "(" comb ")"                 : comb
syntax "_"                              : comb
syntax "#" term                         : comb
syntax op                               : comb

syntax:1022 comb:1022     comb:1023     : comb

syntax  "⟪" comb "⟫"     : term

macro_rules
  | `(⟪Sort $n⟫) => `(Expr.TAtom (TAtom.Sort $n))
  | `(⟪M $c:comb⟫) => `(Expr.M ⟪$c⟫)
  | `(⟪Π.{[$m, $n]}⟫) => `(Expr.TAtom (TAtom.Pi $m $n))
  | `(⟪($c:comb)⟫) => `(⟪$c:comb⟫)
  | `(⟪$c:ident.{$lvs:term}⟫) =>
    let name := c.getId
    let name_s := quote name.toString
    `((Expr.comb (Comb.mk $name_s:term $lvs:term)))
  | `(⟪$id:ident⟫) =>
    match id with
    | `(ident| $id) =>`($id:term)
  | `(⟪#$t:term⟫) => `($t)
  | `(⟪$f:comb $x:comb⟫) => `(Expr.app ⟪$f:comb⟫ ⟪$x:comb⟫)

#eval ⟪K'.{[1]}⟫
#eval ⟪K'.{[1, 2]}⟫

