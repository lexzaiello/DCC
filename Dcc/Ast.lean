import Mathlib.Data.Nat.Notation
import Mathlib.Tactic
import Lean

open Lean.Meta (registerSimpAttr)
open Lean.Meta (SimpExtension)


open Lean.Quote (quote)

abbrev Level := ℕ
abbrev Ident := String

/-
Normal SK
-/

inductive Comb where
  | K  : Level → Level → Comb
  | K' : Level → Level → Comb
  | S  : Level → Level → Level → Comb
   -- γ argument for S type:
  | Sγ : Level → Level → Level → Comb
  -- f argument for S type:
  | Sf : Level → Level →  Level → Comb
deriving BEq, Repr

inductive Ty where
  | Sort  : Level → Ty
  | Pi    : Level → Level → Ty
deriving BEq, Repr

inductive Expr where
  | M       : Expr → Expr
  | comb    : Comb → Expr
  | ty      : Ty    → Expr
  | app     : Expr → Expr → Expr
deriving BEq, Repr

declare_syntax_cat comb

syntax:max ident                   : comb
syntax "Sγ.{" term "}"             : comb
syntax "Sf.{" term "}"             : comb
syntax "K.{" term "}"              : comb
syntax "K'.{" term "}"             : comb
syntax "S.{" term "}"              : comb
syntax "Π.{" term "}"              : comb
syntax "M" comb                    : comb
syntax "Sort" term                 : comb
syntax:max "(" comb ")"            : comb
syntax "_"                         : comb
syntax "#" term                    : comb

syntax:1022 comb:1022     comb:1023     : comb

syntax  "⟪" comb "⟫"     : term

macro_rules
  | `(⟪Sort $n⟫) => `(Expr.ty (Ty.Sort $n))
  | `(⟪M $c:comb⟫) => `(Expr.M ⟪$c⟫)
  | `(⟪Π.{[$m, $n]}⟫) => `(Expr.ty (Ty.Pi $m $n))
  | `(⟪($c:comb)⟫) => `(⟪$c:comb⟫)
  | `(⟪K.{[$m:term, $n:term]}⟫) => `(Expr.comb (Comb.K $m $n))
  | `(⟪K'.{[$m:term, $n:term]}⟫) => `(Expr.comb (Comb.K' $m $n))
  | `(⟪S.{[$m, $n, $o]}⟫) => `(Expr.comb (Comb.S $m $n $o))
  | `(⟪Sγ.{[$m, $n, $o]}⟫) => `(Expr.comb (Comb.Sγ $m $n $o))
  | `(⟪Sf.{[$m, $n, $o]}⟫) => `(Expr.comb (Comb.Sf $m $n $o))
  | `(⟪$id:ident⟫) =>
    match id with
    | `(ident| $id) =>`($id:term)
  | `(⟪#$t:term⟫) => `($t)
  | `(⟪$f:comb $x:comb⟫) => `(Expr.app ⟪$f:comb⟫ ⟪$x:comb⟫)

#eval ⟪K'.{[1, 2]}⟫
#eval ⟪K'.{[1, 2]}⟫
