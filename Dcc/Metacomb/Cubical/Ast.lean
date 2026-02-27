import Dcc.Ast
import Mathlib.Data.Nat.Notation

open Lean.Quote (quote)

/-
Cubical stuff
-/

inductive Interval where
  | i0 : Interval
  | i1 : Interval
deriving BEq, Repr

inductive CAtom where
  | PathP : Level → CAtom
  | Eq    : Level → CAtom
  | Equiv : Level → CAtom

inductive CExpr where
  | I       : CExpr
  -- I → α
  | Dim     : CExpr    → CExpr
  | intvl   : Interval → CExpr
  | min     : CExpr
  | max     : CExpr
  | rev     : CExpr
  | hcomp   : CExpr → CExpr
  | M       : CExpr → CExpr
  | comb    : Comb  → CExpr
  | TAtom   : TAtom → CExpr
  | CAtom   : CAtom → CExpr
  | app     : CExpr → CExpr → CExpr

syntax:max "I" "→" comb : comb
syntax:max "="  ".{" term "}"           : comb
syntax:max "≃"  ".{" term "}"           : comb
syntax "I"                              : comb
syntax "="                              : comb
syntax "≃"                              : comb
syntax "∧"                              : comb
syntax "∨"                              : comb
syntax "~"                              : comb

syntax  "c⟪" comb "⟫"    : term

macro_rules
  | `(c⟪Sort $n⟫) => `(CExpr.TAtom (TAtom.Sort $n))
  | `(c⟪M $c:comb⟫) => `(CExpr.M ⟪$c⟫)
  | `(c⟪PathP.{[$m]}⟫) => `(CExpr.CAtom (CAtom.PathP $m))
  | `(c⟪∧⟫) => `(CExpr.min)
  | `(c⟪∨⟫) => `(CExpr.max)
  | `(c⟪~⟫) => `(CExpr.rev)
  | `(c⟪=.{[$m]}⟫) => `(CExpr.CAtom (CAtom.Eq $m))
  | `(c⟪≃.{[$m]}⟫) => `(CExpr.CAtom (CAtom.Equiv $m))
  | `(c⟪Π.{[$m, $n]}⟫) => `(CExpr.TAtom (TAtom.Pi $m $n))
  | `(c⟪($c:comb)⟫) => `(c⟪$c:comb⟫)
  | `(c⟪$c:ident.{$lvs:term}⟫) =>
    let name := c.getId
    let name_s := quote name.toString
    `((CExpr.comb (Comb.mk $name_s:term $lvs:term)))
  | `(c⟪$id:ident⟫) =>
    match id with
    | `(ident| i0) => `(CExpr.intvl Interval.i0)
    | `(ident| i1) => `(CExpr.intvl Interval.i1)
    | `(ident| hcomp) => `(CExpr.hcomp)
    | `(ident| $id) =>`($id:term)
  | `(c⟪I⟫) => `(CExpr.I)
  | `(c⟪I → $e:comb⟫) => `(CExpr.Dim ⟪$e⟫)
  | `(c⟪#$t:term⟫) => `($t)
  | `(c⟪$f:comb $x:comb⟫) => `(CExpr.app c⟪$f:comb⟫ c⟪$x:comb⟫)

def i0.type : CExpr := c⟪I⟫
def i1.type : CExpr := c⟪I⟫

def path.type (A α β : CExpr) (l : Level) : CExpr := c⟪PathP.{[l]} A α β⟫

/-
KI α x i = x
-/
def refl (m : Level) : CExpr := c⟪KI.{[m]}⟫


