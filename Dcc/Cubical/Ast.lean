import Mathlib.Data.Nat.Notation

abbrev Level := ℕ

inductive Interval where
  | i₀ : Interval
  | i₁ : Interval
deriving BEq, Repr

inductive MComb where
  | MK : Level → Level → MComb
  | MS : Level → Level → Level → MComb
deriving BEq, Repr

inductive MOp where
  | dom : Level → MOp
  | cod : Level → MOp
deriving BEq, Repr

inductive TAtom where
  | MComb : MComb → TAtom
  | I     : TAtom
  | PathP : Level → TAtom
  | Eq    : Level → TAtom
  | Equiv : Level → TAtom
  | Set   : Level → TAtom
deriving BEq, Repr

inductive Expr where
  | K       : Level → Level → Expr -- Dependent K
  | S       : Level → Level → Level → Expr -- Dependent S
  | TAtom   : TAtom → Expr
  | MOp     : MOp → Expr -- Manipulate meta meta combinators
  | transp  : Expr
  | intvl   : Interval → Expr -- Interval components
  | hcomp   : Expr → Expr
  | app     : Expr → Expr → Expr
deriving BEq, Repr

declare_syntax_cat comb
syntax ident                            : comb
syntax:max comb  ".{" term,+ "}"        : comb
syntax:max num                          : comb
syntax "="                              : comb
syntax "≃"                              : comb
syntax "Set" term                       : comb
syntax:max "(" comb ")"                 : comb
syntax "_"                              : comb
syntax "#(" term ")"                    : comb

syntax:1022 comb:1022     comb:1023     : comb

syntax  "⟪" comb "⟫"     : term

macro_rules
  | `(⟪Set $n⟫) => `(Expr.TAtom (TAtom.Set $n))
  | `(⟪$n:num⟫) => `($n:term)
  | `(⟪$id:ident⟫) =>
    match id with
    | `(ident| I) => `(Expr.TAtom TAtom.I)
    | `(ident| K) => `(Expr.K)
    | `(ident| S) => `(Expr.S)
    | `(ident| PathP) => `(Expr.TAtom TAtom.PathP)
    | `(ident| dom) => `(Expr.MOp MOp.dom)
    | `(ident| cod) => `(Expr.MOp MOp.cod)
    | `(ident| i₀) => `(Expr.intvl Interval.i₀)
    | `(ident| i₁) => `(Expr.intvl Interval.i₁)
    | `(ident| hcomp) => `(Expr.hcomp)
    | `(ident| transp) => `(Expr.transp)
    | `(ident| MK) => `(Expr.TAtom (TAtom.MComb MComb.MK))
    | `(ident| MS) => `(Expr.TAtom (TAtom.MComb MComb.MS))
    | id => `($id)
  | `(⟪=⟫) => `(Expr.TAtom TAtom.Eq)
  | `(⟪≃⟫) => `(Expr.TAtom TAtom.Equiv)
  | `(⟪($c:comb)⟫) => `(⟪$c:comb⟫)
  | `(⟪$f:comb $x:comb⟫) => `(Expr.app ⟪$f:comb⟫ ⟪$x:comb⟫)
  | `(⟪#($t:term)⟫) => `($t)
