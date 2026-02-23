import Mathlib.Data.Nat.Notation

/-
What if we want to extend dom / cod at runtime?
Will this become prohibitive?
No, because we're just using our type inference
to figure out what the next dom / cod will be.

dom / cod needs to not type-check for
things that aren't functions, though.
We could just add a symbol for this.
Unit or something.

We could, alternatively, use Pi.
Then, we don't need dom / cod.
We're just equating Pi.
-/

abbrev Level := ℕ

inductive Interval where
  | i₀ : Interval
  | i₁ : Interval
deriving BEq, Repr

inductive TAtom where
  | Unit  : TAtom
  | I     : TAtom
  | PathP : Level → TAtom
  | Eq    : Level → TAtom
  | Equiv : Level → TAtom
  | Set   : Level → TAtom
  | Pi    : Level → Level → TAtom
deriving BEq, Repr

inductive Expr where
  | M       : Expr → Expr
  | K       : Level → Level → Expr -- Dependent K
  | K'      : Level → Level → Expr -- Nondependent K
  | S       : Level → Level → Level → Expr -- Dependent S
  | TAtom   : TAtom → Expr
  | transp  : Expr
  | intvl   : Interval → Expr -- Interval components
  | hcomp   : Expr → Expr
  | app     : Expr → Expr → Expr
deriving BEq, Repr

declare_syntax_cat comb
syntax:max ident                        : comb
syntax:max comb  ".{" term,+ "}"        : comb
syntax "M" comb                         : comb
syntax "Π" ".{" term,+ "}"              : comb
syntax "="                              : comb
syntax "≃"                              : comb
syntax "Set" term                       : comb
syntax:max "(" comb ")"                 : comb
syntax "_"                              : comb
syntax "#" term                         : comb

syntax:1022 comb:1022     comb:1023     : comb

syntax  "⟪" comb "⟫"     : term

macro_rules
  | `(⟪Set $n⟫) => `(Expr.TAtom (TAtom.Set $n))
  | `(⟪M $c:comb⟫) => `(Expr.M ⟪$c⟫)
  | `(⟪$id:ident⟫) =>
    match id with
    | `(ident| I) => `(Expr.TAtom TAtom.I)
    | `(ident| K) => `(Expr.K)
    | `(ident| K') => `(Expr.K')
    | `(ident| S) => `(Expr.S)
    | `(ident| PathP) => `(Expr.TAtom TAtom.PathP)
    | `(ident| i₀) => `(Expr.intvl Interval.i₀)
    | `(ident| i₁) => `(Expr.intvl Interval.i₁)
    | `(ident| hcomp) => `(Expr.hcomp)
    | `(ident| transp) => `(Expr.transp)
    | `(ident| $id) =>`($id:term)
  | `(⟪=⟫) => `(Expr.TAtom TAtom.Eq)
  | `(⟪≃⟫) => `(Expr.TAtom TAtom.Equiv)
  | `(⟪($c:comb)⟫) => `(⟪$c:comb⟫)
  | `(⟪Π.{$m, $n}⟫) => `(Expr.TAtom (TAtom.Pi $m $n))
  | `(⟪$c.{$l:term}⟫) => `(⟪$c⟫ $l)
  | `(⟪$c.{$l:term, $lvs:term,*}⟫) => `(⟪$c.{$l}.{$lvs,*}⟫)
  | `(⟪#$t:term⟫) => `($t)
  | `(⟪$f:comb $x:comb⟫) => `(Expr.app ⟪$f:comb⟫ ⟪$x:comb⟫)

inductive IsStep : Expr → Expr → Prop
  | K     : IsStep ⟪K.{m, n} α β x y⟫ x
  | K'    : IsStep ⟪K'.{m, n} α β x y⟫ x
  | S     : IsStep ⟪S.{m, n, o} α β γ x y z⟫ ⟪(x z) (y z)⟫
  | left  : IsStep f f' → IsStep ⟪f x⟫ ⟪f' x⟫
  | right : IsStep x x' → IsStep ⟪f x⟫ ⟪f x'⟫
  | pi    : IsStep ⟪Π.{m, n} α β x⟫ ⟪β x⟫
  | k₁    : IsStep ⟪(M K.{m, n}) α⟫ ⟪Π.{n.succ, m} (Π.{m, n.succ}
    α (K'.{n.succ.succ, m} (Set n.succ) α (Set n)))
    (M (K.{m, n} α))⟫
  | k₂    : IsStep ⟪(M (K.{m, n} α)) β⟫ ⟪Π.{m, m} α (M (K.{m, n} α β))⟫
  | k₃    : IsStep ⟪(M (K.{m, n} α β)) x⟫ ⟪Π.{m, m} (β x) (M (K.{m, n} α β x))⟫
  | k₄    : IsStep ⟪(M (K.{m, n} α β x)) y⟫ α
