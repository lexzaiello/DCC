import Mathlib.Data.Nat.Notation

/-
TODO: dependent pairs.
-/

open Lean.Quote (quote)

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
abbrev Ident := String

inductive Interval where
  | i0 : Interval
  | i1 : Interval
deriving BEq, Repr

inductive Comb where
  | mk : Ident → List Level → Comb
deriving BEq, Repr

inductive TAtom where
  | Unit  : TAtom
  | PathP : Level → TAtom
  | Eq    : Level → TAtom
  | Equiv : Level → TAtom
  | Set   : Level → TAtom
  | Pi    : Level → Level → TAtom
deriving BEq, Repr

inductive Expr where
  | I       : Expr
  | M       : Expr → Expr
  | comb    : Comb → Expr
  | TAtom   : TAtom → Expr
  | intvl   : Interval → Expr -- Interval components
  | hcomp   : Expr → Expr
  | app     : Expr → Expr → Expr
deriving BEq, Repr

declare_syntax_cat comb
syntax:max ident                        : comb
syntax:max ident  ".{" term "}"         : comb
syntax:max "="  ".{" term "}"           : comb
syntax:max "≃"  ".{" term "}"           : comb
syntax "Π" ".{" term "}"                : comb
syntax "M" comb                         : comb
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
  | `(⟪PathP.{$m}⟫) => `(Expr.TAtom (TAtom.PathP $m))
  | `(⟪=.{[$m]}⟫) => `(Expr.TAtom (TAtom.PathEq $m))
  | `(⟪≃.{[$m]}⟫) => `(Expr.TAtom (TAtom.Equiv $m))
  | `(⟪Π.{[$m, $n]}⟫) => `(Expr.TAtom (TAtom.Pi $m $n))
  | `(⟪($c:comb)⟫) => `(⟪$c:comb⟫)
  | `(⟪$c:ident.{$lvs:term}⟫) =>
    let name := c.getId
    let name_s := quote name.toString
    `((Expr.comb (Comb.mk $name_s:term $lvs:term)))
  | `(⟪$id:ident⟫) =>
    match id with
    | `(ident| I) => `(Expr.I)
    | `(ident| i0) => `(Expr.intvl Interval.i0)
    | `(ident| i1) => `(Expr.intvl Interval.i1)
    | `(ident| hcomp) => `(Expr.hcomp)
    | `(ident| $id) =>`($id:term)
  | `(⟪#$t:term⟫) => `($t)
  | `(⟪$f:comb $x:comb⟫) => `(Expr.app ⟪$f:comb⟫ ⟪$x:comb⟫)

#eval ⟪K'.{[1]}⟫
#eval ⟪K'.{[1, 2]}⟫

def α_to_set (α : Expr) (m n : Level) : Expr :=
  ⟪(Π.{[m, n.succ.succ]}
    α (K'.{[n.succ.succ, m]} (Set n.succ) α (Set n)))⟫

def βx_to_set (β x : Expr) (n o : Level) : Expr :=
  ⟪(Π.{[n, o.succ.succ]} (β x) (K'.{[o.succ.succ, n]} (Set o.succ) (β x) (Set o)))⟫

def K.type (m n : Level) : Expr :=
  ⟪Π.{[m.succ, m]} (Set m) (M K.{[m, n]})⟫

def K'.type (m n : Level) : Expr :=
  ⟪Π.{[m.succ, m]} (Set m) (M K'.{[m, n]})⟫

def S.type (m n o : Level) : Expr :=
  ⟪Π.{[m.succ, o]} (Set m) (M S.{[m, n, o]})⟫

def i0.type : Expr := ⟪I⟫
def i1.type : Expr := ⟪I⟫

def choose.type (l : Level) : Expr :=
  ⟪Π.{[l.succ, l]} (Set l) (K'.{[l.succ, l.succ]} (Set l) (Set l)
    (Π.{[

/-
choose.{[l]}
-/

inductive IsStep : Expr → Expr → Prop
  | choose  : IsStep ⟪choose.{[l]} A B i0⟫ A
  | choose  : IsStep ⟪choose.{[l]} A B i1⟫ B
  | K       : IsStep ⟪K.{[m, n]} α β x y⟫ x
  | K'      : IsStep ⟪K'.{[m, n]} α β x y⟫ x
  | S       : IsStep ⟪S.{[m, n, o]} α β γ x y z⟫ ⟪(x z) (y z)⟫
  | left    : IsStep f f' → IsStep ⟪f x⟫ ⟪f' x⟫
  | right   : IsStep x x' → IsStep ⟪f x⟫ ⟪f x'⟫
  | pi      : IsStep ⟪Π.{[m, n]} α β x⟫ ⟪β x⟫
  | γ₂      : IsStep ⟪(M (γ.{[m, n, o]} α β)) x⟫ (βx_to_set β x n o)
  | k'₁     : IsStep ⟪(M K'.{[m, n]}) α⟫ ⟪Π.{[n.succ, m]} (Set n) (M (K'.{[m, n]} α))⟫
  | k'₂     : IsStep ⟪(M (K'.{[m, n]} α)) β⟫ ⟪Π.{[m, m]} α (M (K'.{[m, n]} α β))⟫
  | k'₃     : IsStep ⟪(M (K'.{[m, n]} α β)) x⟫ ⟪Π.{[m, m]} β (K'.{[m.succ, n]} (Set m) β α)⟫
  | k₁      : IsStep ⟪(M K.{[m, n]}) α⟫ ⟪Π.{[n.succ.succ, m]}
    (#α_to_set α m n)
    (M (K.{[m, n]} α))⟫
  | k₂      : IsStep ⟪(M (K.{[m, n]} α)) β⟫ ⟪Π.{[m, m]} α (M (K.{[m, n]} α β))⟫
  | k₃      : IsStep ⟪(M (K.{[m, n]} α β)) x⟫ ⟪Π.{[m, m]} (β x) (M (K.{[m, n]} α β x))⟫
  | k₄      : IsStep ⟪(M (K.{[m, n]} α β x)) y⟫ α
  | F₁      : IsStep ⟪(M (F.{[m, n, o]} α β γ)) x⟫ ⟪Π.{[n, o]} (β x) (γ x)⟫
  | s₁      : IsStep ⟪(M S.{[m, n, o]}) α⟫ ⟪Π.{[n.succ.succ, o]} (#α_to_set α m n)
    (M (S.{[m, n]} α))⟫
  | s₂      : IsStep ⟪(M (S.{[m, n, o]} α)) β⟫ ⟪Π.{[o.succ.succ, o]}
    (Π.{[m, o.succ.succ]} α (M (γ.{[m, n, o]} α β)))
    (M (S.{[m, n, o]} α β))⟫
  | s₃      : IsStep ⟪(M (S.{[m, n, o]} α β)) γ⟫ ⟪Π.{[o, o]} (Π.{[m, o]} α (M (F.{[m, n, o]} α β γ)))
    (M (S.{[m, n, o]} α β γ))⟫
  | s₄      : IsStep ⟪(M (S.{[m, n, o]} α β γ)) x⟫ ⟪Π.{[n, o]} (Π.{[m, n]} α β)
    (M (S.{[m, n, o]} α β γ x))⟫
  | s₅      : IsStep ⟪(M (S.{[m, n, o]} α β γ x)) y⟫ ⟪Π.{[m, o]} α
    (M (S.{[m, n, o]} α β γ x y))⟫
  | s₆      : IsStep ⟪(M (S.{[m, n, o]} α β γ x y)) z⟫ ⟪γ z (y z)⟫
  | transp₁ : IsStep ⟪transp.{[m]} A i i1 a⟫ a
  | transpu : IsStep ⟪transp.{[m]} (K'.{[u.succ.succ, A i i0 (Set m)⟫ ⟪
