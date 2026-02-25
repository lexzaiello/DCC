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


declare_syntax_cat op
declare_syntax_cat comb

syntax:max "I" "→" comb : comb

syntax:max ident                        : comb
syntax:max ident  ".{" term "}"         : comb
syntax:max "="  ".{" term "}"           : comb
syntax:max "≃"  ".{" term "}"           : comb
syntax "Π" ".{" term "}"                : comb
syntax "I"                              : comb
syntax "M" comb                         : comb
syntax "="                              : comb
syntax "≃"                              : comb
syntax "∧"                              : comb
syntax "∨"                              : comb
syntax "~"                              : comb
syntax "Sort" term                       : comb
syntax:max "(" comb ")"                 : comb
syntax "_"                              : comb
syntax "#" term                         : comb
syntax op                               : comb

syntax:1022 comb:1022     comb:1023     : comb

syntax  "⟪" comb "⟫"     : term
syntax  "c⟪" comb "⟫"    : term

macro_rules
  | `(⟪Sort $n⟫) => `(Expr.TAtom (TAtom.Sort $n))
  | `(c⟪Sort $n⟫) => `(CExpr.TAtom (TAtom.Sort $n))
  | `(⟪M $c:comb⟫) => `(Expr.M ⟪$c⟫)
  | `(c⟪M $c:comb⟫) => `(CExpr.M ⟪$c⟫)
  | `(c⟪PathP.{[$m]}⟫) => `(CExpr.CAtom (CAtom.PathP $m))
  | `(c⟪∧⟫) => `(CExpr.min)
  | `(c⟪∨⟫) => `(CExpr.max)
  | `(c⟪~⟫) => `(CExpr.rev)
  | `(c⟪=.{[$m]}⟫) => `(CExpr.CAtom (CAtom.Eq $m))
  | `(c⟪≃.{[$m]}⟫) => `(CExpr.CAtom (CAtom.Equiv $m))
  | `(⟪Π.{[$m, $n]}⟫) => `(Expr.TAtom (TAtom.Pi $m $n))
  | `(c⟪Π.{[$m, $n]}⟫) => `(CExpr.TAtom (TAtom.Pi $m $n))
  | `(⟪($c:comb)⟫) => `(⟪$c:comb⟫)
  | `(c⟪($c:comb)⟫) => `(c⟪$c:comb⟫)
  | `(⟪$c:ident.{$lvs:term}⟫) =>
    let name := c.getId
    let name_s := quote name.toString
    `((Expr.comb (Comb.mk $name_s:term $lvs:term)))
  | `(c⟪$c:ident.{$lvs:term}⟫) =>
    let name := c.getId
    let name_s := quote name.toString
    `((CExpr.comb (Comb.mk $name_s:term $lvs:term)))
  | `(⟪$id:ident⟫) =>
    match id with
    | `(ident| $id) =>`($id:term)
  | `(c⟪$id:ident⟫) =>
    match id with
    | `(ident| i0) => `(CExpr.intvl Interval.i0)
    | `(ident| i1) => `(CExpr.intvl Interval.i1)
    | `(ident| hcomp) => `(CExpr.hcomp)
    | `(ident| $id) =>`($id:term)
  | `(c⟪I⟫) => `(CExpr.I)
  | `(c⟪I → $e:comb⟫) => `(CExpr.Dim ⟪$e⟫)
  | `(⟪#$t:term⟫) => `($t)
  | `(c⟪#$t:term⟫) => `($t)
  | `(⟪$f:comb $x:comb⟫) => `(Expr.app ⟪$f:comb⟫ ⟪$x:comb⟫)
  | `(c⟪$f:comb $x:comb⟫) => `(CExpr.app c⟪$f:comb⟫ c⟪$x:comb⟫)

#eval ⟪K'.{[1]}⟫
#eval ⟪K'.{[1, 2]}⟫

def α_to_set (α : Expr) (m n : Level) : Expr :=
  ⟪(Π.{[m, n.succ.succ]}
    α (K'.{[n.succ.succ, m]} (Sort n.succ) α (Sort n)))⟫

def βx_to_set (β x : Expr) (n o : Level) : Expr :=
  ⟪(Π.{[n, o.succ.succ]} (β x) (K'.{[o.succ.succ, n]} (Sort o.succ) (β x) (Sort o)))⟫

def K.type (m n : Level) : Expr :=
  ⟪Π.{[m.succ, m]} (Sort m) (M K.{[m, n]})⟫

def K'.type (m n : Level) : Expr :=
  ⟪Π.{[m.succ, m]} (Sort m) (M K'.{[m, n]})⟫

def S.type (m n o : Level) : Expr :=
  ⟪Π.{[m.succ, o]} (Sort m) (M S.{[m, n, o]})⟫

def i0.type : CExpr := c⟪I⟫
def i1.type : CExpr := c⟪I⟫

def path.type (A α β : Expr) (l : Level) : Expr := ⟪PathP.{[l]} A α β⟫

/-
SI, KI, ~, etc.. are all functions of I.
They are all of type I → Sort ℓ.
KI A x i = x
SI f g x = (f x) (g x)
^ (f : I → (Sort l → Sort m)) (g : I → Sort l)
-/

inductive IsStepM : Expr → Expr → Prop
  /-
    Nondependent K combinator type:
  -/
  | k'₁     : IsStepM ⟪(M K'.{[m, n]}) α⟫ ⟪Π.{[n.succ, m]} (Sort n) (M (K'.{[m, n]} α))⟫
  | k'₂     : IsStepM ⟪(M (K'.{[m, n]} α)) β⟫ ⟪Π.{[m, m]} α (M (K'.{[m, n]} α β))⟫
  | k'₃     : IsStepM ⟪(M (K'.{[m, n]} α β)) x⟫ ⟪Π.{[m, m]} β (K'.{[m.succ, n]} (Sort m) β α)⟫
  /-
    Dependent K combinator type:
  -/
  | k₁      : IsStepM ⟪(M K.{[m, n]}) α⟫ ⟪Π.{[n.succ.succ, m]}
    (#α_to_set α m n)
    (M (K.{[m, n]} α))⟫
  | k₂      : IsStepM ⟪(M (K.{[m, n]} α)) β⟫ ⟪Π.{[m, m]} α (M (K.{[m, n]} α β))⟫
  | k₃      : IsStepM ⟪(M (K.{[m, n]} α β)) x⟫ ⟪Π.{[m, m]} (β x) (M (K.{[m, n]} α β x))⟫
  | k₄      : IsStepM ⟪(M (K.{[m, n]} α β x)) y⟫ α
  /-
    S combinator type:
  -/
  | γ₂      : IsStepM ⟪(M (γ.{[m, n, o]} α β)) x⟫ (βx_to_set β x n o)
  | F₁      : IsStepM ⟪(M (F.{[m, n, o]} α β γ)) x⟫ ⟪Π.{[n, o]} (β x) (γ x)⟫
  | s₁      : IsStepM ⟪(M S.{[m, n, o]}) α⟫ ⟪Π.{[n.succ.succ, o]} (#α_to_set α m n)
    (M (S.{[m, n]} α))⟫
  | s₂      : IsStepM ⟪(M (S.{[m, n, o]} α)) β⟫ ⟪Π.{[o.succ.succ, o]}
    (Π.{[m, o.succ.succ]} α (M (γ.{[m, n, o]} α β)))
    (M (S.{[m, n, o]} α β))⟫
  | s₃      : IsStepM ⟪(M (S.{[m, n, o]} α β)) γ⟫ ⟪Π.{[o, o]} (Π.{[m, o]} α (M (F.{[m, n, o]} α β γ)))
    (M (S.{[m, n, o]} α β γ))⟫
  | s₄      : IsStepM ⟪(M (S.{[m, n, o]} α β γ)) x⟫ ⟪Π.{[n, o]} (Π.{[m, n]} α β)
    (M (S.{[m, n, o]} α β γ x))⟫
  | s₅      : IsStepM ⟪(M (S.{[m, n, o]} α β γ x)) y⟫ ⟪Π.{[m, o]} α
    (M (S.{[m, n, o]} α β γ x y))⟫
  | s₆      : IsStepM ⟪(M (S.{[m, n, o]} α β γ x y)) z⟫ ⟪γ z (y z)⟫

inductive IsStep : Expr → Expr → Prop
  | left    : IsStep f f'  → IsStep ⟪f x⟫ ⟪f' x⟫
  | right   : IsStep x x'  → IsStep ⟪f x⟫ ⟪f x'⟫
  | M       : IsStepM x x' → IsStep x x'
  | KI      : IsStep ⟪KI.{[m]} A x i⟫ x
  | SI      : IsStep ⟪SI.{[m, n]} f g x⟫ ⟪(f x) (g x)⟫
  | K       : IsStep ⟪K.{[m, n]} α β x y⟫ x
  | K'      : IsStep ⟪K'.{[m, n]} α β x y⟫ x
  | S       : IsStep ⟪S.{[m, n, o]} α β γ x y z⟫ ⟪(x z) (y z)⟫
  | pi      : IsStep ⟪Π.{[m, n]} α β x⟫ ⟪β x⟫

inductive CIsStep : CExpr → CExpr → Prop
  | transp₁ : CIsStep c⟪transp.{[m]} A i1 a⟫ a
  | transpu : CIsStep c⟪transp.{[m.succ]} _U i0 (Sort m)⟫ c⟪Sort m⟫
  | eq      : CIsStep c⟪=.{[m]} A⟫ c⟪PathP.{[m]} (KI.{[m.succ]} (Sort m) A)⟫

/-
KI α x i = x
-/
def refl (m : Level) : Expr := ⟪KI.{[m]}⟫

/-
Key insight:
- equalities contain data to "transport" across them.

(A ≃ B) ≃ (A = B)

ua : (A ≃ B) → A = B

since we have a fixed number of combinators,
we're composing the core ua combinators with
substitution.

For example, if we have an I combinator, and SKK,
these are both isomoprhic.

we're just changing the definition of equality
to coincide with transport.

transporting along the equality applies the function
underlying the equivalence.

we basically want to a way to convert an "equivalent"
type into another type.

that is,

(h : ∀ x, T₁ x = T₂ x) → T₁ → T₂

the main challenge is filling in the previous arguments.

equality is not inductively defined on refl, but is defined
by transport.

we need to define transport for all of the arguments of S and K.
we also need to define transport for the types of S and K.
-/
