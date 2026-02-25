import Dcc.Ast

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

def S_type.type  (_m _n o : Level) : Expr := ⟪Sort o⟫
def K_type.type  (m : Level) : Expr       := ⟪Sort m⟫
def K'_type.type (m : Level) : Expr       := ⟪Sort m⟫

def Sort.type (m : Level) : Expr := ⟪Sort m.succ⟫

def Pi.type (m n : Level) : Expr := ⟪Π.{[m.succ, n.succ]}
  (Sort m)
  (K'.{[n.succ.succ, m.succ]} (Sort n.succ) (Sort m) (Sort n))⟫

def MK'.type (m _n    : Level) : Expr := ⟪Sort m⟫
def MK.type  (m _n    : Level) : Expr := ⟪Sort m⟫
def MS.type  (_m _n o : Level) : Expr := ⟪Sort o⟫

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
  | K       : IsStep ⟪K.{[m, n]} α β x y⟫ x
  | K'      : IsStep ⟪K'.{[m, n]} α β x y⟫ x
  | S       : IsStep ⟪S.{[m, n, o]} α β γ x y z⟫ ⟪(x z) (y z)⟫
  | pi      : IsStep ⟪Π.{[m, n]} α β x⟫ ⟪β x⟫

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | symm    : DefEq e e'  → DefEq e' e
  | step    : IsStep e e' → DefEq e e'
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ⟪f x⟫ ⟪f' x⟫
  | right   : DefEq x x'  → DefEq ⟪f x⟫ ⟪f x'⟫

inductive ValidJudgment : Expr → Expr → Prop
  | Sort  : ValidJudgment (Sort.type m)   ⟪Sort m⟫
  | S     : ValidJudgment (S.type m n o)  ⟪S.{[m, n, o]}⟫
  | K     : ValidJudgment (K.type m n)    ⟪S.{[m, n]}⟫
  | K'    : ValidJudgment (K'.type m n)   ⟪K'.{[m, n]}⟫
  | Pi    : ValidJudgment (Pi.type m n)   ⟪Π.{[m, n]}⟫
  | MK    : ValidJudgment (MK.type m n)   ⟪M K.{[m, n]}⟫
  | MK'   : ValidJudgment (MK'.type m n)  ⟪M K'.{[m, n]}⟫
  | MS    : ValidJudgment (MS.type m n o) ⟪M S.{[m, n, o]}⟫
  | app   : ValidJudgment ⟪Π.{[m, n]} α cod⟫ f
    → ValidJudgment α x
    → ValidJudgment ⟪cod x⟫ ⟪f x⟫
  | defeq : ValidJudgment t x
    → DefEq t t'
    → ValidJudgment t' x

