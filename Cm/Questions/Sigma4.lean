import Mathlib.Data.Nat.Notation

/-
⊢ cod ⸨∶ Ty α⸩ ⸨∶ α x⸩ = ⸨cod ⸨∶ α x⸩⸩
-/

abbrev Universe := ℕ

inductive Expr where
  | judge  : Universe → Expr
  | vdash  : Universe → Expr
  -- S combinator
  | S      : Universe  → Universe → Universe → Expr
  -- Dependent K combinator
  | K      : Universe → Universe → Expr
  -- Nondependent K combinator
  | K'     : Universe → Universe → Expr
  | prop   : Expr
  | ty     : Universe → Expr
  | app    : Expr → Expr → Expr

open Expr

notation "⊢" => Expr.vdash
notation "∶" => Expr.judge

syntax "⸨" term+ "⸩"       : term

notation "Ty" => Expr.ty
notation "Prp" => Expr.prop

macro_rules
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f $x)
  | `(⸨ $f $x:term $args:term*⸩) => `(⸨ (Expr.app $f $x) $args*⸩)

inductive IsStep : Expr → Expr → Prop
  | k'     : IsStep ⸨(K' m n) α β x y⸩ x
  | k      : IsStep ⸨(K m n) α β x y⸩ x
  | s      : IsStep ⸨(S m n o) α β γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | left   : IsStep f f' → IsStep ⸨f x⸩ ⸨f' x⸩
  | right  : IsStep x x' → IsStep ⸨f x⸩ ⸨f x'⸩

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | step    : IsStep e e' → DefEq e e'
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ⸨f x⸩ ⸨f' x⸩
  | right   : DefEq x x'  → DefEq ⸨f x⸩ ⸨f x'⸩
  | vdash   : DefEq ⸨(⊢ m) cod_fn dom subst⸩ ⸨(⊢ m) ⸨cod_fn subst⸩ dom⸩

abbrev Term := Expr
abbrev Typ  := Expr

def prp.judge : Expr :=
  ⸨(∶ 1) (Ty 0) Prp⸩

def mk_arrow (α β : Expr) (n : Universe) : Expr :=
  ⸨(⊢ n) ⸨(K' n 0) (Ty n) Prp β⸩ α⸩

/-
vdash m : (Prop → Type m) → Prop → Type m
-/
def vdash.type (m : Universe) : Expr :=
  mk_arrow (mk_arrow Prp (Ty m) m.succ) (mk_arrow Prp (Ty m) m.succ) m.succ

/-
Simply-typed B combinator.

B α β γ (f : β → γ) (g : α → β) (x : α), γ

B x y z = 

C = S α (const' f) g
-/
def comp 

/-
∀ (α : Type) (β : Type), α → β → α
-/
def const'.type (m n : Universe) : Expr :=
  ⸨(⊢ m) ⸨(⊢ m) _ (Ty n)⸩ (Ty m)⸩

inductive ValidJudgment : Term → Typ → Prop
  | ty    : ValidJudgment (Ty m) (Ty m.succ)
  | prp   : ValidJudgment Prp (Ty 0)
  | app   : ValidJudgment f ⸨(⊢ n) cod ⸨(∶ m.succ) (Ty m) α⸩⸩
    → ValidJudgment x α
    → ValidJudgment ⸨f x⸩ ⸨cod ⸨(∶ m) α x⸩⸩
  | defeq : ValidJudgment e t₁
    → DefEq t₁ t₂
    → ValidJudgment e t₂

