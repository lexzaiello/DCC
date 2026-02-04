import Mathlib.Data.Nat.Notation
import Mathlib.Tactic

/-
Realized we've basically been doing sequent calculi the whole time.

⊢ : (Prop → Prop) → (Prop → Prop) → Prop → Prop

id α : (∶ Ty α) ∧ ⊢ (snd ∘ fst)

id α : (∶ α) ⊢ (id Prop)

we always want application to produce a judgment.
This is on normal values, at least.

fst (a ∧ b) = a
snd (a ∧ b) = b

fst ((∶ m) α a) = ((∶ m.succ) (Ty m) α)
snd (∶ α m) = (∶ m)

∧ to combine contexts.

We receive our arguments as (∶ T x)

The consequent is the type of the entire application.

I want

id α : (∶ α) ∘ (id Prop) ⊢ (id Prop)

id : (id Prop) ⊢ (∘ (id Prop)) ∘ snd ⊢ (id Prop)
-/

abbrev Level := ℕ

inductive Expr where
  | app   : Expr  → Expr → Expr
  | vdash : Expr
  | judge : Level → Expr
  | fst   : Expr
  | snd   : Expr
  | id    : Expr
  | prop  : Expr
  | comp  : Expr
  | and   : Expr
  | ty    : Level → Expr

abbrev Term := Expr
abbrev Typ  := Expr

open Expr

syntax "⸨" term+ "⸩"       : term

notation "Ty" => Expr.ty
notation "Prp" => Expr.prop
notation "∶" => Expr.judge
notation "⊢" => Expr.vdash

macro_rules
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f $x)
  | `(⸨ $f $x:term $args:term*⸩) => `(⸨ (Expr.app $f $x) $args*⸩)

infixr:90 " ∘ " => (fun f g => ⸨Expr.comp f g⸩)
infixr:90 " ⊢ " => (fun f g => ⸨Expr.vdash f g⸩)
infixl:90 " ∧ " => (fun f g => ⸨Expr.and f g⸩)

inductive IsStep : Expr → Expr → Prop
  | id     : IsStep ⸨Expr.id _α x⸩ x
  | fst    : IsStep ⸨fst ⸨(∶ m) α x⸩⸩ ⸨(∶ m.succ) (Ty m) α⸩
  | snd    : IsStep ⸨snd ⸨(∶ m.succ) α x⸩⸩ ⸨(∶ m) x⸩
  | fst'   : IsStep ⸨fst (a ∧ b)⸩ a
  | snd'   : IsStep ⸨fst (a ∧ b)⸩ b
  | comp   : IsStep ⸨(f ∘ g) x⸩ ⸨f ⸨g x⸩⸩
  | left   : IsStep f f'
    → IsStep ⸨f x⸩ ⸨f' x⸩
  | right  : IsStep x x'
    → IsStep ⸨f x⸩ ⸨f x'⸩

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | step    : IsStep e e' → DefEq e e'
  | symm    : DefEq e₁ e₂ → DefEq e₂ e₁
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ⸨f x⸩ ⸨f' x⸩
  | right   : DefEq x x'  → DefEq ⸨f x⸩ ⸨f x'⸩

def id.type : Expr :=
  ⸨id Prp⸩ ⊢ (⸨comp ⸨id Prp⸩⸩ ∘ snd) ⊢ ⸨id Prp⸩

inductive ValidJudgment : Typ → Term → Prop
  | ty    : ValidJudgment (Ty m.succ) (Ty m)
  | prp   : ValidJudgment (Ty 0) Prp
  | app   : ValidJudgment t_x x
    → ValidJudgment (Ty m) t_x
    → ValidJudgment (α ⊢ β) f
    → DefEq ⸨α ⸨(∶ m) t_x x⸩⸩ ⸨(∶ m) t_x x⸩
    → ValidJudgment ⸨β ⸨(∶ m) t_x x⸩⸩ ⸨f x⸩
  | defeq : ValidJudgment t₁ e
    → DefEq t₁ t₂
    → ValidJudgment t₂ e

