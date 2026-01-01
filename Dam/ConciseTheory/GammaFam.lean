/-
  An approach to dependently-typed combinators that models contexts as combinatory objects in and of themselves.
-/

import Mathlib.Data.List.Monad

namespace Idea

inductive ExprΓ where
  | k : ExprΓ
  | i : ExprΓ

inductive Expr where
  | Γ    : ExprΓ → Expr
  | ty   : Expr
  | k    : Expr
  | s    : Expr
  | i    : Expr
  | read : Expr
  | next : Expr
  | app  : Expr
    → Expr
    → Expr

declare_syntax_cat atom
declare_syntax_cat app
declare_syntax_cat expr

syntax "Ty"                  : atom
syntax "(" app ")"           : atom
syntax "#" term              : atom
syntax ":" ident             : atom
syntax "::"                  : atom
syntax "K"                   : atom
syntax "ΓK"                  : atom
syntax "ΓI"                  : atom
syntax "ΓS"                  : atom
syntax "I"                   : atom
syntax "S"                   : atom
syntax "read"                : atom
syntax "next"                : atom

syntax atom     : app
syntax app atom : app

syntax "⟪" expr "⟫"      : term
syntax "⟪₁" atom "⟫"     : term
syntax "⟪₂" app "⟫"      : term

macro_rules
  | `(⟪₁ Ty ⟫) => `(Expr.ty)
  | `(⟪₁ #$e:term ⟫) => `($e)
  | `(⟪₁ :$id:ident ⟫) => `($id)
  | `(⟪₁ K ⟫) => `(Expr.k)
  | `(⟪₁ ΓK ⟫) => `(Expr.Γ ExprΓ.k)
  | `(⟪₁ ΓI ⟫) => `(Expr.Γ ExprΓ.i)
  | `(⟪₁ I ⟫) => `(Expr.i)
  | `(⟪₁ S ⟫) => `(Expr.s)
  | `(⟪₁ read ⟫) => `(Expr.read)
  | `(⟪₁ next ⟫) => `(Expr.next)
  | `(⟪₂ ($e:app) ⟫) => `(⟪₂ $e ⟫)
  | `(⟪₂ $e:atom ⟫) => `(⟪₁ $e ⟫)
  | `(⟪₁ ($e:atom) ⟫) => `(⟪₁ $e ⟫)
  | `(⟪₁ ($e:app) ⟫) => `(⟪₂ $e ⟫)
  | `(⟪₂ ($e₁:app) $e₂:atom ⟫) => `(⟪₂ $e₁ $e₂ ⟫)
  | `(⟪₂ $e₁:app $e₂:atom ⟫) => `(Expr.app ⟪₂ $e₁ ⟫ ⟪₁ $e₂ ⟫)

def step : Expr → Option Expr
  | ⟪₂ I :_α :x ⟫ => pure ⟪₁ :x ⟫
  | ⟪₂ read (ΓI :_α) ⟫ => pure ⟪₁ Ty ⟫
  | ⟪₂ read (next (ΓI :α :_x)) ⟫ => α
  | ⟪₂ read (next (read (next (ΓI :α :_x)))) ⟫ => α
  | ⟪₂ read (ΓK :_α) ⟫ => pure ⟪₁ Ty ⟫
  | ⟪₂ read (ΓK :α :_β) ⟫ => pure ⟪₁ Ty ⟫
  | _ => .none

/-
  A context in dependent typing is kind of like a monad.
  "Pure" elements have no type dependency on the context, and are self-contained.
  bind is analogous to a type in the context that refers to a previous item in the context
-/
class Γ (m : Type u → Type v) (α : Type u) where
  -- A context formed by a type with no dependency on the context
  pure : α → m α

  -- Push a nondependent argument type claim to the context
  push : m α → α → m α

  -- A type formed by appending a type that depends on Γ to Γ, giving Γ'
  bind : m α → (m α → α) → m α

  -- The context asserts that the arguments are of an expected type
  -- and this can be done even when the function hasn't been fully
  -- applied
  -- this is stuff below the bar in an inference rule
  pop : m α → α × m α

abbrev ListContext {α : Type} := List α

-- A context that models type-checking for the K combinator
-- Pure and bind are stateless, since the map on m α encodes
-- the assertion logic, not bind itself
instance listContext.instΓK : Γ List Expr where
  pure := Pure.pure
  bind Γ f := f Γ :: Γ
  pop Γ := match Γ.length, Γ with
  | 0, x::xs => (.ty, xs)
  

end Idea

inductive Expr where
  | ty : Expr
  | 
