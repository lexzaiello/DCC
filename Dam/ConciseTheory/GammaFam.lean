/-
  An approach to dependently-typed combinators that models contexts as combinatory objects in and of themselves.
-/

import Mathlib.Data.List.Monad

namespace Idea

inductive Expr where
  | ty   : Expr
  | tup  : Expr
  | cons : Expr
  | nil  : Expr
  | k    : Expr
  | s    : Expr
  | i    : Expr
  | read : Expr
  | next : Expr
  | app  : Expr
    → Expr
    → Expr
deriving BEq

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
syntax "tup"                 : atom
syntax "nil"                 : atom
syntax "::"                  : atom
syntax "next"                : atom
syntax ","                   : atom

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
  | `(⟪₁ I ⟫) => `(Expr.i)
  | `(⟪₁ S ⟫) => `(Expr.s)
  | `(⟪₁ read ⟫) => `(Expr.read)
  | `(⟪₁ :: ⟫) => `(Expr.cons)
  | `(⟪₁ next ⟫) => `(Expr.next)
  | `(⟪₁ nil ⟫) => `(Expr.nil)
  | `(⟪₁ , ⟫) => `(Expr.tup)
  | `(⟪₂ ($e:app) ⟫) => `(⟪₂ $e ⟫)
  | `(⟪₂ $e:atom ⟫) => `(⟪₁ $e ⟫)
  | `(⟪₁ ($e:atom) ⟫) => `(⟪₁ $e ⟫)
  | `(⟪₁ ($e:app) ⟫) => `(⟪₂ $e ⟫)
  | `(⟪₂ ($e₁:app) $e₂:atom ⟫) => `(⟪₂ $e₁ $e₂ ⟫)
  | `(⟪₂ $e₁:app $e₂:atom ⟫) => `(Expr.app ⟪₂ $e₁ ⟫ ⟪₁ $e₂ ⟫)

def Expr.toString : Expr → String
  | ⟪₂ Ty ⟫ => "Ty"
  | ⟪₂ :: ⟫ => "::"
  | ⟪₂ nil ⟫ => "nil"
  | ⟪₂ read ⟫ => "read"
  | ⟪₂ , ⟫ => ","
  | ⟪₂ :f :x ⟫ => s!"({f.toString} {x.toString})"
  | ⟪₂ next ⟫ => "next"
  | ⟪₂ I ⟫ => "I"
  | ⟪₂ K ⟫ => "K"
  | ⟪₂ S ⟫ => "S"

instance Expr.instToString : ToString Expr where
  toString := Expr.toString

def Expr.push_in (with_e : Expr) : Expr → Expr
  | ⟪₂ :: :x nil ⟫ => ⟪₂ :: :x (:: :with_e nil) ⟫
  | ⟪₂ nil ⟫ => ⟪₂ :: :with_e nil ⟫
  | ⟪₂ :: :x :xs ⟫ => ⟪₂ :: :x (:: :xs :with_e) ⟫
  | e => e

def Expr.as_list : Expr → Option (List Expr)
  | ⟪₂ :: :x :xs ⟫ => do return x :: (← xs.as_list)
  | ⟪₂ nil ⟫ => pure []
  | x => pure [x]

example : Expr.as_list ⟪₂ :: Ty (:: K Ty) ⟫ = [⟪₁ Ty ⟫, ⟪₁ K ⟫, ⟪₁ Ty ⟫] := rfl

example : Expr.push_in ⟪₂ Ty ⟫ ⟪₂ :: Ty K ⟫ = ⟪₂ :: Ty (:: K Ty) ⟫ := rfl

def step : Expr → Option Expr
  | ⟪₂ I :_α :x ⟫ => x
  | ⟪₂ K :_α :_β :x :_y ⟫ => x
  | ⟪₂ next (:: :_x :xs) ⟫ => xs
  | ⟪₂ read (:: :x :_xs) ⟫ => x
  | ⟪₂ read (, :a :_b) ⟫ => a
  | ⟪₂ next (, :_a :b) ⟫ => b
  | _ => .none

def infer : Expr → Option Expr
  | ⟪₂ I ⟫ => ⟪₂ , (:: (K Ty Ty Ty) (:: read (:: read nil))) nil ⟫
  | ⟪₂ Ty ⟫ => ⟪₂ , nil (:: Ty nil) ⟫
  | ⟪₂ :f :arg ⟫ => do
    let t_f ← infer f
    let t_arg ← infer arg

    match t_f, t_arg with
    | ⟪₂ , :Γ :Δ ⟫, ⟪₂ , nil (:: :t_arg nil) ⟫ =>
      let Δ' := Expr.push_in arg Δ

      let asserts ← Γ.as_list
      let claims  ← Δ'.as_list

      -- Assertion to check that we provided the right type
      let check_with ← asserts[(← Δ.as_list).length]?

      dbg_trace t_arg

      if (← step ⟪₂ :check_with :Δ' ⟫) == t_arg then
        -- We have found the final β-normal form's type
        -- the combinator should be asserting more types
        -- in the context than we have arguments, exactly one more (the return type)
        if claims.length.succ == asserts.length then
          let t_out ← step ⟪₂ (#← claims.getLast?) :Δ' ⟫

          pure ⟪₂ , nil (:: :t_out nil) ⟫
        else
          pure ⟪₂ , :Γ :Δ' ⟫
      else
        .none
    | _, _ => .none
  | _ => .none

#eval infer ⟪₂ I Ty ⟫

end Idea
