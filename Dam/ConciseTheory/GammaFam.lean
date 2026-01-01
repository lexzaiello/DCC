/-
  An approach to dependently-typed combinators that models contexts as combinatory objects in and of themselves.
-/

import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Monad

namespace Idea

inductive Expr where
  | ty     : Expr
  | tup    : Expr
  | cons   : Expr
  | nil    : Expr
  | seq    : Expr
  | k      : Expr
  | s      : Expr
  | i      : Expr
  | fst    : Expr
  | snd    : Expr
  | read   : Expr
  | read_α : Expr
  | read_y : Expr
  | next   : Expr
  | app    : Expr
    → Expr
    → Expr
deriving BEq

declare_syntax_cat atom
declare_syntax_cat app
declare_syntax_cat expr

syntax "Ty"                  : atom
syntax ">>"                  : atom
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
syntax "fst"                 : atom
syntax "snd"                 : atom
syntax "nil"                 : atom
syntax "::"                  : atom
syntax "next"                : atom
syntax "read_α"              : atom
syntax "read_y"              : atom
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
  | `(⟪₁ fst ⟫) => `(Expr.fst)
  | `(⟪₁ snd ⟫) => `(Expr.snd)
  | `(⟪₁ read ⟫) => `(Expr.read)
  | `(⟪₁ read_α ⟫) => `(Expr.read_α)
  | `(⟪₁ read_y ⟫) => `(Expr.read_y)
  | `(⟪₁ :: ⟫) => `(Expr.cons)
  | `(⟪₁ next ⟫) => `(Expr.next)
  | `(⟪₁ >> ⟫) => `(Expr.seq)
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
  | ⟪₂ fst ⟫ => "fst"
  | ⟪₂ snd ⟫ => "snd"
  | ⟪₂ >> ⟫ => ">>"
  | ⟪₂ read_α ⟫ => "read_α"
  | ⟪₂ read_y ⟫ => "read_y"
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
  | ⟪₂ :: :x (:: :y :xs) ⟫ => ⟪₂ :: :x (:: :y (#Expr.push_in with_e xs)) ⟫
  | ⟪₂ :: :x :xs ⟫ => ⟪₂ :: :x (:: :xs :with_e) ⟫
  | e => e

def Expr.as_list : Expr → Option (List Expr)
  | ⟪₂ :: :x :xs ⟫ => do return x :: (← xs.as_list)
  | ⟪₂ nil ⟫ => pure []
  | x => pure [x]

def Expr.from_list : List Expr → Expr
  | [] => ⟪₂ nil ⟫
  | x::xs => ⟪₂ :: :x (#Expr.from_list xs) ⟫

def Expr.mk_tup : List Expr → Expr
  | [] => ⟪₂ nil ⟫
  | [x, xs] => ⟪₂ , :x :xs ⟫
  | x :: xs => ⟪₂ , :x (#Expr.mk_tup xs) ⟫

example : Expr.mk_tup [⟪₂ Ty ⟫, ⟪₂ S ⟫, ⟪₂ K ⟫] = ⟪₂ ((, Ty) (, S K)) ⟫ := rfl

def Expr.map_list (f : Expr → Expr) : Expr → Option Expr
  | ⟪₂ :: :x :xs ⟫ => do pure ⟪₂ :: (#← f x) (#← xs.map_list f) ⟫
  | e@⟪₂ nil ⟫ => e
  | _ => .none

def Expr.map_listM {m : Type → Type} [Monad m] (f : Expr → m Expr) : Expr → OptionT m Expr
  | ⟪₂ :: :x :xs ⟫ => do pure ⟪₂ :: (#← f x) (#← xs.map_listM f) ⟫
  | e@⟪₂ nil ⟫ => pure e
  | _ => OptionT.mk (pure .none)

def Expr.display_infer : Expr → Expr
  | ⟪₂ , nil (, (:: :t nil) :_Ξ) ⟫ => t
  | e => e

example : Expr.as_list ⟪₂ :: Ty (:: K Ty) ⟫ = [⟪₁ Ty ⟫, ⟪₁ K ⟫, ⟪₁ Ty ⟫] := rfl

example : Expr.push_in ⟪₂ Ty ⟫ ⟪₂ :: Ty K ⟫ = ⟪₂ :: Ty (:: K Ty) ⟫ := rfl

def step : Expr → Option Expr
  | ⟪₂ >> :f :g :Γ ⟫ => step ⟪₂ :g (:f :Γ) ⟫
  | ⟪₂ I :_α :x ⟫ => x
  | ⟪₂ K :_α :_β :x :_y ⟫ => x
  | ⟪₂ next (:: :_x :xs) ⟫ => xs
  | ⟪₂ read (:: :x :_xs) ⟫ => x
  | ⟪₂ fst (, :a :_b) ⟫ => a
  | ⟪₂ snd (, :_a :b) ⟫ => b
  | ⟪₂ read_α (, :Γ :_Ξ) ⟫ => do
    let term_α := ⟪₂ read :Γ ⟫
    pure ⟪₂ ,
      (:: (K Ty Ty :term_α) (:: (>> fst read) (:: (K Ty Ty Ty) nil)))
      (,
        (:: :term_α nil)
        (:: Ty nil)) ⟫
  | ⟪₂ read_y (, :Γ :_Ξ) ⟫ =>
    ⟪₂ (read (next :Γ)) (read (next (next :Γ))) ⟫
  | ⟪₂ :f :x ⟫ => do
    ⟪₂ (# (step f).getD f) (#(step x).getD x) ⟫
  | _ => .none

def try_step_n (n : ℕ) (e : Expr) : Option Expr := do
  if n = 0 then
    pure e
  else
    let e' ← step e
    pure <| (try_step_n (n - 1) e').getD e'

def try_step_n! (n : ℕ) (e : Expr) : Expr := (try_step_n n e).getD e

-- Applies the Δ claims context to all handlers in the app context
-- returns all of the applied assertions, in order
def sub_context : Expr → Expr
  | ⟪₂ , :Γ (, :Δ :Ξ) ⟫ =>
    Expr.mk_tup <| (do (← Γ.as_list).mapM (fun f => step ⟪₂ :f (, :Δ :Ξ) ⟫)).getD []
  | e => e

def infer : Expr → Option Expr
  | ⟪₂ I ⟫ => ⟪₂ , (:: (K Ty Ty Ty) (:: (>> fst read) (:: (>> fst read) nil))) (, nil nil) ⟫
  | ⟪₂ K ⟫ =>
    let t_α := ⟪₂ K Ty Ty Ty ⟫
    let t_β := ⟪₂ read_α ⟫
    let t_x := ⟪₂ (>> fst read) ⟫
    let t_y := ⟪₂ read_y ⟫

    ⟪₂ , (:: :t_α (:: :t_β (:: :t_x (:: :t_y (:: :t_x nil))))) (, nil nil) ⟫
  | ⟪₂ Ty ⟫ => ⟪₂ , nil (, (:: Ty nil) nil) ⟫
  | ⟪₂ :f :arg ⟫ => do
    let t_f ← infer f
    let t_arg := (← infer arg).display_infer

    match t_f with
    | ⟪₂ , :Γ (, :Δ :Ξ) ⟫ =>
      let Δ' := Expr.push_in arg Δ
      let Ξ' := Expr.push_in t_arg Ξ

      let asserts ← Γ.as_list
      let claims  ← Δ'.as_list

      -- Assertion to check that we provided the right type
      let check_with ← asserts[(← Δ.as_list).length]?

      let norm_ctx := (try_step_n! 10 ∘ sub_context)

      let norm_expected := norm_ctx (← try_step_n 10 ⟪₂ :check_with (, :Δ' :Ξ') ⟫)
      let norm_actual := norm_ctx t_arg

      if norm_expected == norm_actual then
        if claims.length.succ == asserts.length then
          let t_out ← try_step_n 10 ⟪₂ (#← asserts.getLast?) (, :Δ' :Ξ') ⟫

          pure ⟪₂ , nil (, (:: :t_out nil) :Ξ') ⟫
        else
          pure ⟪₂ , :Γ (, :Δ' :Ξ') ⟫
      else
        .none
    | _ => .none
  | _ => .none

#eval infer ⟪₂ ((, ((:: (((K Ty) Ty) Ty)) ((:: read) ((:: read) nil)))) ((:: Ty) nil)) ⟫

#eval Expr.display_infer <$> infer ⟪₂ I Ty ⟫
#eval Expr.display_infer <$> infer ⟪₂ I Ty Ty ⟫
#eval Expr.display_infer <$> infer ⟪₂ K Ty (I Ty) Ty Ty ⟫

end Idea
