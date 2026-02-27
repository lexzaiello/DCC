import Qq
import Mathlib.Data.Nat.Notation
import Lean.Elab.Term.TermElabM
import Lean.Elab.Term
import Mathlib.Tactic.ToExpr
import Mathlib
import Lean

open Qq
open Lean (Macro)
open Lean (MacroM)
open Lean (Syntax)
open Lean (Level)
open Lean (mkApp)
open Lean (mkAppN)
open Lean (mkLambda)
open Lean (mkConst)
open Lean.ToExpr (toExpr)
open Lean.Quote (quote)
open Lean.Elab
open Lean.Elab.Term
open Lean.Elab.Level

inductive Expr where
  | I       : Level → Expr
  | K       : Level → Level → Expr -- Dependent K
  | K'      : Level → Level → Expr -- Nondependent K
  | S       : Level → Level → Level → Expr -- Dependent S
  | cons    : Level → Level → Expr -- Normal pair. this is a Type.
  | mkcons  : Level → Level → Level → Level → Level → Level → Expr
  -- ^ (mkcons πcons πf πg f g x) = (πcons πf πg (πf f x) (πg g x))
  | judge   : Level  → Expr -- judge t is a freestanding expr
  /-
    Sorts:
  -/
  | sort   : Level → Expr
  | fst    : Level → Level → Expr
  | snd    : Level → Level → Expr
  | app    : Expr  → Expr  → Expr
deriving BEq, Repr

open Expr

declare_syntax_cat comb
syntax ident                            : comb
syntax:max comb  ".{" level,+ "}"       : comb
syntax:max num                          : comb
syntax "Sort" level                     : comb
syntax "Type" level                     : comb
syntax "Prop"                           : comb
syntax:max "(" comb ")"                 : comb
syntax:max "::(" comb,+ ")"             : comb
syntax "_"                              : comb
syntax "#(" term ")"                    : comb

syntax:1022 comb:1022     comb:1023     : comb
syntax:50   comb:51 " : " comb:50       : comb
syntax:40   comb:41 " → " comb:40       : comb
syntax:30   "∀" "(" comb,+ ")" "," comb : comb

syntax  "⟪" comb "⟫"     : term
syntax "*⟪" comb "⟫"     : term

/-def Expr.decode (e : Lean.Expr) : TermElabM Expr := do
  match e with
  | .app (.const ``Expr.sort []) n =>
    Expr.sort n
  | _ => sorry-/

def unwrap_sorts {n_sorts : ℕ} (raw : Vector Q(Level) n_sorts) : TermElabM (Vector Lean.Level n_sorts) :=
  raw.mapM (fun l => match l with
    | .sort m => pure m
    | e => throwError s!"expected a sort but found: {e}")

def Expr.toExpr (e : Expr) : Lean.Expr :=
  match e with
    | .cons m n =>
      q(fun (α : Type $m) (β : Type $n) => α → β)
    | .sort n => q(Sort $n)
    | .I n => q(fun (α : Type $n) (x : α) => x)
    | .K m n => q(fun (α : Type $m) (β : α → Type $n) (x : α) (_y : β x) => x)
    | .K' m n => q(fun (α : Type $m) (β : Type $n) (x : α) (_y : β) => x)
    | .S m n o => q(fun (α : Type $m) (β : α → Type $n) (γ : ∀ (x : α), β x → Type $o) (f : ∀ (x : α) (y : β x), γ x y) (g : ∀ (x : α), β x) (x : α) => (f x (g x)))
    | .judge m => q(fun (α : Type $m) (x : α) => (@Inhabited.mk α x))
    | .fst m n => q(fun (α : Type $m) (β : α → Type $n) (S : Σ a : α, β a) => S.fst)
    | .snd m n => q(fun (α : Type $m) (β : α → Type $n) (S : Σ a : α, β a) => S.snd)
    | .app f x =>
      let f' := f.toExpr
      let x' := x.toExpr
      f'.app x'
    | .mkcons m n o p q r =>
      -- (mkcons πcons πf πg f g x) = (πcons πf πg (πf f x) (πg g x))
      -- α : Type m
      -- f : (F : Type n)
      -- g : (G : Type o)
      -- πf : ∀ (f : F) (x : α), D f x
      -- πg : ∀ (g : G) (x : α), E g x
      -- πcons : ∀ (πf : ∀ (f : F) (x : α), D f x)
      -- (πg : ∀ (g : G) (x : α), E g x)
      -- D f x β= D'
      -- πcons : ∀ (πf : ∀ (f : F) (x : α), )
      -- (πg : ∀ (f : F) (x : α), )
      -- (fst : D')
      -- (snd : E'), End
      -- mkcons takes a πcons, which dicates how to build the next cons.
      -- mkcons also takes πf, which makes the f / fst compoent of the sigma, and
      -- the next substitute value (x : α)
      -- πcons : ∀ (πf : Dummy₁) (πg : Dummy₂) (fst : D) (snd : e), γ πf πg fst snd
      -- if we used A as a placeholder, how scuffed would it be? not toob ad.
      -- if we already know fst and snd, we can shortcut the type dependency.
      -- fst was produced by substitution.
      -- refinement: instead of F and G being the literal types,
      -- F and G are the codomain? hmmmm
      q(fun (α : Type $m) (F : Type $n) (G : Type $o) (A : Type $p) (B : Type $q)
        (γ : Type $r)
        (πcons : (F → α → A) → (G → α → B) → A → B → γ)
        (πf : F → α → A) (πg : G → α → B)
        (f : F) (g : G)
        (x : α) => (πcons πf πg (πf f x) (πg g x)))

instance : Lean.ToExpr Expr where
  toExpr := Expr.toExpr
  toTypeExpr := .const ``Expr []

macro_rules
  | `(⟪Prop⟫) => `(Expr.sort Level.zero)
  | `(⟪::($cfg:comb, $a:comb, $b:comb)⟫) =>`(⟪$cfg $a $b⟫)
  | `(⟪::($cfg:comb, $a:comb, $b:comb,*)⟫) => `(⟪$cfg $a ::($cfg, $b,*)⟫)
  | `(⟪$n:num⟫) => `($n:term)
  | `(⟪$id:ident⟫) =>
    match id with
    | `(ident| I) => `(Expr.I)
    | `(ident| K) => `(Expr.K)
    | `(ident| K') => `(Expr.K')
    | `(ident| S) => `(Expr.S)
    | `(ident| cons) => `(Expr.cons)
    | `(ident| mkcons) => `(Expr.mkcons)
    | `(ident| judge) => `(Expr.judge)
    | `(ident| fst) => `(Expr.fst)
    | `(ident| snd) => `(Expr.snd)
    | id => `($id)
  | `(⟪($c:comb)⟫) => `(⟪$c:comb⟫)
  | `(⟪$f:comb $x:comb⟫) => `(Expr.app ⟪$f:comb⟫ ⟪$x:comb⟫)

elab_rules : term
  | `(⟪$c:ident.{$lvs:level,*}⟫) => do
    let lvs ← lvs.getElems.mapM (fun h => Lean.toExpr <$> elabLevel h)
    let c ← elabTerm c .none
    return Lean.mkAppN c lvs
  | `(⟪Type $n⟫) => do
    let n ← elabLevel n
    return (Lean.Expr.const ``Expr.sort []).app (toExpr n.succ)
  | `(⟪Sort $n⟫) => do
    let n ← elabLevel n
    return (Lean.Expr.const ``Expr.sort []).app (toExpr n)

#eval ⟪I.{1}⟫
#eval ⟪I.{1} Prop⟫
