import Qq
import Mathlib.Data.Nat.Notation
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
open Lean (Syntax)

/-
The tricky thing is mkcons. I like that we can be so flexible with it.
However, it should also almost certainly have universe arguments.

If we wanted to we could make it just eliminate into Prop eventually.
We will need some way of unifying the type at somepoint.

The key potential idea is that

(mkcons πcons πf πg f g x) = (πcons πf πg (πf f x) (πg g x))

so we need to restrict the type of πcons so that it it can accept these things.

This implies, unfortunately, that we need additional type arguments. that's fine tho.

πcons πf πg (πf f x) (πg g x)

call πf : α
call πg : β
call (πf f x) : γ
call (πg g x) : δ

it doesn't really make sense for the types in the list to be dependent, really.

we could just go simply-typed for now.

so πcons has m n o p universe levels.

πcons's type depends on all of these things

πcons : ∀ (πf : α) (πg : β) (πx : γ) (πy : δ), ε(πf, πg, πx, πy)

mkcons m n o p α β

πf and πg's types are both equally dependent on x at thev ery least.

πf : ∀ (f : ∀ (x : α), P x) (x : α), P x
πg : ∀ (g : ∀ (x : α), Q x) (x : α), Q x

unique objects so far:
- α
- P
- Q

- will probably needa  δ.

πcons : 

But what about the combined type?
πcons gives us that, I suppose, through another universe arugment.

fst is not actually necessary with our current version of cons.
I am fairly certain of this. However, it will probably be useful for judgments.

fst and snd are not required. total bogus.
ONLY thing they might be useful for is judgments, but we can encode those
with lists too, if we wanted. I say, leave fst and snd out for now,
or restrict them to judgments.

At the very least, fst and snd need type arguments.

We're always working with a Σ-like thing.

δ

πf πg (πf f x) (πg g x)

α : Type m

f doesn't necessarily depend on x.
πf didcates this.

however, πf should accept f, whatever it is
and x. and it should do something with them.

another way to think of it:
πf f has a type alreayd defined, independently of x.

this is (πf f) : ∀ (x : α), P x

challenge: we don't know type of f.
we will need to internalize it into πf.

doesn't necessarily have to apply f and x, just ware of them.
πf : ∀ (f :

going back to original sigma types:
we dont' hard-code this in the types as strictly.

the most stable parts:
- we need a type for x to substitute,
- we need a codomain after substitution
- intermeidate steps are mildly irrelevant.

πf should be aware of f and x, but it should be able to do whatever it wants with them.

in other words:

πf : ∀ (f : Tf) (x : α), Δ f x?

- α : Type m
- x : α
- tf : Type n
- f : Tf
- g : Tg
- tg : Type o
- πf : ∀ (f : Tf) (x : α), P f x
- πg : ∀ (g : Tg) (x : α), Q g x
- πcons : ∀ (πf : ∀ (f : Tf) (x : α), P f x)
  (πg : ∀ (g : Tg) (x : α), Q g x)
  (fst :

- we want to know our very final codomain.
after applying πcons, we don't want our type to change.

Most important intermeidate step? / argumentsS?

- if we work outside in and start with the types of f and g, this might be helpful.

(x : α)
(f : F)
(πf : F → α → D) / (πf : F → α → D

α : Type m
F : Type n
G : Type o
D is some dependent function living in sort p
E is some dependent function living in sort q
πcons takes all in and lives in sort t

πmkcons : ∀ (πf : ∀ (f : F) (x : α), D f x)
  (πg : ∀ (g : G) (x : α), E g x)
  (f : F)
  (g : G)

- 5 type universe levels. that's lovely.
- α : Type m
- F : Type n
- G : type o

-/

inductive Expr where
  | I       : Level → Expr
  | K       : Level → Level → Expr -- Dependent K
  | K'      : Level → Level → Expr -- Nondependent K
  | S       : Level → Level → Level → Expr -- Dependent S
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
deriving BEq

open Expr

declare_syntax_cat comb
syntax level                            : comb
syntax:max ident (".{" term,+ "}")?     : comb
syntax:max num                          : comb
syntax "Sort" term                      : comb
syntax "Type" term                      : comb
syntax "Prop"                           : comb
syntax:max "(" comb ")"                 : comb
syntax:max "::(" comb,+ ")"             : comb

syntax:1022 comb:1022     comb:1023     : comb
syntax:50   comb:51 " : " comb:50       : comb
syntax:40   comb:41 " → " comb:40       : comb
syntax:30   "∀" "(" comb,+ ")" "," comb : comb

syntax "⟪" comb "⟫"     : term

def Expr.toExpr (e : Expr) : Lean.Expr :=
  match e with
    | .sort n => mkApp (mkConst ``Expr.sort) (Lean.toExpr n)
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
      Lean.mkApp f' x'
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
      -- another interesting idea:
      q(fun (α : Type $m) (F : Type $n) (G : Type $o) (A : Type $p) (B : Type $q)
        (γ : (F → α → A) → (G → α → B) → A → B → Type $r)
        (πcons : ∀ (πf : F → α → A) (πg : G → α → B) (fst : A) (snd : B), γ πf πg fst snd)
        (πf : F → α → A) (πg : G → α → B)
        (f : F) (g : G)
        (x : α) => (πcons πf πg (πf f x) (πg g x)))

instance : Lean.ToExpr Expr where
  toExpr := Expr.toExpr
  toTypeExpr := .const ``Expr []

macro_rules
  | `(⟪Prop⟫) => `(Expr.sort 0)
  | `(⟪Type $n⟫) => `(Expr.sort ($n:term + 1))
  | `(⟪Sort $n⟫) => `(Expr.sort $n:term)
  | `(⟪::($cfg:comb, $a:comb, $b:comb)⟫) =>`(⟪$cfg $a $b⟫)
  | `(⟪::($cfg:comb, $a:comb, $b:comb,*)⟫) => `(⟪$cfg $a ::($cfg, $b,*)⟫)
  | `(⟪$n:num⟫) => `($n:term)
  | `(⟪$id:ident.{$l:term,*}⟫) => `($id $l:term*)
  | `(⟪$id:ident⟫) => `($id)
  | `(⟪($c:comb)⟫) => `(⟪$c:comb⟫)
  | `(⟪$f:comb $x:comb⟫) => `(Expr.app ⟪$f:comb⟫ ⟪$x:comb⟫)

#eval ⟪I.{1} Prop⟫
