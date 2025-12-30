import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Sigma.Basic

/-
Altenkirch's munchhausen method for combinatory calculi in Lean.
https://drops.dagstuhl.de/storage/00lipics/lipics-vol269-types2022/LIPIcs.TYPES.2022.10/LIPIcs.TYPES.2022.10.pdf
Altenkirch 10:2
-/

/-
A very dependent type has a "placeholder" value which is substitutable as the "very dependent" value.
An example is given below of a "very dependent" sigma type.
-/
class VeryDependent.{u, v} (A : Type u) (G : A → Type v) where
  a : A -- Placeholder
  x : G a
  α : ⦃a : A⦄ → G a → A
  heq : a = α x

namespace VeryDependent

instance Setoid.{u, v} (A : Type u) (G : A → Type v) : Setoid (VeryDependent.{u, v} A G) where
  r X Y := X = Y
  iseqv := {
    refl _ := Eq.refl _
    symm := (·.symm)
    trans _ _ := Eq.trans (by assumption) (by assumption)
  }

def up.{u, v} (A : Type u) (G : A → Type v) : VeryDependent.{u, v} A G →
  Quotient (VeryDependent.Setoid A G) := (Quotient.mk _ ·)

end VeryDependent

/-
P 10:6 Altenkirch. Dependent pairs without using our VeryDependent class.
-/

abbrev DPair.choose.{u} (A : Type u) (B : A → Type u) (h : A) (b : Bool) : Type u := if b then A else B h

structure DPair.{u} (A : Type u) (B : A → Type u) where
  h   : A
  f   : ∀ (b : Bool), if b then A else B h
  heq : h = f true

namespace DPair

def mk'.{u} (A : Type u) (B : A → Type u) (a : A) (b : B a) : DPair.{u} A B where
  h := a
  f := fun x => match x with
  | true => a
  | false => b
  heq := rfl

instance VeryDependent.{u} (A : Type u) (B : A → Type u) (e : DPair A B) : VeryDependent A B where
  a := e.h
  x := e.f false
  α o _ := o
  heq := rfl

def equivSigma.toFun.{u} (A : Type u) (B : A → Type u) : Sigma B → DPair A B := Sigma.uncurry (mk' A B)

def equivSigma.invFun.{u} (A : Type u) (B : A → Type u) (e : DPair A B) : Sigma B := ⟨e.h, e.f false⟩

instance equivSigma.{u} (A : Type u) (B : A → Type u) : Sigma B ≃ DPair A B where
  toFun := equivSigma.toFun A B
  invFun := equivSigma.invFun A B
  right_inv e := match e with
    | .mk h f heq => by
      simp only [equivSigma.toFun, equivSigma.invFun, Sigma.uncurry, mk', mk.injEq, heq_eq_eq, true_and]
      funext
      split
      exact heq
      rfl

end DPair

