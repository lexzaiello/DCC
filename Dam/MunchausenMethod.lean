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
P 10:6 Altenkirch. Dependent pairs.
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

instance instVeryDependent.{u} (A : Type u) (B : A → Type u) (e : DPair A B) : VeryDependent A B where
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

namespace Comb

/-
Dependently-typed combinators:
-/

/-
A language with a sort for terms indexed by types.
-/
class TyUniv.{u} where
  Ty : Type u
  Tm : Ty → Type u
  U : Ty
  heq : Tm U = Ty

/-
A language with pi types and rules for applying families and terms
-/
class AppLang.{u} extends TyUniv.{u} where
  Fam     : Ty
    → Ty
  app_fam : Tm (Fam X)
    → Tm X
    → Ty
  Pi      : (X : Ty)
    → Tm (Fam (Fam X))
  app     {X : Ty} {Y : Tm (Fam X)} : Tm (app_fam (Pi X) Y)
    → (a : Tm X)
    → Tm (app_fam Y a)

infixl:65 " $f " => AppLang.app_fam
infixl:65 " $. " => AppLang.app

class FamLang.{u} extends AppLang.{u} where
  fam_of_ty : (Y : Ty) → Tm (Fam X)
  step_fam_of_ty : ∀ {a : Tm X}, (fam_of_ty Y) $f a = Y

abbrev arr [h : FamLang.{u}] (X Y : h.Ty) : h.Ty := h.Pi X $f (h.fam_of_ty Y)

infixr:65 " ⇒ " => arr

class CombLang.{u} extends FamLang.{u} where
  /-
    Helper "meta combinator" for K's type
  -/
  k_ty_comb : ∀ X (_Y : Tm (Fam X)), (Z : Ty) → Tm (Fam X)
  step_k_ty_comb : ∀ X Y Z {x : Tm X}, k_ty_comb X Y Z $f x = ((Y $f x) ⇒ Z)

  k_comb : {Y : Tm (Fam X)} → Tm (Pi X $f (k_ty_comb X Y X))
  step_k_comb : ∀ {Y : Tm (Fam X)} {x : Tm X} {y : Tm (Y $f x)}, (by
    have h := (@k_comb X Y) $. x
    rw [step_k_ty_comb] at h
    have h' := h $. y
    change TyUniv.Tm (app_fam (fam_of_ty X) y) at h'
    rw [@step_fam_of_ty _ X y] at h'
    exact h' = x
  )

class SLang.{u} extends CombLang.{u} where
  

end Comb
