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

namespace Comb

