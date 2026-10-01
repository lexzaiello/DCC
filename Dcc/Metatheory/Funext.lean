import Dcc.Judge3

universe u
variable {τ_c : Type u} [DecidableEq τ_c]

namespace GenericExpr

open Dsl in
def eq_imp_equiv (ht₁ : Judge (τ_c := τ_c) e (DCC? (= τ x y))) :
  Judge (DCC? ((≃.mk (`⊤ (Id (= τ x x)))
                     (`⊤ (Id (= τ y y)))
                     ((refl (Id Sort 0)) (& (= τ x x)))
                     ((refl (Id Sort 0)) (& (= τ y y)))) ∗))
        (DCC? (≃ (= τ x x) (= τ y y))) := by
  
  sorry

/-
Equality reflection:
If (x = y), then x ≡ y.

This is because x = y implies (≃ (= x x) (= y y))
and (≃ (= x x) (= y y)) implies (= x x) ≡ (= y y)
which implies x ≡ y.
-/

def elim_eq (ht₁ : Judge (τ_c := τ_c) e (DCC? (= τ x y))) : x ≡ y := by
  
  sorry

end GenericExpr
