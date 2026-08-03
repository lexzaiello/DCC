import Dcc.Ast
import Dcc.Types
import Dcc.Judge2
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

namespace GenericExpr

namespace Judge₂

theorem all_sorts.{u} {τ_c : Type u} [DecidableEq τ_c] {e τ : GenericExpr τ_c} (ht : Judge₂ e τ) : (∃ (m : Level), Judge₂ τ (DCC? Sort m)) := by
  induction ht
  any_goals (exact ⟨_, by constructor⟩)
  case refl h_t_f_α harr hr_τ h_t_t_f_α =>
    
    sorry

end Judge₂

end GenericExpr

open CategoryTheory
open GenericExpr

universe u
variable {τ_c : Type u} [DecidableEq τ_c]

def DccObj := ((e τ : GenericExpr τ_c) × (PLift (Judge₂ e τ)))

structure DccHom (X Y : DccObj (τ_c := τ_c)) where
  f     : GenericExpr (τ := τ_c)
  f_α   : GenericExpr (τ := τ_c)
  f_β   : GenericExpr (τ := τ_c)
  x_α   : GenericExpr (τ := τ_c)
  α     : GenericExpr (τ := τ_c)
  β     : GenericExpr (τ := τ_c)
  e     : GenericExpr (τ := τ_c)
  ht    : (Judge₂ e (DCC? (Π(f_α, f_β) x_α)))
  hr₁   : Reduces₂ (DCC? (f_α x_α)) α
  hr₂   : Reduces₂ (DCC? (f_β x_α X.fst)) β
  hdeq₁ : DefEq α τ₁
  hdeq₂ : DefEq β τ₂

instance : Quiver (DccObj (τ_c := τ_c)) := ⟨DccHom⟩

instance : Category (DccObj (τ_c := τ_c)) where
  id := fun ⟨X, τ, ⟨ht⟩⟩ => ⟨DCC? Id(τ), by sorry, by sorry, by sorry, by sorry, by sorry, by sorry, by sorry, by sorry, by sorry, by sorry, by sorry⟩

def DccCat : Category DccObj where
  

def DccCat : MonoidalCategoryStruct DccObj where
  tensorObj := by sorry
