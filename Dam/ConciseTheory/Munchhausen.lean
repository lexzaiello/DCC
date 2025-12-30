import Dam.Munchhausen.Defs

/-
Dependently-typed combinators:
-/

namespace Comb

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
  s_ty_yx_comb : ∀ X (_Y : Tm (Fam X)), Tm (Fam X)
  step_s_ty_yx_comb : ∀ X Y {x : Tm X}, s_ty_yx_comb X Y $f x = Fam (Y $f x)

  s_π_yx_zx : ∀ X (Y : Tm (Fam X)), (Z : Tm (Pi X $f s_ty_yx_comb X Y)) → Tm (Fam X)
  step_s_π_yx_zx : ∀ X Y Z {x : Tm X}, s_π_yx_zx X Y Z $f x = Pi (Y $f x) $f (by
    have h := Z $. x
    rw [step_s_ty_yx_comb] at h
    exact h
  )

  s_zxgx : ∀ X (Y : Tm (Fam X)) (_Z : Tm (Pi X $f s_ty_yx_comb X Y)),
    Tm (Pi X $f Y) → Tm (Fam X)
  step_s_zxgx : ∀ X Y Z g {x}, s_zxgx X Y Z g $f x = (by
    have f :=  Z $. x
    have a := (g $. x)
    rw [step_s_ty_yx_comb] at f
    exact f $f a
  )

  s_π_x_zx_gx : ∀ X (Y : Tm (Fam X)) (_Z : Tm (Pi X $f s_ty_yx_comb X Y)),
    Tm (Fam (Pi X $f Y))
  step_s_π_x_zx_gx : ∀ X Y Z g, s_π_x_zx_gx X Y Z $f g = Pi X $f (s_zxgx X Y Z g)

  s_comb : {Y : Tm (Fam X)}
    → {Z : Tm (Pi X $f s_ty_yx_comb X Y)}
    → Tm ((Pi X $f s_π_yx_zx X Y Z) ⇒ (Pi (Pi X $f Y) $f (s_π_x_zx_gx X Y Z)))
  step_s_comb : {Y : Tm (Fam X)}
    → {Z : Tm (Pi X $f s_ty_yx_comb X Y)}
    → {f : Tm (Pi X $f s_π_yx_zx X Y Z)}
    → {g : Tm (Pi X $f Y)}
    → {x : Tm X}
    → (by
      -- left side of eq, S f g x
      have h := s_comb $. f
      change TyUniv.Tm (app_fam (fam_of_ty (Pi (Pi X $f Y) $f s_π_x_zx_gx X Y Z)) f) at h
      rw [step_fam_of_ty] at h
      have h' := h $. g
      rw [step_s_π_x_zx_gx] at h'
      have left := h' $. x
      rw [step_s_zxgx] at left

      have right := f $. x
      rw [step_s_π_yx_zx] at right
      have right' :=  right $. (g $. x)

      exact left = right'
    )

/-
Interesting note from the paper:
We need to define
the version of these combinators that internalises this quantification within U. There is
no conceptual problem in doing so, but the resulting terms become incredibly large and
inconvenient to work with. Specifically, the one for the dependent S combinator. It is not
clear whether there is a more elegant way of doing this.
-/

end Comb
