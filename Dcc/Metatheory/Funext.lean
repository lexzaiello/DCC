import Dcc.Judge3
import Dcc.Eta.Nbe.Funext.Binary
import Dcc.Eta.Nbe.Funext.Unary

open GenericExpr

variable {τ_c : Type u}
variable [DecidableEq τ_c]
variable [BEq τ_c]

namespace NormExpr

namespace EtaFn

def has_canonicalize (e_f : EtaFn f doms) : ((f' : NormExpr RedAff) × (e_f' : EtaFn f' doms) × Canonicalize e_f e_f') := by
  sorry

end EtaFn

end NormExpr

namespace GenericExpr

namespace IsNorm

def mk_map (h : IsNorm RedAff x) : IsNorm RedAff (.map x) := fun ⟨_, h⟩ => by
  cases h with
  | map₀ hr => exact h ⟨_, hr⟩

end IsNorm

namespace RedAffNorm

/-theorem map_point (h : RedAffNorm (τ_c := τ_c) (.map x) B) : ∃ (x' : NormExpr RedAff) (hrn : RedAffNorm x x'), (B = ⟨(.map x'.raw), x'.is_norm.mk_map⟩) := by
  match h with
  | ⟨hr, hn⟩ =>
    match hr.cases_head with
    | .inl h =>
      sorry-/

end RedAffNorm

def id_norm    : IsNorm RedAff (DCC? Id(α))       := fun ⟨_, h⟩ => by cases h
def curr_norm  : IsNorm RedAff (DCC? Λ(α, β, x))  := fun ⟨_, h⟩ => by cases h
def curr'_norm : IsNorm RedAff (DCC? !Λ(α, β, x)) := fun ⟨_, h⟩ => by cases h

def pi_norm (hn₁ : IsNorm RedAff f_α) (hn₂ : IsNorm RedAff f_β) (hn₃ : IsNorm RedAff x_α) : IsNorm RedAff (DCC? (Π(f_α, f_β) x_α)) := fun ⟨_, h⟩ => by
  cases h with
  | congrFun h =>
    cases h with
    | pil h =>
      exact hn₁ ⟨_, h⟩
    | pir h =>
      exact hn₂ ⟨_, h⟩
  | congrArg h => exact hn₃ ⟨_, h⟩

def pi_norm' (hn₁ : IsNorm RedAff f_α) (hn₂ : IsNorm RedAff f_β) : IsNorm RedAff (DCC? Π(f_α, f_β)) := fun ⟨_, h⟩ => by
  cases h with
  | pil h =>
    exact hn₁ ⟨_, h⟩
  | pir h =>
    exact hn₂ ⟨_, h⟩

namespace Judge

open NormExpr

def dom₁ (h₁ : Judge (τ_c := τ_c) f (DCC? (Π(f_α, f_β) x_α)))
  (h₂ : Judge g (DCC? (Π(f_α, f_β) x_α)))
  (hr₁    : RedAffNorm f f')
  (hr₂    : RedAffNorm g g') : ((α : NormExpr RedAff) × (Domain f' α) × (Domain g' α)) := by
  sorry

def dom₂ (h₁ : Judge (τ_c := τ_c) f (DCC? (Π(f_α, f_β) x_α)))
  (h₂     : Judge g (DCC? (Π(f_α, f_β) x_α)))
  (hr₁    : RedAffNorm f f')
  (h_arr₁ : arity f = 2)
  (h_arr₂ : arity g = 2)
  (hr₂    : RedAffNorm g g') : ((α : NormExpr RedAff) × (β : NormExpr RedAff) × (Domain₂ f' α β) × (Domain₂ g' α β)) := by
  sorry

def fn_arity_pos (h : Judge (τ_c := τ_c) f (DCC? (Π(f_α, f_β) x_α))) : 0 < f.arity := by
  sorry

/-def view_eta_some (h : Judge (τ_c := τ_c) f (DCC? (Π(f_α, f_β) x_α))) (hrt : RedAffNorm f f') : f'.view_eta_fn.isSome := by
  cases h with
  | refl =>
    cases hrt.elim_norm (fun ⟨_, h⟩ => by cases h)
    simp [view_eta_fn]
    unfold arity
    simp [raw]
    sorry-/

--def canonicalize (h : Judge f (DCC? (Π(f_α, f_β) x_α))) (hrt : RedAffNorm f f') : ((e_f' : EtaFn

def all_eta_fn (h₁ : Judge (τ_c := τ_c) f (DCC? (Π(f_α, f_β) x_α))) (hrt : RedAffNorm f f') : ((doms : List (NormExpr RedAff)) × EtaFn f' doms) := by
  sorry

def ext₁ (h₁ : Judge (τ_c := τ_c) f (DCC? (Π(f_α, f_β) x_α))) (h₂ : Judge g (DCC? (Π(f_α, f_β) x_α)))
  (h_arr₁ : f'.arity = 1)
  (h_arr₂ : g'.arity = 1)
  (hr₁    : RedAffNorm f f')
  (hr₂    : RedAffNorm g g')
  (hr₃    : RedAffNorm (DCC? (f'.raw x)) B)
  (hr₄    : RedAffNorm (DCC? (g'.raw x)) B) : f' = g' := by
  --have ⟨doms₁, h₃⟩ := h₁.all_eta_fn (aff_sound' _)
  --have ⟨doms₂, h₄⟩ := h₂.all_eta_fn (aff_sound' _)
  have ⟨α, h_dom₁, h_dom₂⟩ := h₁.dom₁ h₂ hr₁ hr₂
  have h₃ : EtaFn _ _ := .tm₁ h_dom₁ (_heq := by assumption)
  have h₄ : EtaFn _ _ := .tm₁ h_dom₂ (_heq := by assumption)
  have ⟨f'', h₅, h_canon₁⟩ := h₃.has_canonicalize
  have ⟨g'', h₆, h_canon₂⟩ := h₄.has_canonicalize
  have h := h_canon₁.ext (by sorry)
  sorry

def ext (h₁ : Judge (τ_c := τ_c) f (DCC? (Π(f_α, f_β) x_α))) (h₂ : Judge g (DCC? (Π(f_α, f_β) x_α)))
  (hr₁ : RedAffNorm f f')
  (hr₂ : RedAffNorm g g')
  (hr₃ : RedAffNorm (DCC? (f'.raw x)) B)
  (hr₄ : RedAffNorm (DCC? (g'.raw x)) B) : f' = g' := by
  have h₃ := h₁.all_eta_fn (aff_sound' _)
  have h₄ := h₂.all_eta_fn (aff_sound' _)
  
  sorry

end Judge

end GenericExpr

/-
To lift ext from Canonicalize up into Judge, we need:

- All function terms w Judge have a corresponding EtaFn
  - For this, we just need that all Judge have a Domain entry, but this may be hard to prove
- All EtaFn have a canonicalization (e_f.Canonicalize e_f')
- that's all we need
- seemingly will need arity preservation, which is super super annoying
  - might not actually, just depends on eronomics. I think we can let it slide.

I don't think it particularly matters what dom there is, but we need to say that f and g have the same dom.

dom_same

def Judge.all_eta_fn (h₁ : Judge (τ_c := τ_c) f (DCC? (Π(f_α, f_β) x_α))) (hrt : RedAffNorm f f') : ((doms : List NormExpr) × EtaFn f' doms) := by
  sorry

def ext (h₁ : Judge f (DCC? (Π(f_α, f_β) x_α))) (h₂ : Judge g (DCC? (Π(f_α, f_β) x_α)))
  (hr₁ : RedAffNorm f f')
  (hr₂ : RedAffNorm g g')
  (hr₃ : RedAffNorm (DCC? (f' x)) B)
  (hr₄ : RedAffNorm (DCC? (g' x)) B) : f' = g' := by
  sorry

Questions remaining:
- why isn't canonicalize total? Shouldn't EtaFn have all info we need?
  - Assume it doesn't
-/
