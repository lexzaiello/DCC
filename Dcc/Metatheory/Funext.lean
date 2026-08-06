import Dcc.Judge3

variable {τ_c : Type u}
variable [DecidableEq τ_c]
variable [BEq τ_c]

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

/-def view_eta_some (h : Judge (τ_c := τ_c) f (DCC? (Π(f_α, f_β) x_α))) (hrt : RedAffNorm f f') : f'.view_eta_fn.isSome := by
  cases h with
  | refl =>
    cases hrt.elim_norm (fun ⟨_, h⟩ => by cases h)
    simp [view_eta_fn]
    unfold arity
    simp [raw]
    sorry-/

--def canonicalize (h : Judge f (DCC? (Π(f_α, f_β) x_α))) (hrt : RedAffNorm f f') : ((e_f' : EtaFn

end Judge

end GenericExpr
