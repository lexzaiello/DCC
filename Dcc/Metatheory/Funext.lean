import Dcc.Judge3

variable {τ_c : Type u}
variable [DecidableEq τ_c]
variable [BEq τ_c]

namespace GenericExpr

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

def eta_fn (h : Judge f (DCC? (Π(f_α, f_β) x_α))) (hrt : RedAffNorm f f') : ((doms : List (@NormExpr τ_c RedAff))
  × EtaFn (τ_c := τ_c) f' doms) := by
  cases h with
  | id =>
    expose_names
    simp [id.type] at a_2
    cases hrt.elim_norm (fun ⟨_, h⟩ => by cases h)
    cases heq : α.view_fn_type? with
    | some h =>
      cases h
      exact ⟨_, .tm₂ (_heq := by grind) (.id (aff_sound rfl) (aff_sound rfl))⟩
    | none =>
      have h := view_fn_type?_none_sound heq
      exact ⟨_, .tm₁ (_heq := by grind) (.id (aff_sound rfl))⟩
  | _ => sorry

def canonicalize (h : Judge f (DCC? (Π(f_α, f_β) x_α))) (hrt : RedAffNorm f f') : ((e_f' : EtaFn

end Judge

end GenericExpr
