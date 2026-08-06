import Dcc.Eta.Nbe.Canonicalize
import Dcc.Eta.Nbe.Normal

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

open NormExpr

/-
eta-reduce all points, then canonicalize again
-/

inductive RedAll : (e : @GenericExpr τ_c) → (e' : @GenericExpr τ_c) → Type (u + 1)
  | pi₁  : (hrt₁ : RedAffNorm f_α f_α₁)
    → (h_dom : Domain (τ_c := τ_c) f_α₁ ⟨δ, hn_δ⟩)
    → (hr₁   : RedAll f_α f_α')
    → (hr₂   : RedAll env env')
    → (hr₃   : RedAffNorm (DCC? (f_β env)) ⟨f_β_env, hn_f_β_env⟩)
    → (hr₄   : RedAll f_β_env f_β')
    → RedAll (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', `(δ, f_β')) env'))
  | pi₂    : (hrt₁ : RedAffNorm f_α f_α₁)
    → (hn_dom : ∀ {δ}, Domain f_α₁ δ → PEmpty.{u + 1})
    → (hr₁ : RedAll f_α f_α')
    → (hr₂ : RedAll env env')
    → (hr₄ : RedAll f_β f_β')
    → RedAll (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', f_β') env'))
  | pi₃  : (hr₁ : RedAll (DCC? (f_α ∘' g)) f_α')
    → (hr₂ : RedAll (DCC? (f_β ∘' g)) f_β')
    → RedAll (DCC? Π(f_α, f_β) ∘' g) (DCC? (Π(f_α', f_β')))
  | pi₄  : (hr₁ : RedAll f_α f_α') → (hr₂ : RedAll f_β f_β') → RedAll (DCC? Π(f_α, f_β)) (DCC? Π(f_α', f_β'))
  | coup : (hr₁ : RedAll β β') → RedAll (DCC? Coup(β)) (DCC? Coup(β'))
  | bang : (hr₁ : RedAll β β') → RedAll (DCC? !(β)) (DCC? !(β'))
  | tm   : (hn  : ViewEta f → False) → f.Canonicalize! f' → RedAll f f'

def red_all (e : @GenericExpr τ_c) : ((e' : @GenericExpr τ_c) × (RedAll e e')) :=
  match heq : e.view_eta? with
  | .some (.pi_type (f_α := f_α) (f_β := f_β) (env := env)) =>
    match h_dom_eq : (red_aff (A := f_α)).domain? with
    | .some ⟨δ, h_dom⟩ =>
      have h_dec := (aff_sound (A := f_α) rfl).decreasing?
      ⟨_, .pi₁
        (aff_sound rfl)
        h_dom
        f_α.red_all.snd
        env.red_all.snd
        (aff_sound rfl)
        (reduce RedAff (f_β.app env)).fst.red_all.snd⟩
    | .none => ⟨_, .pi₂
      (aff_sound rfl)
      (fun h => by
        have h := h.complete
        grind)
        f_α.red_all.snd
        env.red_all.snd
        f_β.red_all.snd⟩
  | .some (.pi_comp (f_α := f_α) (f_β := f_β) (g := g)) => ⟨_, .pi₃ (DCC? (f_α ∘' g)).red_all.snd  (DCC? (f_β ∘' g)).red_all.snd ⟩
  | .some (.pi (f_α := f_α) (f_β := f_β)) => ⟨_, .pi₄ f_α.red_all.snd f_β.red_all.snd⟩
  | .some (.coup (β := β)) => ⟨.coup β.red_all.fst, .coup β.red_all.snd⟩
  | .some (.bang (β := β)) => ⟨.bang β.red_all.fst, .bang β.red_all.snd⟩
  | .none => ⟨_, .tm (view_eta?_none_sound (by grind)) e.canonicalize!.snd⟩
termination_by size e
decreasing_by all_goals (grind)

end GenericExpr
