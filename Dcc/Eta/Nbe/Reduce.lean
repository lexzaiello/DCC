import Dcc.Eta.Nbe.Canonicalize
import Dcc.Eta.Nbe.Normal

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

open NormExpr

/-
eta-reduce all points, then canonicalize again
-/

inductive RedEta : (e : @GenericExpr τ_c) → (e' : @GenericExpr τ_c) → Type (u + 1)
  | pi₁  : (hrt₁ : RedAffNorm f_α f_α₁)
    → (h_dom : Domain (τ_c := τ_c) f_α₁ ⟨δ, hn_δ⟩)
    → (hr₁   : RedEta f_α f_α')
    → (hr₂   : RedEta env env')
    → (hr₃   : RedAffNorm (DCC? (f_β env)) ⟨f_β_env, hn_f_β_env⟩)
    → (hr₄   : RedEta f_β_env f_β')
    → RedEta (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', `(δ, f_β')) env'))
  | pi₂    : (hrt₁ : RedAffNorm f_α f_α₁)
    → (hn_dom : ∀ {δ}, Domain f_α₁ δ → PEmpty.{u + 1})
    → (hr₁ : RedEta f_α f_α')
    → (hr₂ : RedEta env env')
    → (hr₄ : RedEta f_β f_β')
    → RedEta (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', f_β') env'))
  | pi₃  : (hr₁ : RedEta (DCC? (f_α ∘' g)) f_α')
    → (hr₂ : RedEta (DCC? (f_β ∘' g)) f_β')
    → RedEta (DCC? Π(f_α, f_β) ∘' g) (DCC? (Π(f_α', f_β')))
  | pi₄  : (hr₁ : RedEta f_α f_α') → (hr₂ : RedEta f_β f_β') → RedEta (DCC? Π(f_α, f_β)) (DCC? Π(f_α', f_β'))
  | coup : (hr₁ : RedEta β β') → RedEta (DCC? Coup(β)) (DCC? Coup(β'))
  | bang : (hr₁ : RedEta β β') → RedEta (DCC? !(β)) (DCC? !(β'))
  | tm   : (hn  : ViewEta f → False) → f.Canonicalize! f' → RedEta f f'

def red_eta (e : @GenericExpr τ_c) : ((e' : @GenericExpr τ_c) × (RedEta e e')) :=
  match heq : e.view_eta? with
  | .some (.pi_type (f_α := f_α) (f_β := f_β) (env := env)) =>
    match h_dom_eq : (red_aff (A := f_α)).domain? with
    | .some ⟨δ, h_dom⟩ =>
      have h_dec := (aff_sound (A := f_α) rfl).decreasing?
      ⟨_, .pi₁
        (aff_sound rfl)
        h_dom
        f_α.red_eta.snd
        env.red_eta.snd
        (aff_sound rfl)
        (reduce RedAff (f_β.app env)).fst.red_eta.snd⟩
    | .none => ⟨_, .pi₂
      (aff_sound rfl)
      (fun h => by
        have h := h.complete
        grind)
        f_α.red_eta.snd
        env.red_eta.snd
        f_β.red_eta.snd⟩
  | .some (.pi_comp (f_α := f_α) (f_β := f_β) (g := g)) => ⟨_, .pi₃ (DCC? (f_α ∘' g)).red_eta.snd  (DCC? (f_β ∘' g)).red_eta.snd ⟩
  | .some (.pi (f_α := f_α) (f_β := f_β)) => ⟨_, .pi₄ f_α.red_eta.snd f_β.red_eta.snd⟩
  | .some (.coup (β := β)) => ⟨.coup β.red_eta.fst, .coup β.red_eta.snd⟩
  | .some (.bang (β := β)) => ⟨.bang β.red_eta.fst, .bang β.red_eta.snd⟩
  | .none => ⟨_, .tm (view_eta?_none_sound (by grind)) e.canonicalize!.snd⟩
termination_by size e
decreasing_by all_goals (grind)

def RedEta.complete (h : RedEta (τ_c := τ_c) e e') : red_eta e = ⟨e', h⟩ := by
  induction h with
  | pi₁ =>
    expose_names
    have heq₁ := hrt₁.complete
    have heq₂ := hr₃.complete
    cases heq₁
    have heq_dom := h_dom.complete
    simp [red_eta, view_eta?]
    split
    case h_1 h_dom₂ heq₃ =>
      cases heq_dom.symm.trans heq₃
      cases hr₃.complete
      cases heq₂
      simp [hr₁_ih, hr₂_ih, hr₄_ih, hrt₁.eq, hr₃.eq]
      have heq_whole₁ := (Sigma.mk f_α' hr₁).ext_iff.mp hr₁_ih.symm
      have heq_whole₂ := (Sigma.mk env' hr₂).ext_iff.mp hr₂_ih.symm
      grind
    · grind
  | pi₂ =>
    expose_names
    have heq₁ := hrt₁.complete
    cases heq₁
    let h_dom_eq : f_α.red_aff.domain? = .none := by
      apply Option.eq_none_iff_forall_ne_some.mpr
      intro h heq
      cases hn_dom h.snd
    simp [red_eta, view_eta?]
    split
    · grind
    case h_2 =>
      expose_names
      simp [hr₁_ih, hr₂_ih, hr₄_ih, hrt₁.eq]
      have heq_whole₁ := (Sigma.mk f_α' hr₁).ext_iff.mp hr₁_ih.symm
      have heq_whole₂ := (Sigma.mk env' hr₂).ext_iff.mp hr₂_ih.symm
      have heq_whole₃ := (Sigma.mk f_β' hr₄).ext_iff.mp hr₄_ih.symm
      simp at heq_whole₁
      simp at heq_whole₂
      simp at heq_whole₃
      cases heq_whole₁.left
      cases heq_whole₂.left
      cases heq_whole₃.left
      cases heq_whole₁.right
      cases heq_whole₂.right
      cases heq_whole₃.right
      congr
      grind
  | pi₄ | pi₃ =>
    expose_names
    simp [red_eta]
    simp only [view_eta?]
    simp [hr₁_ih, hr₂_ih]
    grind
  | bang | coup =>
    expose_names
    simp [red_eta]
    simp only [view_eta?]
    simp [hr₁_ih]
    grind
  | tm =>
    expose_names
    have ha := a.complete
    simp [red_eta]
    simp only [view_eta?]
    grind

#eval (red_eta (DCC (Id(Sort 0) ∘' Id(Sort 0)))).fst
#eval (red_eta (DCC Π(Id(Sort 0) ∘' Id(Sort 0), `(Sort 0, `(Sort 0, Sort 0))))).fst

end GenericExpr
