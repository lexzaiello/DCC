import Dcc.Eta.Nbe.Canonicalize

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace NormExpr

namespace Hole

def app_norm (h₁ : Hole α l₁ a) (h₂ : Hole β l₂ b) : GenericExpr.IsNorm GenericExpr.RedAff (DCC? (a.raw b.raw)) := by
  induction h₁ with
  | pure h_view₁ =>
    induction h₂
    any_goals (
      focus
      try(
        intro ⟨_, hr⟩
        cases hr with
        | congrFun h => cases h
        | congrArg h => cases h)
      done)
    case bang =>
      intro ⟨_, h⟩
      cases h with
      | congrFun h =>
        expose_names
        exact a_ih.congrFun ⟨_, h⟩
      | congrArg h =>
        expose_names
        cases h with
        | box₀ h => exact a_ih.congrArg ⟨_, h⟩
    case coup =>
      intro ⟨_, h⟩
      cases h with
      | congrFun h => cases h
      | congrArg h =>
        cases h with
        | sig₀ h =>
          expose_names
          exact hn_hole₁ ⟨_, h⟩
        | sig₁ h =>
          expose_names
          exact hn_hole₁ ⟨_, h⟩
        | sig₂ h =>
          expose_names
          exact hn_hole₂ ⟨_, h⟩
  | bang h ih =>
    intro ⟨_, h⟩
    cases h with
    | congrFun h =>
      cases h with
      | box₀ h =>
        expose_names
        exact h_1.is_norm ⟨_, h⟩
    | congrArg h =>
      have h := h₂.is_norm
      exact h ⟨_, by assumption⟩
  | coup h_dom h₁ hrt h₂ ih₁ ih₂ =>
    intro ⟨_, h⟩
    cases h with
    | congrFun h =>
      cases h with
      | sig₀ h =>
        exact h₁.is_norm ⟨_, h⟩
      | sig₁ h =>
        exact h₁.is_norm ⟨_, h⟩
      | sig₂ h =>
        exact h₂.is_norm ⟨_, h⟩
    | congrArg h =>
      expose_names
      exact h₂_1.is_norm ⟨_, h⟩

def app_norm_arg (h₁ : Hole α l₁ a) (h₂ : Hole β l₂ b) (hn : GenericExpr.IsNorm GenericExpr.RedAff c) : GenericExpr.IsNorm GenericExpr.RedAff (DCC? (a.raw b.raw c)) := by
  induction h₁ with
  | pure h_view₁ =>
    induction h₂
    any_goals (
      focus
      try (
        intro ⟨_, hr⟩
        cases hr with
        | congrFun h =>
          cases h with
          | congrFun h => cases h
          | congrArg h => cases h
        | congrArg h => exact hn ⟨_, h⟩)
      done)
    case bang hn =>
      intro ⟨_, h⟩
      cases h with
      | congrFun h =>
        cases h with
        | congrFun h =>
          exact hn.congrFun.congrFun ⟨_, h⟩
        | congrArg h =>
          cases h with
          | box₀ h =>
            expose_names
            exact hn_hole ⟨_, h⟩
      | congrArg h => exact hn.congrArg ⟨_, h⟩
    case coup =>
      intro ⟨_, h⟩
      cases h with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h =>
          expose_names
          cases h with
          | sig₀ h => exact a_2.is_norm ⟨_, h⟩
          | sig₁ h =>
            exact a_2.is_norm ⟨_, h⟩
          | sig₂ h => exact a_4.is_norm ⟨_, h⟩
      | congrArg h => exact hn ⟨_, h⟩
  | bang h ih =>
    intro ⟨_, h⟩
    cases h with
    | congrFun h =>
      cases h with
      | congrFun h =>
        cases h with
        | box₀ h =>
          expose_names
          exact h_1.is_norm ⟨_, h⟩
      | congrArg h =>
        exact h₂.is_norm ⟨_, h⟩
    | congrArg h =>
      have h := h₂.is_norm
      exact hn ⟨_, by assumption⟩
  | coup h_dom h₁ hrt h₂ ih₁ ih₂ =>
    intro ⟨_, h⟩
    cases h with
    | congrFun h =>
      cases h with
      | congrFun h =>
        cases h with
        | sig₀ h =>
          exact h₁.is_norm ⟨_, h⟩
        | sig₁ h =>
          exact h₁.is_norm ⟨_, h⟩
        | sig₂ h =>
          exact h₂.is_norm ⟨_, h⟩
      | congrArg h =>
        expose_names
        exact h₂_1.is_norm ⟨_, h⟩
    | congrArg h =>
      expose_names
      exact hn ⟨_, h⟩

@[grind]
def app_norm' {a b : NormExpr GenericExpr.RedAff (τ := (@EtaConst τ_c))} (h₁ : Hole α l₁ a) (h₂ : Hole β l₂ b) : NormExpr (τ := (@EtaConst τ_c)) GenericExpr.RedAff :=
  ⟨DCC? (a.raw b.raw), h₁.app_norm h₂⟩

end Hole

namespace EtaFn

def unique (h₁ : EtaFn (τ_c := τ_c) f doms₁) (h₂ : EtaFn (τ_c := τ_c) f doms₂) : doms₁ = doms₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  grind

def hole_same (e_f₁ : EtaFn (τ_c := τ_c) f doms) (e_f₂ : EtaFn (τ_c := τ_c) f' doms) (e_h₁ : e_f₁.Holes level h₁) (e_h₂ : e_f₂.Holes level h₂) : h₁ = h₂ := by
  cases e_h₁ with
  | tm₁ heq₁ =>
    cases heq₁
    cases e_h₂ with
    | tm₁ heq₂ =>
      cases heq₂
      rename_i e_h₁ _ e_h₂
      simp [Hole.unique e_h₁ e_h₂]

namespace Holes

def hole_same {e_f₁ : EtaFn (τ_c := τ_c) f doms} {e_f₂ : EtaFn (τ_c := τ_c) f' doms} (e_h₁ : e_f₁.Holes level h₁) (e_h₂ : e_f₂.Holes level h₂) : h₁ = h₂ := by
  cases e_h₁ with
  | tm₁ heq₁ =>
    cases heq₁
    cases e_h₂ with
    | tm₁ heq₂ =>
      cases heq₂
      rename_i e_h₁ _ e_h₂
      simp [Hole.unique e_h₁ e_h₂]

def app_coup_norm {e_f : EtaFn (τ_c := τ_c) f doms} (e_h : e_f.Holes level [⟨DCC? ⟦β⟧(a, b), hn⟩]) :
  GenericExpr.IsNorm GenericExpr.RedAff (DCC? (a b)) := by
  cases e_h with
  | tm₁ heq h =>
    cases h with
    | coup h_dom h₁ hrt h₂ =>
      exact h₁.app_norm h₂

/-def app_norm_arg {e_f : EtaFn (τ_c := τ_c) f doms} (e_h : e_f.Holes level [⟨DCC? ⟦β⟧(a, b), hn⟩]) (hn : GenericExpr.IsNorm GenericExpr.RedAff c) :
  GenericExpr.IsNorm GenericExpr.RedAff (DCC? (a b c)) := by
  cases e_h with
  | tm₁ heq h =>
    cases h with
    | coup h_dom h₁ hrt h₂ =>
      have h := h₁.app_norm_arg h₂ hn
      exact h-/

def app_norm {e_f : EtaFn (τ_c := τ_c) f doms} (e_h : e_f.Holes level [⟨a, hn_α⟩, ⟨b, hn_b⟩]) : GenericExpr.IsNorm GenericExpr.RedAff (DCC? (a b)) := by
  cases e_h with

end Holes

namespace Canonicalize

def preservation₁ {e_f₁ : EtaFn (τ_c := τ_c) f [α]} {e_f₂ : EtaFn (τ_c := τ_c) f' [α]} (h₁ : Canonicalize e_f₁ e_f₂) : Domain f' α := by
  cases e_f₂
  · assumption

end Canonicalize

end EtaFn

end NormExpr
