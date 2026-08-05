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
    case coup =>
      intro ⟨_, h⟩
      cases h with
      | congrFun h => cases h
      | congrArg h =>
        cases h with
        | sigl h =>
          expose_names
          exact hn_hole₁ ⟨_, h⟩
        | sigr h =>
          expose_names
          exact hn_hole₂ ⟨_, h⟩
  | bang h ih =>
    intro ⟨_, h⟩
    cases h with
    | congrFun h => cases h
    | congrArg h =>
      have h := h₂.is_norm
      exact h ⟨_, by assumption⟩
  | coup h_dom h₁ hrt h₂ ih₁ ih₂ =>
    intro ⟨_, h⟩
    cases h with
    | congrFun h =>
      cases h with
      | sigl h =>
        exact h₁.is_norm ⟨_, h⟩
      | sigr h =>
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
    case coup =>
      intro ⟨_, h⟩
      cases h with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h =>
          expose_names
          cases h with
          | sigl h =>
            exact a_2.is_norm ⟨_, h⟩
          | sigr h => exact a_4.is_norm ⟨_, h⟩
      | congrArg h => exact hn ⟨_, h⟩
  | bang h ih =>
    intro ⟨_, h⟩
    cases h with
    | congrFun h =>
      cases h with
      | congrFun h => cases h
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
        | sigl h =>
          exact h₁.is_norm ⟨_, h⟩
        | sigr h =>
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
  | tm₂ heq₁ =>
    cases heq₁
    cases e_h₂ with
    | tm₂ heq₂ =>
      cases heq₂
      rename_i hrt₁ e_h₁ e_h₂ _ _ _ _ _ hrt₂ e_h₃ e_h₄
      have ha := hrt₁.complete
      have hb := hrt₂.complete
      cases e_h₄.unique e_h₂
      simp_all
      cases ha
      cases e_h₁.unique e_h₃
      rfl

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
  | tm₂ heq₁ =>
    cases heq₁
    cases e_h₂ with
    | tm₂ heq₂ =>
      cases heq₂
      rename_i hrt₁ e_h₁ e_h₂ _ _ _ _ _ hrt₂ e_h₃ e_h₄
      have ha := hrt₁.complete
      have hb := hrt₂.complete
      cases e_h₄.unique e_h₂
      simp_all
      cases ha
      cases e_h₁.unique e_h₃
      rfl

def app_coup_norm {e_f : EtaFn (τ_c := τ_c) f doms} (e_h : e_f.Holes level [⟨DCC? ⟦β⟧(a, b), hn⟩]) :
  GenericExpr.IsNorm GenericExpr.RedAff (DCC? (a b)) := by
  cases e_h with
  | tm₁ heq h =>
    cases h with
    | coup h_dom h₁ hrt h₂ =>
      exact h₁.app_norm h₂

def app_norm_arg {e_f : EtaFn (τ_c := τ_c) f doms} (e_h : e_f.Holes level [⟨DCC? ⟦β⟧(a, b), hn⟩]) (hn : GenericExpr.IsNorm GenericExpr.RedAff c) :
  GenericExpr.IsNorm GenericExpr.RedAff (DCC? (a b c)) := by
  cases e_h with
  | tm₁ heq h =>
    cases h with
    | coup h_dom h₁ hrt h₂ =>
      have h := h₁.app_norm_arg h₂ hn
      exact h

end Holes

namespace Canonicalize

def preservation₁ {e_f₁ : EtaFn (τ_c := τ_c) f [α]} {e_f₂ : EtaFn (τ_c := τ_c) f' [α]} (h₁ : Canonicalize e_f₁ e_f₂) : Domain f' α := by
  cases e_f₂
  · assumption

def preservation₂ {e_f₁ : EtaFn (τ_c := τ_c) f [α, β]} {e_f₂ : EtaFn (τ_c := τ_c) f' [α, β]} (h₁ : Canonicalize e_f₁ e_f₂) : Domain₂ f' α β := by
  cases e_f₂
  · assumption

end Canonicalize

end EtaFn

end NormExpr
