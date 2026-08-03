import Dcc.Eta.Nbe.Canonicalize

namespace NormExpr

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace EtaFn

def unique (h₁ : EtaFn (τ_c := τ_c) f doms₁) (h₂ : EtaFn (τ_c := τ_c) f doms₂) : doms₁ = doms₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  grind

def hole_same (e_f₁ : EtaFn (τ_c := τ_c) f doms) (e_f₂ : EtaFn (τ_c := τ_c) f' doms) (e_h₁ : e_f₁.Holes level h₁) (e_h₂ : e_f₂.Holes level h₂) : h₁ = h₂ := by
  cases e_h₁ with
  | tm₁ =>
    cases e_h₂ with
    | tm₁ =>
      rename_i e_h₁ _ e_h₂
      simp [Hole.unique e_h₁ e_h₂]
  | tm₂ =>
    cases e_h₂ with
    | tm₂ =>
      rename_i hrt₁ e_h₁ e_h₂ _ _ _ _ _ hrt₂ e_h₃ e_h₄
      have ha := hrt₁.complete
      have hb := hrt₂.complete
      cases Hole.unique e_h₁ e_h₄
      cases Hole.unique e_h₂ (ha.symm.trans hb ▸ e_h₃)
      rfl

namespace Canonicalize

def preservation₁ {e_f₁ : EtaFn (τ_c := τ_c) f [α]} {e_f₂ : EtaFn (τ_c := τ_c) f' [α]} (h₁ : Canonicalize e_f₁ e_f₂) : Domain f' α := by
  cases e_f₂
  · assumption

def preservation₂ {e_f₁ : EtaFn (τ_c := τ_c) f [α, β]} {e_f₂ : EtaFn (τ_c := τ_c) f' [α, β]} (h₁ : Canonicalize e_f₁ e_f₂) : Domain₂ f' α β := by
  cases e_f₂
  · assumption

set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
def is_norm_fn {e_f₁ : EtaFn (τ_c := τ_c) f₁ doms} {e_f₂ : EtaFn (τ_c := τ_c) f₂ doms}
  {e_f₃ : EtaFn (τ_c := τ_c) f₃ doms} (h₁ : Canonicalize e_f₁ e_f₂) (h₂ : Canonicalize e_f₂ e_f₃) : f₂ = f₃ := by
  match h₁ with
  | .id₁ _ _ _ _ =>
    match h₂ with
    | .id₁ _ _ _ _ => rfl
    | .quot₁ _ _ _ _ _ =>
      expose_names
      have hrt' : (α.id.app hole₁_1).RedAffNorm ⟨hole₁_1, hn_hole₁_1⟩ :=
        ⟨.single .id, hn_hole₁_1⟩
      have h_mem := e_h.hole_mem_tm ⟨0, e_f₁.arity_pos⟩
      have e_f_heq := e_f₁_2.unique e_f₁
      cases e_f_heq
      have heq := GenericExpr.RedAffNorm.unique hrt' hr_τ
      simp_all
      simp [raw, Holes.v_elems, Vector.get] at h_mem
      have hole_eq := e_f₁_2.hole_same (.tm₁ (Domain.id ⟨.refl, by assumption⟩)) e_h e_h_1
      cases hole_eq
      cases heq
      grind
    | .fstc _ _ _ =>
      expose_names
      have hrt' : ((NormExpr.mk β.coup.id (fun x =>
              match x with
              | Exists.intro w h => nomatch h)).raw.app (β.mkc a_1 b)).RedAffNorm
        (mk (β.mkc a_1 b) hn_hole₁_1) :=
        ⟨.single .id, hn_hole₁_1⟩
      dcc_aesop
    | _ => sorry
  | _ => sorry

end Canonicalize

end EtaFn

end NormExpr
