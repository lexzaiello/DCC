import Dcc.Eta.Nbe.Canonicalize

namespace NormExpr

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace EtaFn

namespace Canonicalize

def is_norm_fn {e_f₁ : EtaFn (τ_c := τ_c) f₁ doms} {e_f₂ : EtaFn (τ_c := τ_c) f₂ doms}
  {e_f₃ : EtaFn (τ_c := τ_c) f₃ doms} (h₁ : Canonicalize e_f₁ e_f₂) (h₂ : Canonicalize e_f₂ e_f₃) : f₂ = f₃ := by
  cases h₁ with
  | id₁ =>
    cases h₂ with
    | id₁ => rfl
    | quot₁ =>
      expose_names
      have hrt' : (α.id.app hole₁_1).RedAffNorm ⟨hole₁_1, hn_hole₁_1⟩ :=
        ⟨.single .id, hn_hole₁_1⟩
      
      sorry

end Canonicalize

end EtaFn

end NormExpr
