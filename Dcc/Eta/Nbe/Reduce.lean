import Dcc.Eta.Nbe.Canonicalize
import Dcc.Eta.Nbe.Normal

namespace NormExpr

variable {τ_c : Type u}
variable [DecidableEq τ_c]

/-
eta-reduce all points, then canonicalize again
-/
inductive RedEta : (e : GenericExpr (τ := τ_c)) → (e' : GenericExpr (τ := τ_c)) → Type u
  | nil : e.points = #v[] → 

end NormExpr
