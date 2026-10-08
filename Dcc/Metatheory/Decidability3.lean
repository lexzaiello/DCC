import Dcc.Judge3

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

namespace Judge3

set_option maxHeartbeats 20000000000 in
def Judge.complete (h : Judge (τ_c := τ_c) e τ) : e.infer = .ok ⟨τ, h⟩ := by
  induction h <;> (dsimp [infer]; try (dcc_aesop' [reduce]))

end Judge3

end GenericExpr
