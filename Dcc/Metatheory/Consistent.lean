import Dcc.Metatheory.Progress

namespace Expr

namespace Judge

def elim_bot (ht : Judge e (DCC 𝟘)) : False := by
  have h := ht.progress
  match h with
  | .inl hv => exact elim_bot_value (by assumption) (by assumption)
  | .inr ⟨e', hr⟩ =>
    have h_dec := hr.decreasing
    have ht' := preservation ht hr
    exact elim_bot ht'
termination_by e.size

end Judge

end Expr
