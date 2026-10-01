import Dcc.Judge3

namespace GenericExpr

/-

-/

/-
Function extensionality:
∀ (f g : ((Π B₁ C₁) x₁)) (h : ∀ (x : (B₁ x₁)), (f x) = (g x)), f = g

This is due to transport over function equality equivalence.
By refl, (f = f) and (g = g).
Since h, (f = f) ≃ (g = g).
And due to (≃.1 (f = f) (g = g)), (f = g).
-/

end GenericExpr
