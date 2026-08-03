import Dcc.Ast.Core
import Dcc.Ast.Dsl

namespace GenericExpr

@[grind]
def contains {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr (τ := τ_c))
  (to_find : GenericExpr (τ := τ_c)) : Bool :=
  e = to_find ||
  match e, to_find with
  | .const x₁, x₂ => .const x₁ = x₂
  | DCC[.] ∗, DCC[.] ∗ => true
  | DCC[.] ⊤, DCC[.] ⊤ => true
  | DCC[.] Sort _n, DCC[.] Sort __n => true
  | DCC[.] ⊥, DCC[.] ⊥ => true
  | DCC[.] Π(x, y), to_find
  | DCC[.] (x ∘' y), to_find
  | DCC[.] (x ∘ y), to_find
  | DCC[.] (x ∘∘ y), to_find
  | DCC[.] (x y), to_find
  | DCC[.] x = y, to_find => x.contains to_find || y.contains to_find
  | DCC[.] Fstc(α), to_find
  | DCC[.] Sndc(α), to_find
  | DCC[.] Coup(α), to_find
  | DCC[.] &(α), to_find
  | DCC[.] !<α>, to_find
  | DCC[.] $<α>, to_find
  | DCC[.] !(α), to_find
  | DCC[.] *(α), to_find
  | DCC[.] *<α>, to_find
  | DCC[.] Id(α), to_find
  | DCC[.] Eql(α), to_find
  | DCC[.] refl(α), to_find => α.contains to_find
  | DCC[.] Σ(α, β), to_find => α.contains to_find || β.contains to_find
  | DCC[.] `(β, x), to_find => β.contains to_find || x.contains to_find
  | DCC[.] Eval(β, x, y), to_find
  | DCC[.] !Λ(β, x, y), to_find
  | DCC[.] Λ(β, x, y), to_find
  | DCC[.] ⟦β⟧⟨x, y⟩, to_find
  | DCC[.] ⟦β⟧(x, y), to_find => β.contains to_find || x.contains to_find || y.contains to_find
  | _, _ => false

@[grind =]
theorem contains_refl {τ_c : Type u} [DecidableEq τ_c] {e : @GenericExpr τ_c} : contains e e = true := by
  unfold contains
  simp

instance instMemDecEq {τ_c : Type u} [DecidableEq τ_c] : Membership (@GenericExpr τ_c) (@GenericExpr τ_c) where
  mem e to_find := contains e to_find

end GenericExpr
