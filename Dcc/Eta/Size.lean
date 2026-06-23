import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Size
import Dcc.Aff.Red

namespace GenericExpr

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def eta_size.{u} {τ : Type u} (e : GenericExpr τ) : ℕ :=
  match e with
  | DCC[.] ∗ => 0
  | DCC[.] ⊤ => 2
  | DCC[.] ⊥ => 2
  | DCC[.] x = y => x.eta_size + y.eta_size
  | DCC[.] Eql(α)  => α.eta_size + 3
  | DCC[.] refl(α) => α.eta_size + 2
  | DCC[.] Sort m => m
  | DCC[.] Σ(α, β) => α.eta_size + β.eta_size + 2
  | DCC[.] `(_β, x) => x.eta_size + 2
  | DCC[.] ⟦_β⟧(x, y) => x.eta_size + y.eta_size
  | DCC[.] Coup(β) => β.eta_size + 1
  | DCC[.] Id(α)      => 2 + α.eta_size
  | DCC[.] Fstc(α)    => 2 + α.eta_size
  | DCC[.] Sndc(α)    => 2 + α.eta_size
  | DCC[.] Π(α, β) => α.eta_size + β.eta_size + 1
  | DCC[.] (f ∘' g) => f.eta_size + f.eta_size + g.eta_size + 2
  | DCC[.] (f ∘ g)  => f.eta_size + f.eta_size + g.eta_size + 2
  | DCC[.] (f ∘∘ g)  => f.eta_size + f.eta_size + g.eta_size + 2
  | DCC[.] ⟦_β⟧⟨a, b⟩   => a.eta_size + a.eta_size + b.eta_size + 2
  | DCC[.] Λ(α, β, x) => α.eta_size + β.eta_size + x.eta_size + 6
  | DCC[.] !Λ(α, β, x) => α.eta_size + β.eta_size + x.eta_size + 6
  | DCC[.] Eval(_α, _β, x) => x.eta_size + 1
  | DCC[.] !(x)   => x.eta_size + 1
  | DCC[.] *(α)   => α.eta_size + 2
  | DCC[.] &(x)   => x.eta_size + x.eta_size + x.eta_size + 2
  | DCC[.] !<x>   => x.eta_size + x.eta_size + x.eta_size + 2
  | DCC[.] $<x>   => x.eta_size + x.eta_size + x.eta_size + 2
  | DCC[.] (f x) => f.eta_size + x.eta_size
  | .const _ => 0

end GenericExpr
