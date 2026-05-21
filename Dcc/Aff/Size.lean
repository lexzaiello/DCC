import Dcc.Attrs
import Dcc.Ast
import Dcc.Relation
import Mathlib.Tactic

namespace Expr

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind] def size (e : Expr) : ℕ :=
  match e with
  | DCC ∗ => 0
  | DCC ⊤ => 0
  | DCC ⊥ => 0
  | DCC =(α)    => α.size + 1
  | DCC Eql(α)  => α.size + 1
  | DCC refl(α) => α.size + 1
  | DCC Subst(x, y) => x.size + x.size + y.size + 3
  | DCC Sort _m => 0
  | DCC Σ(α, β) => α.size + β.size + 1
  | DCC `(_β, x) => x.size + 1
  | DCC ⟦_β⟧(x, y) => x.size + y.size
  | DCC Coup(β) => β.size
  | DCC Id(_α)      => 1
  | DCC Fst(_α, _β) => 1
  | DCC Fstc(_α)    => 1
  | DCC Snd(_α, _β) => 1
  | DCC Sndc(_α)    => 1
  | DCC Π(_α, β) => β.size + 1
  | DCC (f ∘' g) => f.size + f.size + g.size + 1
  | DCC (f ∘ g)  => f.size + f.size + g.size + 1
  | DCC ⟨a, b⟩   => a.size + b.size + 1
  | DCC Λ(_α, _β, x) => x.size + 1
  | DCC (f x) => f.size + x.size

end Expr
