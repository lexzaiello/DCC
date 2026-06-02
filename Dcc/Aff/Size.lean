import Dcc.Attrs
import Dcc.Ast
import Dcc.Relation
import Mathlib.Data.Nat.Notation

namespace Expr

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind] def size (e : Expr) : ℕ :=
  match e with
  | DCC ∗ => 0
  | DCC ⊤ => 2
  | DCC ⊥ => 2
  | DCC x = _y => x.size
  | DCC Eql(α)  => α.size + 1
  | DCC refl(α) => α.size + 1
  | DCC Sort m => m
  | DCC Σ(α, β) => α.size + β.size + 1
  | DCC `(_β, x) => x.size + 1
  | DCC ⟦_β⟧(x, y) => x.size + y.size
  | DCC Coup(β) => β.size
  | DCC Id(_α)      => 1
  | DCC Fstc(_α)    => 1
  | DCC Sndc(_α)    => 1
  | DCC Π(_α, β) => β.size + 1
  | DCC (f ∘' g) => f.size + f.size + g.size + 1
  | DCC (f ∘ g)  => f.size + f.size + g.size + 1
  | DCC ⟦_β⟧⟨a, b⟩   => a.size + a.size + b.size + 2
  | DCC Λ(_α, _β, x) => x.size + 1
  | DCC !Λ(_α, _β, x) => x.size + 1
  | DCC Eval(_α, _β, x) => x.size + 1
  | DCC !(x)   => x.size + x.size + 1
  | DCC *(α)   => α.size + 1
  | DCC &(x)   => x.size + x.size + x.size + 1
  | DCC !<x>   => x.size + x.size + x.size + 1
  | DCC $<x>   => x.size + x.size + x.size + 1
  | DCC (f x) => f.size + x.size

end Expr
