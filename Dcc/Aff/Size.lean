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
  | DCC x = y => x.size + y.size
  | DCC Eql(α)  => α.size + 3
  | DCC refl(α) => α.size + 3
  | DCC Sort m => m
  | DCC Σ(α, β) => α.size + β.size + 2
  | DCC `(_β, x) => x.size + 2
  | DCC ⟦_β⟧(x, y) => x.size + y.size
  | DCC Coup(β) => β.size
  | DCC Id(_α)      => 2
  | DCC Fstc(_α)    => 2
  | DCC Sndc(_α)    => 2
  | DCC Π(α, β) => α.size + β.size + 1
  | DCC (f ∘' g) => f.size + f.size + g.size + 2
  | DCC (f ∘ g)  => f.size + f.size + g.size + 2
  | DCC (f ∘∘ g)  => f.size + f.size + g.size + 2
  | DCC ⟦_β⟧⟨a, b⟩   => a.size + a.size + b.size + 2
  | DCC Λ(α, β, x) => α.size + β.size + x.size + 2
  | DCC !Λ(α, β, x) => α.size + β.size + x.size + 2
  | DCC Eval(_α, _β, x) => x.size + 1
  | DCC !(x)   => x.size
  | DCC *(α)   => α.size + 1
  | DCC &(x)   => x.size + x.size + x.size + 2
  | DCC !<x>   => x.size + x.size + x.size + 2
  | DCC $<x>   => x.size + x.size + x.size + 2
  | DCC (f x) => f.size + x.size

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind] def head_arity (e : Expr) : ℕ :=
  match e with
  | DCC ∗
  | DCC ⊤
  | DCC ⊥
  | DCC _x = _y => 0
  | DCC Eql(_α)
  | DCC refl(_α) => 2
  | DCC Sort _m => 0
  | DCC Σ(_α, _β) => 1
  | DCC `(_β, _x) => 1
  | DCC ⟦_β⟧(_x, _y) => 0
  | DCC Coup(_β) => 0
  | DCC Id(_α)      => 1
  | DCC Fstc(_α)    => 1
  | DCC Sndc(_α)    => 1
  | DCC Π(_α, _β) => 1
  | DCC (_f ∘' _g) => 1
  | DCC (_f ∘ _g)  => 1
  | DCC (_f ∘∘ _g)  => 1
  | DCC ⟦_β⟧⟨_a, _b⟩ => 1
  | DCC Λ(_α, _β, _x) => 2
  | DCC !Λ(_α, _β, _x) => 2
  | DCC Eval(_α, _β, _x) => 1
  | DCC !(_x)   => 0
  | DCC *(_α)   => 1
  | DCC &(_x)   => 0
  | DCC !<_x>   => 1
  | DCC $<_x>   => 1
  | DCC (f _x) => f.head_arity - 1

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def composite_size (e : Expr) : ℕ := e.size + e.head_arity

end Expr
