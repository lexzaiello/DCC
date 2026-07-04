import Dcc.Attrs
import Dcc.Ast
import Dcc.Relation
import Mathlib.Data.Nat.Notation

namespace GenericExpr

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def size.{u} {τ : Type u} (e : GenericExpr τ) : ℕ :=
  match e with
  | DCC[.] ∗ => 1
  | DCC[.] ⊤ => 2
  | DCC[.] ⊥ => 2
  | DCC[.] x = y => x.size + y.size
  | DCC[.] Eql(α)  => α.size + 4
  | DCC[.] refl(α) => α.size + 3
  | DCC[.] Sort m => m
  | DCC[.] Σ(α, β) => α.size + β.size + 3
  | DCC[.] `(β, x) => β.size + x.size + 3
  | DCC[.] ⟦_β⟧(x, y) => x.size + y.size
  | DCC[.] Coup(β) => β.size + 1
  | DCC[.] Id(α)      => 1 + α.size
  | DCC[.] Fstc(α)    => 3 + α.size
  | DCC[.] Sndc(α)    => 3 + α.size
  | DCC[.] Π(α, β) => α.size + β.size + 2
  | DCC[.] (f ∘' g) => f.size + f.size + g.size + 3
  | DCC[.] (f ∘ g)  => f.size + f.size + g.size + 3
  | DCC[.] (f ∘∘ g)  => f.size + f.size + g.size + 3
  | DCC[.] ⟦_β⟧⟨a, b⟩   => a.size + a.size + b.size + 3
  | DCC[.] Λ(α, β, x) => α.size + β.size + x.size + 3
  | DCC[.] !Λ(α, β, x) => α.size + β.size + x.size + 3
  | DCC[.] Eval(_α, _β, x) => x.size + 2
  | DCC[.] !(x)   => x.size
  | DCC[.] *(α)   => α.size + 3
  | DCC[.] *<α>   => α.size + 1
  | DCC[.] &(x)   => x.size + x.size + x.size + x.size
  | DCC[.] !<x>   => x.size + x.size + x.size + 3
  | DCC[.] $<x>   => x.size + x.size + x.size + x.size + 3
  | DCC[.] (f x) => f.size + x.size
  | .const _ => 0

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def head_arity.{u} {τ : Type u} (e : GenericExpr τ) : ℕ :=
  match e with
  | DCC[.] ∗
  | DCC[.] ⊤
  | DCC[.] ⊥
  | DCC[.] _x = _y => 0
  | DCC[.] Eql(_α)
  | DCC[.] refl(_α) => 2
  | DCC[.] Sort _m => 0
  | DCC[.] Σ(_α, _β) => 1
  | DCC[.] `(_β, _x) => 1
  | DCC[.] ⟦_β⟧(_x, _y) => 0
  | DCC[.] Coup(_β) => 0
  | DCC[.] Id(_α)      => 1
  | DCC[.] Fstc(_α)    => 1
  | DCC[.] Sndc(_α)    => 1
  | DCC[.] Π(_α, _β) => 1
  | DCC[.] (_f ∘' _g) => 1
  | DCC[.] (_f ∘ _g)  => 1
  | DCC[.] (_f ∘∘ _g)  => 1
  | DCC[.] ⟦_β⟧⟨_a, _b⟩ => 1
  | DCC[.] Λ(_α, _β, _x) => 2
  | DCC[.] !Λ(_α, _β, _x) => 2
  | DCC[.] Eval(_α, _β, _x) => 1
  | DCC[.] !(_x)   => 0
  | DCC[.] *(_α)   => 1
  | DCC[.] *<_α>   => 1
  | DCC[.] &(_x)   => 0
  | DCC[.] !<_x>   => 1
  | DCC[.] $<_x>   => 1
  | DCC[.] (f _x) => f.head_arity - 1
  | .const _ => 0

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def composite_size.{u} {τ : Type u} (e : GenericExpr τ) : ℕ := e.size + e.head_arity

end GenericExpr
