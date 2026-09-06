import Dcc.Attrs
import Dcc.Ast

/-
A measure of term size which decreases under the affine and eta reduction rules counted like such:

- AST terms which are combinators count themselves as an operation + 1
- Boxed terms are counted thrice, since pairs duplicate
  - ⟦β⟧⟨M, N⟩ &(x) = (M x, N x (M x))
- Computationally irrelevant points (e.g., type arguments) are also counted when
  they have relevance to eta reduction
- No terms have a size of zero, except injected constants (e.g., holes in eta reduction)
-/

namespace GenericExpr

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def size.{u} {τ : Type u} (e : GenericExpr τ) : ℕ :=
  match e with
  | DCC[.] Dom(x) => x.size
  | DCC[.] ∗ => 1
  | DCC[.] ⊤ => 2
  | DCC[.] ⊥ => 2
  | DCC[.] x = y => (x.size + y.size) + 1
  | DCC[.] Eql(α)  => α.size * 2 + 5
  | DCC[.] refl(α) => α.size * 2 + 5
  | DCC[.] Sort m => m
  | DCC[.] Σ(α, β) => α.size + (β.size + 1) * 6 + 5
  | DCC[.] `(β, x) => β.size + x.size + 1
  | DCC[.] ⟦β⟧(x, y) => β.size + x.size + y.size
  | DCC[.] Coup(β) => β.size + 1
  | DCC[.] Id(α)      => α.size + 1
  | DCC[.] Fst(α)    => α.size + 2
  | DCC[.] Snd(α)    => α.size + 2
  | DCC[.] Π(α, β) => α.size + β.size + 2
  | DCC[.] (f ∘ g)  => f.size + f.size + g.size + 3
  | DCC[.] ⟦β⟧⟨a, b⟩   => β.size + a.size + a.size + b.size + 3
  | DCC[.] Λ(α, β, x) => α.size + β.size * 2 + x.size + 3
  | DCC[.] !Λ(α, β, x) => α.size + (5 * β.size) + x.size + 3
  | DCC[.] Eval(α, β, x) => α.size + β.size + x.size + 4
  | DCC[.] !(x)   => x.size + 1
  | DCC[.] *<x>   => 10 * x.size + 4
  | DCC[.] &(x)   => 5 * x.size
  | DCC[.] !<x>   => x.size + x.size + x.size + 4
  | DCC[.] $<x>   => 5 * x.size + 4
  | DCC[.] (f x) => f.size + x.size
  | .const _ => 0
  | .hole _ => 0

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def head_arity.{u} {τ : Type u} (e : GenericExpr τ) : ℕ :=
  match e with
  | DCC[.] Dom(_x) => 0
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
  | DCC[.] Fst(_α)    => 1
  | DCC[.] Snd(_α)    => 1
  | DCC[.] Π(_α, _β) => 1
  | DCC[.] (_f ∘ _g)  => 1
  | DCC[.] ⟦_β⟧⟨_a, _b⟩ => 1
  | DCC[.] Λ(_α, _β, _x) => 2
  | DCC[.] !Λ(_α, _β, _x) => 2
  | DCC[.] Eval(_α, _β, _x) => 1
  | DCC[.] !(_x)   => 0
  | DCC[.] *<_α>   => 1
  | DCC[.] &(_x)   => 0
  | DCC[.] !<_x>   => 1
  | DCC[.] $<_x>   => 1
  | DCC[.] (f _x) => f.head_arity - 1
  | .const _ => 0
  | .hole _ => 0

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def composite_size.{u} {τ : Type u} (e : GenericExpr τ) : ℕ := e.size + e.head_arity

end GenericExpr
