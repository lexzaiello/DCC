import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Size
import Dcc.Aff.Red

namespace Expr

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind] def eta_size (e : Expr) : ℕ :=
  match e with
  | DCC ∗ => 0
  | DCC ⊤ => 0
  | DCC ⊥ => 0
  | DCC =(α)    => α.eta_size + 1
  | DCC Eql(α)  => α.eta_size + 1
  | DCC refl(α) => α.eta_size + 1
  | DCC Subst(x, y) => x.eta_size + x.eta_size + y.eta_size + 3
  | DCC Sort _m => 0
  | DCC Σ(α, β) => α.eta_size + β.eta_size + 1
  | DCC `(_β, x) => x.eta_size + 1
  | DCC ⟦_β⟧(x, y) => x.eta_size + y.eta_size
  | DCC Coup(β) => β.eta_size
  | DCC Id(_α)      => 1
  | DCC Fst(_α, _β) => 1
  | DCC Fstc(_α)    => 1
  | DCC Snd'(_α,_β) => 1
  | DCC Snd(_α, _β) => 1
  | DCC Sndc(_α)    => 1
  | DCC Π(_α, β) => β.eta_size + 1
  | DCC (f ∘' g) => f.eta_size + f.eta_size + g.eta_size + 1
  | DCC (f ∘ g)  => f.eta_size + f.eta_size + g.eta_size + 1
  | DCC ⟨a, b⟩   => a.eta_size + b.eta_size + 1
  | DCC Λ(_α, _β, x) => x.eta_size + 2
  | DCC (Eql(_f_α) _env _x) => 2
  | DCC (Π(f_α, f_β) _env) =>(DCC Π(f_α, f_β)).eta_size + _env.eta_size + 2
  | DCC (Σ(f_α, f_β) _env) =>(DCC Σ(f_α, f_β)).eta_size + _env.eta_size + 2
  | DCC (=(_f_α) _env _x _y) => 0
  | DCC (f x) => f.eta_size + x.eta_size

end Expr
