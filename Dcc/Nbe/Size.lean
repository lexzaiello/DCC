import Dcc.Nbe.Value
import Dcc.Nbe.ApplyEval

namespace Expr

@[grind ., grind! .]
theorem head_arity_le_size : Expr.head_arity x ≤ Expr.size x := by
  induction x <;> grind

end Expr

namespace Semantic

mutual

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def Neutral.size (nv : Neutral) : ℕ :=
  match nv with
  | Neutral(var(_v)) => 0
  | Neutral(∗) => 0
  | Neutral(⊤) => 2
  | Neutral(⊥) => 2
  | Neutral(x = y) => x.size + y.size
  | Neutral(Eql(α))  => α.size + 3
  | Neutral(refl(α)) => α.size + 3
  | Neutral(Sort m) => m
  | Neutral(Σ(α, β)) => α.size + β.size + 2
  | Neutral(`(_β, x)) => x.measure + 2
  | Neutral(⟦_β⟧(x, y)) => x.measure + y.measure
  | Neutral(Coup(β)) => β.size
  | Neutral(Id(_α))      => 2
  | Neutral(Fstc(_α))    => 2
  | Neutral(Sndc(_α))    => 2
  | Neutral(f ∘' g) => f.measure + f.measure + g.measure + 2
  | Neutral(f ∘ g)  => f.measure + f.measure + g.measure + 2
  | Neutral(f ∘∘ g)  => f.measure + f.measure + g.measure + 2
  | Neutral(⟦_β⟧⟨a, b⟩)   => a.measure + a.measure + b.measure + 2
  | Neutral(Λ(α, β, x)) => α.size + β.size + x.measure + 2
  | Neutral(!Λ(α, β, x)) => α.size + β.size + x.measure + 2
  | Neutral(Eval(_α, _β, x)) => x.measure + 1
  | Neutral(!(x))            => x.measure
  | Neutral(*(α))            => α.size + 1
  | Neutral(&(x))            => x.measure + x.measure + x.measure + 2
  | Neutral(!<x>)            => x.measure + x.measure + x.measure + 2
  | Neutral($<x>)            => x.measure + x.measure + x.measure + 2
  | Neutral(f x)             => f.size + x.size

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def Val.size (v : Val) : ℕ :=
  match v with
  | Val(neutral(x)) => x.size
  | Val(λ _env _n => bdy) => bdy.size
  | Val(Π (f_α) _env _n, f_β) => f_α.size + f_β.size

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def Val.measure (v : Val) : ℕ :=
  match v with
  | Val(neutral(x)) => x.size
  | Val(λ _env n => bdy) => bdy.size + n
  | Val(Π (f_α) _env n, f_β) => f_α.size + f_β.size + n

end

@[grind ., grind! .]
theorem Val.size_le_measure : Val.size x ≤ Val.measure x := by
  cases x <;> grind

@[dcc_size]
theorem Apply.decreasing (h : Apply f x e') : e'.measure < f.measure + x.measure := by
  induction h
  any_goals (grind)
  case curr₂ =>
    dcc_simp_all
    
    sorry


/-@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def Neutral.head_arity (v : Neutral) : ℕ :=
  match v with
  | Neutral(raw(e)) => e.head_arity
  | Neutral(⊤)
  | Neutral(⊥)
  | Neutral(∗)
  | Neutral(Coup(_β))
  | Neutral(⟦_β⟧(_x, _y))
  | Neutral(!(_x))
  | Neutral(&(_x))
  | Neutral(_x = _y)
  | Neutral(var(_x))
  | Neutral(Sort _m) => 0
  | Neutral(f _x) => f.head_arity - 1-/

/-@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def Val.head_arity (v : Val) : ℕ :=
  match v with
  | Val(λ _env n => _bdy) => n
  | Val(neutral(_x)) => 0-/

/-mutual

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def Neutral.composite_size (nv : Neutral) : ℕ :=
  match nv with
  | Neutral(var(_m)) => 0
  | Neutral(f x) => f.composite_size + x.composite_size
  | Neutral(raw(c)) => c.size
  | Neutral(x = y) => x.composite_size + y.composite_size
  | Neutral(!(x)) => x.composite_size
  | Neutral(&(x)) => x.composite_size + x.composite_size + x.composite_size + 1
  | Neutral(⟦_β⟧(x, y)) => x.composite_size + y.composite_size
  | Neutral(Coup(β)) => β.composite_size
  | Neutral(⊤) => (DCC ⊤).size
  | Neutral(⊥) => (DCC ⊥).size
  | Neutral(∗) => (DCC ∗).size
  | Neutral(Sort m) => (DCC Sort m).size

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def Val.composite_size (v : Val) : ℕ :=
  match v with
  | .neut nv => nv.composite_size
  | Val(λ _env n => bdy) => n + bdy.composite_size

end-/

/-@[grind ., grind! .]
theorem Neutral.head_arity_le_size : Neutral.head_arity x ≤ Neutral.size x := by
  cases x
  any_goals (grind)
  case app f x =>
    have h := f.head_arity_le_size
    dcc_simp
    grind-/

/-@[aesop safe forward (rule_sets := [DccSize])]
theorem ApplySimple.decreasing (h : ApplySimple f x e') : e'.composite_size < f.composite_size + x.composite_size := by
  cases h <;> grind

-- 3 is our maximum arity kinda
@[dcc_size, aesop safe forward (rule_sets := [DccSize])]
theorem EvalSimple.size_eq (h : EvalSimple env x x') : Val.size x' = Expr.size x := by
  cases h <;> grind

@[dcc_size, aesop safe forward (rule_sets := [DccSize])]
theorem EvalSimple.composite_size_eq (h : EvalSimple env x x') : Val.composite_size x' = (Expr.composite_size x) + x.head_arity := by
  cases h
  any_goals (grind)-/



end Semantic
