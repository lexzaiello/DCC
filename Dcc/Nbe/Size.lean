import Dcc.Nbe.Value
import Dcc.Nbe.ApplyEval

namespace Expr

@[grind ., grind! ., dcc_size]
theorem head_arity_le_size : Expr.head_arity x ≤ Expr.size x := by
  induction x <;> grind

end Expr

namespace Semantic

mutual

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def Neutral.size (nv : Neutral) : ℕ :=
  match nv with
  | Neutral(var(_v)) => 1
  | Neutral(∗) => 1
  | Neutral(⊤) => 2
  | Neutral(⊥) => 2
  | Neutral(x = y) => x.size + y.size
  | Neutral(Eql(α))  => α.size + 3
  | Neutral(refl(α)) => α.size + 3
  | Neutral(Sort _m) => 1
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
  | Val(λ _env _n => bdy) => bdy.size + 1
  | Val(Π (f_α) _env _n, f_β) => f_α.size + f_β.size + 1

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def Val.measure (v : Val) : ℕ :=
  match v with
  | Val(neutral(x)) => x.size
  | Val(λ env n => bdy) =>
    match env with
    | x :: _xs =>
      bdy.size + x.measure + 1
    | _ => bdy.size + n + 1
  | Val(Π (f_α) _env n, f_β) => f_α.size + f_β.size + n + 1

end

mutual

@[grind ., grind! .]
theorem Val.measure_pos : 0 < Val.measure x := by
  cases x
  any_goals (grind)
  case lam =>
    unfold Val.measure
    split
    · grind
    · grind
  case neut nv =>
    dsimp [Val.measure]
    exact Neutral.size_pos

@[grind ., grind! .]
theorem Neutral.size_pos : 0 < Neutral.size x := by
  cases x
  any_goals (grind)
  case app f v =>
    have h := f.size_pos
    grind
  case t_coup x | eq x y =>
    have h := x.size_pos
    grind
  case coup x | bang x =>
    have h := x.measure_pos
    grind

@[grind ., grind! .]
theorem Val.size_pos : 0 < Val.size x := by
  cases x
  any_goals (grind)
  case neut n =>
    have h := n.size_pos
    grind

end

@[grind ., grind! ., dcc_size]
theorem Val.size_le_measure : Val.size x ≤ Val.measure x := by
  cases x
  any_goals (grind)
  case lam env arity bdy =>
    unfold Val.measure
    split
    case h_1 env x xs =>
      grind
    case h_2 env ih =>
      grind

@[dcc_size]
theorem Apply.decreasing (h : Apply f x e') : e'.measure < f.measure + x.measure := by
  induction h
  any_goals (grind)
  any_goals (
    focus
    dcc_simp
    unfold Val.measure
    split
    · grind
    · grind
    done)
  any_goals (
    dcc_simp
    conv =>
      right
      unfold Val.measure
      rfl
    split <;> grind)

end Semantic
