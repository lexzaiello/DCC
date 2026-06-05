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
def NeutralTm.size (nv : NeutralTm) : ℕ :=
  match nv with
  | NeutralTm(∗) => 1
  | NeutralTm(⊤) => 2
  | NeutralTm(⊥) => 2
  | NeutralTm(x = y) => x.measure + y.measure
  | NeutralTm(Eql(α))  => α.measure + 3
  | NeutralTm(refl(α)) => α.measure + 3
  | NeutralTm(Sort _m) => 1
  | NeutralTm(Σ(α, β)) => α.measure + β.measure + 2
  | NeutralTm(`(β, x)) => β.measure + x.measure + 2
  | NeutralTm(⟦β⟧(x, y)) => β.measure + x.measure + y.measure
  | NeutralTm(Coup(β)) => β.measure + 1
  | NeutralTm(Id(α))      => α.measure + 1
  | NeutralTm(Fstc(α))    => α.measure + 1
  | NeutralTm(Sndc(α))    => α.measure + 1
  | NeutralTm(f ∘' g) => f.measure + f.measure + g.measure + 2
  | NeutralTm(f ∘ g)  => f.measure + f.measure + g.measure + 2
  | NeutralTm(f ∘∘ g)  => f.measure + f.measure + g.measure + 2
  | NeutralTm(⟦β⟧⟨a, b⟩)   => β.measure + a.measure + a.measure + b.measure + 2
  | NeutralTm(Λ(α, β, x)) => α.measure + β.measure + x.measure + 2
  | NeutralTm(!Λ(α, β, x)) => α.measure + β.measure + β.measure + β.measure + x.measure + 2
  | NeutralTm(Eval(α, β, x)) => α.measure + β.measure + x.measure + 1
  | NeutralTm(!(x))            => x.measure + 1
  | NeutralTm(*(α))            => α.measure + 1
  | NeutralTm(&(x))            => x.measure + x.measure + x.measure + 2
  | NeutralTm(!<x>)            => x.measure + x.measure + x.measure + 2
  | NeutralTm($<x>)            => x.measure + x.measure + x.measure + 2
  | NeutralTm(f x)             => f.size + x.measure
  --| NeutralTm(var(v) x)        => Neutral(var(v)).size + x.size

/-
a_ih :
  e'.measure <
    x.measure +
      (β.measure + y.measure + z.measure + (β.measure + y.measure + z.measure) +
          (β.measure + y.measure + z.measure) +
        2)
⊢ e'.measure <
    α.measure + β.measure + x.measure + 2 + (y.measure + y.measure + y.measure + 2) + 1 +
      (z.measure + z.measure + z.measure + 2)

matching:
  - 3 ys cancel out
  - α cancels out
  - β needs two more

total constant sum:
  - before: 2
  - after: 7
α sum:
  - before: 

-/

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def Neutral.size (nv : Neutral) : ℕ :=
  match nv with
  | Neutral(var(_v)) => 1
  | Neutral(tm(tm)) => tm.size

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
  · grind
  case tm trm =>
    exact trm.size_pos

@[grind ., grind! .]
theorem NeutralTm.size_pos : 0 < NeutralTm.size x := by
  cases x
  any_goals (grind)
  case app f v =>
    have h := f.size_pos
    grind
  case eq x y =>
    have h₁ := x.measure_pos
    have h₂ := y.measure_pos
    grind
  case coup x =>
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

#check Apply.decreasing

end Semantic
