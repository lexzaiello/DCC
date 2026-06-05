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
  | NeutralTm(var(_v) x)       => x.measure.succ.succ
  | NeutralTm(f neutral(var(_v))) => f.size.succ.succ
  | NeutralTm(f x)             => f.size + x.measure
  | NeutralTm(∗) => 1
  | NeutralTm(⊤) => 2
  | NeutralTm(⊥) => 2
  | NeutralTm(x = y) => x.measure + y.measure + 1
  | NeutralTm(Eql(α))  => α.measure + 3
  | NeutralTm(refl(α)) => α.measure + 3
  | NeutralTm(Sort _m) => 1
  | NeutralTm(Σ(α, β)) => α.measure + β.measure + 2
  | NeutralTm(`(β, x)) => β.measure + x.measure + 2
  | NeutralTm(⟦β⟧(x, y)) => β.measure + x.measure + y.measure + 1
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
  | Neutral(var(_v)) => 0
  | Neutral(tm(tm)) => tm.size.succ

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
    bdy.size + 1 + n + match env with
    | x :: _xs =>
      x.measure
    | _ => 0
  | Val(Π (f_α) env n, f_β) => f_α.measure + f_β.measure + n + 1 + match env with
    | x :: _xs =>
      x.measure
    | _ => 0

end

end Semantic
