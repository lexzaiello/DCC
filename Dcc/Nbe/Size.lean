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
  --| NeutralTm(var((_v) : _τ) x)       => x.measure.succ.succ
  --| NeutralTm(f neutral(var((_v) : _τ))) => f.size.succ.succ
  | NeutralTm(f x)             => f.size + x.measure
  | NeutralTm(∗) => 1
  | NeutralTm(⊤) => 2
  | NeutralTm(⊥) => 2
  | NeutralTm(x = y) => x.measure + y.measure + 1
  | NeutralTm(Eql(α))  => α.measure + 3
  | NeutralTm(refl(α)) => α.measure + 2
  | NeutralTm(Sort _m) => 1
  | NeutralTm(Σ(α, β)) => α.measure + β.measure + 2
  | NeutralTm(`(β, x)) => β.measure + x.measure
  | NeutralTm(⟦β⟧(x, y)) => β.measure + x.measure + y.measure + 1
  | NeutralTm(Coup(β)) => β.measure + 1
  | NeutralTm(Id(α))      => α.measure + 1
  | NeutralTm(Fst(α))    => α.measure + 1
  | NeutralTm(Snd(α))    => α.measure + 1
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
  | Neutral(var((_v) : _τ)) => 0
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
    bdy.size + 2 + n + match env with
    | x :: _xs =>
      x.measure
    | _ => 0
  | Val(Π (f_α) env n, f_β) => f_α.measure + f_β.measure + n + 2 + match env with
    | x :: _xs =>
      x.measure
    | _ => 0

end

mutual

def NeutralTm.contains_var (v : NeutralTm) (var : Val) : Bool :=
  match v with
  | NeutralTm(f x)             => f.contains_var var ∨ x.contains_var var
  | NeutralTm(∗)
  | NeutralTm(⊤)
  | NeutralTm(⊥) => False
  | NeutralTm(x = y) => x.contains_var var ∨ y.contains_var var
  | NeutralTm(Eql(α))  => α.contains_var var
  | NeutralTm(refl(α)) => α.contains_var var
  | NeutralTm(Sort _m) => False
  | NeutralTm(Σ(α, β)) => α.contains_var var ∨ β.contains_var var
  | NeutralTm(`(β, x)) => β.contains_var var ∨ x.contains_var var
  | NeutralTm(⟦β⟧(x, y)) => β.contains_var var ∨ x.contains_var var ∨ y.contains_var var
  | NeutralTm(Coup(β)) => β.contains_var var
  | NeutralTm(Id(α))      => α.contains_var var
  | NeutralTm(Fst(α))    => α.contains_var var
  | NeutralTm(Snd(α))    => α.contains_var var
  | NeutralTm(f ∘' g) => f.contains_var var ∨ g.contains_var var
  | NeutralTm(f ∘ g)  => f.contains_var var ∨ g.contains_var var
  | NeutralTm(f ∘∘ g)  => f.contains_var var ∨ g.contains_var var
  | NeutralTm(⟦β⟧⟨a, b⟩)   => β.contains_var var ∨ a.contains_var var ∨ b.contains_var var
  | NeutralTm(Λ(α, β, x)) => α.contains_var var ∨ β.contains_var var ∨ x.contains_var var
  | NeutralTm(!Λ(α, β, x)) => α.contains_var var ∨ β.contains_var var ∨ x.contains_var var
  | NeutralTm(Eval(α, β, x)) => α.contains_var var ∨ β.contains_var var ∨ x.contains_var var
  | NeutralTm(!(x))            => x.contains_var var
  | NeutralTm(*(α))            => α.contains_var var
  | NeutralTm(&(x))            => x.contains_var var
  | NeutralTm(!<x>)            => x.contains_var var
  | NeutralTm($<x>)            => x.contains_var var

def Neutral.contains_var (v : Neutral) (var : Val) : Bool :=
  match v with
  | Neutral(var((n₂) : _τ')) =>
    match var with
    | Val(neutral(var((n) : _τ))) => n == n₂
    | _ => False
  | Neutral(tm(tm)) => tm.contains_var var

def Val.contains_var (v : Val) (var : Val) : Bool :=
  match v with
  | Val(λ env _n => bdy) => env.any (fun v => match v, var with
    | Val(neutral(var((n₂) : _τ₂))), Val(neutral(var((n) : _τ))) => n == n₂
    | _, _ => False) ∨ bdy.contains_var var
  | Val(Π (f_α) env _n, f_β) => env.any (fun v => match v, var with
    | Val(neutral(var((n₂) : _τ₂))), Val(neutral(var((n) : _τ)))  => n == n₂
    | _, _ => False) ∨ f_α.contains_var v ∨ f_β.contains_var v
  | Val(neutral(neut)) => neut.contains_var v

end

end Semantic
