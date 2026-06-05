import Dcc.Nbe.Value
import Dcc.Nbe.Size
import Dcc.Nbe.ApplyEval
import Dcc.Metatheory.Value

mutual

def Expr.evaluate (env : List Semantic.Val) (e : Expr) : Option ((e' : Semantic.Val) × Semantic.Eval env e e') :=
  match e with
  | (DCC ⊤) => .some ⟨_, .top⟩
  | (DCC ∗) => .some ⟨_, .tintro⟩
  | (DCC ⊥) => .some ⟨_, .bot⟩
  | (DCC Sort _m) => .some ⟨_, .sort⟩
  | (DCC !<f>) =>
    match f.evaluate env with
    | .some ⟨_, h⟩ => .some ⟨_, .map h⟩
    | _ => .none
  | (DCC $<f>) =>
    match f.evaluate env with
    | .some ⟨_, h⟩ => .some ⟨_, .fmap h⟩
    | _ => .none
  | (DCC *(x)) =>
    match x.evaluate env with
    | .some ⟨_, h⟩ => .some ⟨_, .unbox h⟩
    | _ => .none
  | (DCC Eval(α, β, x)) =>
    match α.evaluate env, β.evaluate env, x.evaluate env with
    | .some ⟨_, h_α⟩, .some ⟨_, h_β⟩, .some ⟨_, h_x⟩ => .some ⟨_, .eval h_α h_β h_x⟩
    | _, _, _ => .none
  | (DCC `(β, x)) =>
    match β.evaluate env, x.evaluate env with
    | .some ⟨_, h_β⟩, .some ⟨_, h_x⟩ => .some ⟨_, .quot h_β h_x⟩
    | _, _ => .none
  | (DCC Id(α)) =>
    match α.evaluate env with
    | .some ⟨_, h_α⟩ => .some ⟨_, .id h_α⟩
    | _ => .none
  | (DCC Fstc(β)) =>
    match β.evaluate env with
    | .some ⟨_, h_β⟩ => .some ⟨_, .fstc h_β⟩
    | _ => .none
  | (DCC Sndc(β)) =>
    match β.evaluate env with
    | .some ⟨_, h_β⟩ => .some ⟨_, .sndc h_β⟩
    | _ => .none
  | (DCC Λ(α, β, x)) =>
    match α.evaluate env, β.evaluate env, x.evaluate env with
    | .some ⟨_, h_α⟩, .some ⟨_, h_β⟩, .some ⟨_, h_x⟩ => .some ⟨_, .curr h_α h_β h_x⟩
    | _, _, _ => .none
  | (DCC !Λ(α, β, x)) =>
    match α.evaluate env, β.evaluate env, x.evaluate env with
    | .some ⟨_, h_α⟩, .some ⟨_, h_β⟩, .some ⟨_, h_x⟩ => .some ⟨_, .curr' h_α h_β h_x⟩
    | _, _, _ => .none
  | (DCC Π(f_α, f_β)) =>
    match f_α.evaluate env, f_β.evaluate env with
    | .some ⟨_, h_α⟩, .some ⟨_, h_β⟩ => .some ⟨_, .pi h_α h_β⟩
    | _, _ => .none
  | (DCC ⟦β⟧⟨M, N⟩) =>
    match β.evaluate env, M.evaluate env, N.evaluate env with
    | .some ⟨_, h_β⟩, .some ⟨_, h_M⟩, .some ⟨_, h_N⟩ => .some ⟨_, .pair h_β h_M h_N⟩
    | _, _, _ => .none
  | (DCC Σ(α, β)) =>
    match α.evaluate env, β.evaluate env with
    | .some ⟨_, h_α⟩, .some ⟨_, h_β⟩ => .some ⟨_, .sigma h_α h_β⟩
    | _, _ => .none
  | (DCC Eql(f_α)) =>
    match f_α.evaluate env with
    | .some ⟨_, h_α⟩ => .some ⟨_, .eql h_α⟩
    | _ => .none
  | (DCC refl(f_α)) =>
    match f_α.evaluate env with
    | .some ⟨_, h_α⟩ => .some ⟨_, .refl h_α⟩
    | _ => .none
  | (DCC f ∘ g) =>
    match f.evaluate env, g.evaluate env with
    | .some ⟨_, h_f⟩, .some ⟨_, h_g⟩ => .some ⟨_, .comp h_f h_g⟩
    | _, _ => .none
  | (DCC f ∘' g) =>
    match f.evaluate env, g.evaluate env with
    | .some ⟨_, h_f⟩, .some ⟨_, h_g⟩ => .some ⟨_, .comp' h_f h_g⟩
    | _, _ => .none
  | (DCC f ∘∘ g) =>
    match f.evaluate env, g.evaluate env with
    | .some ⟨_, h_f⟩, .some ⟨_, h_g⟩ => .some ⟨_, .comp₂ h_f h_g⟩
    | _, _ => .none
  | (DCC &(x)) =>
    match x.evaluate env with
    | .some ⟨_, h_x⟩ => .some ⟨_, .boxed h_x⟩
    | _ => .none
  | (DCC !(x)) =>
    match x.evaluate env with
    | .some ⟨_, h_x⟩ => .some ⟨_, .bang h_x⟩
    | _ => .none
  | (DCC ⟦β⟧(x, y)) =>
    match β.evaluate env, x.evaluate env, y.evaluate env with
    | .some ⟨_, h_β⟩, .some ⟨_, h_x⟩, .some ⟨_, h_y⟩ => .some ⟨_, .coup h_β h_x h_y⟩
    | _, _, _ => .none
  | (DCC Coup(β)) =>
    match β.evaluate env with
    | .some ⟨_, h_β⟩ => .some ⟨_, .t_coup h_β⟩
    | _ => .none
  | (DCC (x = y)) =>
    match x.evaluate env, y.evaluate env with
    | .some ⟨_, h_x⟩, .some ⟨_, h_y⟩ => .some ⟨_, .eq h_x h_y⟩
    | _, _ => .none
  | (DCC (f x)) =>
    match f.evaluate env, x.evaluate env with
    | .some ⟨f', h₁⟩, .some ⟨x', h₂⟩ =>
      match f'.apply x' with
      | .some ⟨_, h₃⟩ => .some ⟨_, .app h₁ h₂ h₃⟩
      | _ => .none
    | _, _ => .none

def Semantic.Val.apply (f x : Semantic.Val) : Option ((e' : Semantic.Val) × Semantic.Apply f x e') :=
  match f, x with
  | Val(λ xs 2 => Eql(f_α)), Val(neutral(&(env))) => .some ⟨_, .eql₁⟩
  | Val(λ env 1 => Eql(f_α)), Val(neutral(&(x))) => .some ⟨_, .eql₂⟩
  | Val(λ env 1 => *(α)), Val(neutral(&(x))) => .some ⟨_, .unbox⟩
  | Val(λ env 1 => Id(α)), x => .some ⟨_, .id⟩
  | Val(λ env 1 => Fstc(_α)), Val(neutral(⟦β⟧(a, b))) => .some ⟨_, .fstc⟩
  | Val(λ env 1 => Sndc(_α)), Val(neutral(⟦β⟧(a, b))) => .some ⟨_, .sndc⟩
  | Val(λ env 2 => Λ(α, β, x)), Val(neutral(&(y))) => .some ⟨_, .curr₁⟩
  | Val(λ env 2 => !Λ(α, β, x)), Val(neutral(&(y))) => .some ⟨_, .curr'₁⟩
  | Val(λ env 1 => !<f>), Val(neutral(&(x))) =>
    have h_dec : f.measure + x.measure < Val(λ env 1 => !<f>).measure + Val(neutral(&(x))).measure := by
      grind
    match f.apply x with
    | .some ⟨_, h⟩ => .some ⟨_, .map h⟩
    | _ => .none
  | Val(λ env 1 => $<f>), Val(neutral(&(x))) =>
    have h_dec : f.measure + x.measure < Val(λ env 1 => $<f>).measure + Val(neutral(&(x))).measure := by
      grind
    match f.apply x with
    | .some ⟨_, h⟩ => .some ⟨_, .fmap h⟩
    | _ => .none
  | Val(λ env 1 => ⟦β⟧⟨M, N⟩), Val(neutral(&(x))) =>
    have h_dec₁ : M.measure + x.measure < Val(λ env 1 => ⟦β⟧⟨M, N⟩).measure + Val(neutral(&(x))).measure := by
      grind
    have h_dec₂ : N.measure + x.measure < Val(λ env 1 => ⟦β⟧⟨M, N⟩).measure + Val(neutral(&(x))).measure := by
      grind
    match M.apply x, N.apply x with
    | .some ⟨A, h₁⟩, .some ⟨B, h₂⟩ =>
      have h_dec₁ := h₁.decreasing
      have h_dec₂ := h₂.decreasing
      have h_dec₃ : B.measure + A.measure < Val(λ env 1 => ⟦β⟧⟨M, N⟩).measure + Val(neutral(&(x))).measure := by
        grind
      match B.apply A with
      | .some ⟨_, h₃⟩ =>
        .some ⟨_, .pair h₁ h₂ h₃⟩
      | _ => .none
    | _, _ => .none
  | Val(λ env 1 => Eval(_α, _β, x)), Val(neutral(⟦__β⟧(y, z))) =>
    have h_dec : x.measure + y.measure < Val(λ env 1 => Eval(_α, _β, x)).measure + Val(neutral(⟦__β⟧(y, z))).measure := by
      grind
    match x.apply y with
    | .some ⟨f', h₁⟩ =>
      have h_dec₁ := h₁.decreasing
      have h_dec₂ : f'.measure + z.measure < Val(λ env 1 => Eval(_α, _β, x)).measure + Val(neutral(⟦__β⟧(y, z))).measure := by
        grind
      match f'.apply z with
      | .some ⟨_, h₂⟩ =>
        .some ⟨_, .eval h₁ h₂⟩
      | _ => .none
    | _ => .none
  | Val(λ env 1 => `(β, x)), _y =>
    .some ⟨_, .quot⟩
  | Val(λ env 1 => f ∘' g), x =>
    have h_dec : g.measure + x.measure < Val(λ env 1 => f ∘' g).measure + x.measure := by
      grind
    match g.apply x with
    | .some ⟨A, h₁⟩ =>
      have h_dec := h₁.decreasing
      have h_dec₂ : f.measure + A.measure < Val(λ env 1 => f ∘' g).measure + x.measure := by
        grind
      match f.apply A with
      | .some ⟨_, h₂⟩ => .some ⟨_, .comp' h₁ h₂⟩
      | _ => .none
    | _ => .none
  | Val(λ env 1 => f ∘ g), x =>
    have h_dec : g.measure + x.measure < Val(λ env 1 => f ∘ g).measure + x.measure := by
      grind
    match g.apply x with
    | .some ⟨A, h₁⟩ =>
      have h_dec := h₁.decreasing
      have h_dec₂ : f.measure + A.measure < Val(λ env 1 => f ∘ g).measure + x.measure := by
        grind
      match f.apply A with
      | .some ⟨_, h₂⟩ => .some ⟨_, .comp h₁ h₂⟩
      | _ => .none
    | _ => .none
  | Val(λ env 1 => f ∘∘ g), x =>
    have h_dec : g.measure + x.measure < Val(λ env 1 => f ∘∘ g).measure + x.measure := by
      grind
    match g.apply x with
    | .some ⟨A, h₁⟩ =>
      have h_dec := h₁.decreasing
      have h_dec₂ : f.measure + A.measure < Val(λ env 1 => f ∘∘ g).measure + x.measure := by
        grind
      match f.apply A with
      | .some ⟨_, h₂⟩ => .some ⟨_, .comp₂ h₁ h₂⟩
      | _ => .none
    | _ => .none
  | Val(λ y::env 1 => Λ(α, β, x)), z =>
    have h_dec : x.measure + Val(neutral(⟦β⟧(y, z))).measure < Val(λ y::env 1 => Λ(α, β, x)).measure + z.measure := by
      grind
    match x.apply Val(neutral(⟦β⟧(y, z))) with
    | .some ⟨_, h⟩ => .some ⟨_, .curr₂ h⟩
    | _ => .none
  | Val(λ neutral(&(y))::env 1 => !Λ(α, β, x)), Val(neutral(&(z))) =>
    have h_dec : x.measure + Val(neutral(&(neutral(⟦β⟧(y, z))))).measure < Val(λ neutral(&(y))::env 1 => !Λ(α, β, x)).measure + Val(neutral(&(z))).measure := by
      grind
    match x.apply Val(neutral(&(neutral(⟦β⟧(y, z))))) with
    | .some ⟨_, h⟩ => .some ⟨_, .curr'₂ h⟩
    | _ => .none
  | _, _ => .none
termination_by f.measure + x.measure

end

namespace Semantic

mutual

inductive Neutral.Quote : (level : ℕ) → (v : Neutral) → (e : Expr) → Type
  | tintro : Neutral.Quote level Neutral(∗) (DCC ∗)
  | top    : Neutral.Quote level Neutral(⊤) (DCC ⊤)
  | bot    : Neutral.Quote level Neutral(⊥) (DCC ⊥)
  | eq     : Val.Quote level x x' → Val.Quote level y y'
    → Neutral.Quote level Neutral(x = y) (DCC (x' = y'))
  | eql    : Val.Quote level α α' → Neutral.Quote level Neutral(Eql(α)) (DCC Eql(α'))
  | refl   : Val.Quote level α α' → Neutral.Quote level Neutral(refl(α)) (DCC refl(α'))
  | sort   : Neutral.Quote level Neutral(Sort m) (DCC Sort m)
  | sigma  : Val.Quote level x x' → Val.Quote level y y'
    → Neutral.Quote level Neutral(Σ(x, y)) (DCC (Σ(x', y')))
  | quot   : Val.Quote level β β' → Val.Quote level x x'
    → Neutral.Quote level Neutral(`(β, x)) (DCC `(β', x'))
  | coup   : Val.Quote level β β' → Val.Quote level x x'
    → Val.Quote level y y' → Neutral.Quote level Neutral(⟦β⟧(x, y)) (DCC ⟦β'⟧(x', y'))
  | id     : Val.Quote level α α' → Neutral.Quote level Neutral(Id(α)) (DCC Id(α'))
  | fstc   : Val.Quote level α α' → Neutral.Quote level Neutral(Fstc(α)) (DCC Fstc(α'))
  | sndc   : Val.Quote level α α' → Neutral.Quote level Neutral(Sndc(α)) (DCC Sndc(α'))
  | comp'  : Val.Quote level x x' → Val.Quote level y y'
    → Neutral.Quote level Neutral(x ∘' y) (DCC (x' ∘' y'))
  | comp   : Val.Quote level x x' → Val.Quote level y y'
    → Neutral.Quote level Neutral(x ∘ y) (DCC (x' ∘ y'))
  | comp₂  : Val.Quote level x x' → Val.Quote level y y'
    → Neutral.Quote level Neutral(x ∘∘ y) (DCC (x' ∘∘ y'))
  | pair   : Val.Quote level β β' → Val.Quote level x x'
    → Val.Quote level y y' → Neutral.Quote level Neutral(⟦β⟧⟨x, y⟩) (DCC ⟦β'⟧⟨x', y'⟩)
  | curr   : Val.Quote level α α' → Val.Quote level β β'
    → Val.Quote level x x' → Neutral.Quote level Neutral(Λ(α, β, x)) (DCC Λ(α', β', x'))
  | curr'  : Val.Quote level α α' → Val.Quote level β β'
    → Val.Quote level x x' → Neutral.Quote level Neutral(!Λ(α, β, x)) (DCC !Λ(α', β', x'))
  | eval   : Val.Quote level α α' → Val.Quote level β β'
    → Val.Quote level x x' → Neutral.Quote level Neutral(Eval(α, β, x)) (DCC Eval(α', β', x'))
  | bang   : Val.Quote level x x' → Neutral.Quote level Neutral(!(x)) (DCC !(x'))
  | unbox  : Val.Quote level x x' → Neutral.Quote level Neutral(*(x)) (DCC *(x'))
  | boxed  : Val.Quote level x x' → Neutral.Quote level Neutral(&(x)) (DCC &(x'))
  | map    : Val.Quote level x x' → Neutral.Quote level Neutral(!<x>) (DCC !<x'>)
  | fmap   : Val.Quote level x x' → Neutral.Quote level Neutral($<x>) (DCC $<x'>)
  | app    : Neutral.Quote level f f' → Val.Quote level x x' → Neutral.Quote level
    Neutral(f x) (DCC (f' x'))

inductive Val.Quote : (level : ℕ) → (v : Val) → (e : Expr) → Type
  | neut : Neutral.Quote level nv e → Val.Quote level Val(neutral(nv)) e
  | lam₁ : Apply f Val(neutral(var(level))) Val(neutral(f' neutral(var(level))))
    → Val.Quote level Val(neutral(f')) e'
    → Val.Quote level f e'
  | pi₁  : Apply f_α Val(neutral(var(level))) Val(neutral(f_α' neutral(var(level))))
    → Apply f_β Val(neutral(var(level))) Val(neutral(f_β' neutral(var(level))))
    → Val.Quote level Val(neutral(f_α')) f_α''
    → Val.Quote level.succ Val(neutral(f_β')) f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 2, f_β) (DCC (Π(f_α'', f_β'')))
  | pi₂  : Apply Val(Π (f_α) ⟦⟧ 2, f_β) env Val(Π (f_α') ⟦env'⟧ 1, f_β')
    → 
  --Apply Val(Π (f_α) ⟦⟧ 2, f_β) Val(neutral(var(level)))

end

mutual

def Neutral.quote (level : ℕ) (v : Neutral) : Option Expr :=
  match v with
  | Neutral(var(_v)) => .none
  | Neutral(∗) => .some (DCC ∗)
  | Neutral(⊤) => .some (DCC ⊤)
  | Neutral(⊥) => .some (DCC ⊥)
  | Neutral(x = y) =>
    match x.quote level, y.quote level with
    | .some 
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

def Val.quote (level : ℕ) (v : Val) : Expr :=
  match v with
  | 

end

end Semantic
