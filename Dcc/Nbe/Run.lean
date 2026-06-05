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
  | Val(Π (f_α) env 2, f_β), x => .some ⟨_, .pi⟩
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
  | t_coup : Val.Quote level β β' → Neutral.Quote level Neutral(Coup(β)) (DCC Coup(β'))
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
  | app    : Neutral.Quote level f f' → Val.Quote level x x' → Neutral.Quote level Neutral(f x) (DCC (f' x'))

/-
Val(neutral(f' neutral(var(level))))
-/

inductive Val.Quote : (level : ℕ) → (v : Val) → (e : Expr) → Type
  | neut : Neutral.Quote level nv e → Val.Quote level Val(neutral(nv)) e
  | lam₁ : Apply Val(λ env n => bdy) Val(neutral(var(level))) Val(neutral(f' neutral(var(level))))
    → Neutral.Quote level.succ f' e'
    → Val.Quote level Val(λ env n => bdy) e'
  | lam₂ : Apply Val(λ env n => bdy) Val(neutral(var(level))) Val(λ env' n' => bdy')
    → Val.Quote level.succ Val(λ env' n' => bdy') e'
    → Val.Quote level Val(λ env n => bdy) e'
  | pi₁  : Apply f_α Val(neutral(var(level))) Val(neutral(f_α' neutral(var(level))))
    → Apply f_β Val(neutral(var(level))) Val(neutral(f_β' neutral(var(level))))
    → Neutral.Quote level.succ f_α' f_α''
    → Neutral.Quote level.succ.succ f_β' f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 2, f_β) (DCC (Π(f_α'', f_β'')))
  | pi₂  : Apply f_α Val(neutral(var(level))) Val(λ env' n' => bdy')
    → Apply f_β Val(neutral(var(level))) Val(neutral(f_β' neutral(var(level))))
    → Val.Quote level.succ Val(λ env' n' => bdy') f_α''
    → Neutral.Quote level.succ.succ f_β' f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 2, f_β) (DCC (Π(f_α'', f_β'')))
  | pi₃  : Apply f_α Val(neutral(var(level))) Val(neutral(f_α' neutral(var(level))))
    → Apply f_β Val(neutral(var(level))) Val(λ env' n' => bdy')
    → Neutral.Quote level.succ f_α' f_α''
    → Val.Quote level.succ.succ Val(λ env' n' => bdy') f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 2, f_β) (DCC (Π(f_α'', f_β'')))
  | pi₄ : Apply f_α Val(neutral(var(level))) Val(λ env'₁ n'₁ => bdy'₁)
    → Apply f_β Val(neutral(var(level))) Val(λ env'₂ n'₂ => bdy'₂)
    → Val.Quote level.succ Val(λ env'₁ n'₁ => bdy'₁) f_α''
    → Val.Quote level.succ.succ Val(λ env'₂ n'₂ => bdy'₂) f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 2, f_β) (DCC (Π(f_α'', f_β'')))

end

mutual

def Neutral.quote (level : ℕ) (v : Neutral) : Option ((e : Expr) × v.Quote level e) :=
  match v with
  | Neutral(var(_v)) => .none
  | Neutral(∗) => .some ⟨_, .tintro⟩
  | Neutral(⊤) => .some ⟨_, .top⟩
  | Neutral(⊥) => .some ⟨_, .bot⟩
  | Neutral(x = y) =>
    have h_dec₁ : x.measure < Neutral(x = y).size := by
      grind
    have h_dec₂ : y.measure < Neutral(x = y).size := by
      grind
    match x.quote level, y.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .eq h₁ h₂⟩
    | _, _ => .none
  | Neutral(Eql(α))  =>
    have h_dec₁ : α.measure < Neutral(Eql(α)).size := by
      grind
    match α.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .eql h⟩
    | _ => .none
  | Neutral(refl(α))  =>
    have h_dec₁ : α.measure < Neutral(refl(α)).size := by
      grind
    match α.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .refl h⟩
    | _ => .none
  | Neutral(Sort _m) => .some ⟨_, .sort⟩
  | Neutral(Σ(α, β)) =>
    have h_dec₁ : α.measure < Neutral(Σ(α, β)).size := by
      grind
    have h_dec₂ : β.measure < Neutral(Σ(α, β)).size := by
      grind
    match α.quote level, β.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .sigma h₁ h₂⟩
    | _, _ => .none
  | Neutral(`(β, x)) =>
    have h_dec₁ : β.measure < Neutral(`(β, x)).size := by
      grind
    have h_dec₂ : x.measure < Neutral(`(β, x)).size := by
      grind
    match β.quote level, x.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .quot h₁ h₂⟩
    | _, _ => .none
  | Neutral(⟦β⟧(x, y)) =>
    have h_dec₁ : β.measure < Neutral(⟦β⟧(x, y)).size := by
      grind
    have h_dec₂ : x.measure < Neutral(⟦β⟧(x, y)).size := by
      grind
    have h_dec₃ : y.measure < Neutral(⟦β⟧(x, y)).size := by
      grind
    match β.quote level, x.quote level, y.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ =>
      .some ⟨_, .coup h₁ h₂ h₃⟩
    | _, _, _ => .none
  | Neutral(Coup(β)) =>
    have h_dec₁ : β.measure < Neutral(Coup(β)).size := by
      grind
    match β.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .t_coup h⟩
    | _ => .none
  | Neutral(Id(α))      =>
    have h_dec₁ : α.measure < Neutral(Id(α)).size := by
      grind
    match α.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .id h⟩
    | _ => .none
  | Neutral(Fstc(α))    =>
    have h_dec₁ : α.measure < Neutral(Fstc(α)).size := by
      grind
    match α.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .fstc h⟩
    | _ => .none
  | Neutral(Sndc(α))    =>
    have h_dec₁ : α.measure < Neutral(Sndc(α)).size := by
      grind
    match α.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .sndc h⟩
    | _ => .none
  | Neutral(f ∘' g) =>
    have h_dec₁ : f.measure < Neutral(f ∘' g).size := by
      grind
    have h_dec₂ : g.measure < Neutral(f ∘' g).size := by
      grind
    match f.quote level, g.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .comp' h₁ h₂⟩
    | _, _ => .none
  | Neutral(f ∘ g) =>
    have h_dec₁ : f.measure < Neutral(f ∘ g).size := by
      grind
    have h_dec₂ : g.measure < Neutral(f ∘ g).size := by
      grind
    match f.quote level, g.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .comp h₁ h₂⟩
    | _, _ => .none
  | Neutral(f ∘∘ g) =>
    have h_dec₁ : f.measure < Neutral(f ∘∘ g).size := by
      grind
    have h_dec₂ : g.measure < Neutral(f ∘∘ g).size := by
      grind
    match f.quote level, g.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .comp₂ h₁ h₂⟩
    | _, _ => .none
  | Neutral(⟦β⟧⟨x, y⟩) =>
    have h_dec₁ : β.measure < Neutral(⟦β⟧⟨x, y⟩).size := by
      grind
    have h_dec₂ : x.measure < Neutral(⟦β⟧⟨x, y⟩).size := by
      grind
    have h_dec₃ : y.measure < Neutral(⟦β⟧⟨x, y⟩).size := by
      grind
    match β.quote level, x.quote level, y.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ =>
      .some ⟨_, .pair h₁ h₂ h₃⟩
    | _, _, _ => .none
  | Neutral(Λ(α, β, x)) =>
    have h_dec₁ : α.measure < Neutral(Λ(α, β, x)).size := by
      grind
    have h_dec₂ : β.measure < Neutral(Λ(α, β, x)).size := by
      grind
    have h_dec₃ : x.measure < Neutral(Λ(α, β, x)).size := by
      grind
    match α.quote level, β.quote level, x.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ =>
      .some ⟨_, .curr h₁ h₂ h₃⟩
    | _, _, _ => .none
  | Neutral(!Λ(α, β, x)) =>
    have h_dec₁ : α.measure < Neutral(!Λ(α, β, x)).size := by
      grind
    have h_dec₂ : β.measure < Neutral(!Λ(α, β, x)).size := by
      grind
    have h_dec₃ : x.measure < Neutral(!Λ(α, β, x)).size := by
      grind
    match α.quote level, β.quote level, x.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ =>
      .some ⟨_, .curr' h₁ h₂ h₃⟩
    | _, _, _ => .none
  | Neutral(Eval(α, β, x)) =>
    have h_dec₁ : α.measure < Neutral(Eval(α, β, x)).size := by
      grind
    have h_dec₂ : β.measure < Neutral(Eval(α, β, x)).size := by
      grind
    have h_dec₃ : x.measure < Neutral(Eval(α, β, x)).size := by
      grind
    match α.quote level, β.quote level, x.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ =>
      .some ⟨_, .eval h₁ h₂ h₃⟩
    | _, _, _ => .none
  | Neutral(!(x))            =>
    have h_dec₁ : x.measure < Neutral(!(x)).size := by
      grind
    match x.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .bang h⟩
    | _ => .none
  | Neutral(*(α))            =>
    have h_dec₁ : α.measure < Neutral(*(α)).size := by
      grind
    match α.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .unbox h⟩
    | _ => .none
  | Neutral(&(x))            =>
    have h_dec₁ : x.measure < Neutral(&(x)).size := by
      grind
    match x.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .boxed h⟩
    | _ => .none
  | Neutral(!<x>)            =>
    have h_dec₁ : x.measure < Neutral(!<x>).size := by
      grind
    match x.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .map h⟩
    | _ => .none
  | Neutral($<x>)            =>
    have h_dec₁ : x.measure < Neutral($<x>).size := by
      grind
    match x.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .fmap h⟩
    | _ => .none
  | Neutral(f x)             =>
    have h_dec₁ : f.size < Neutral(f x).size := by
      grind
    have h_dec₂ : x.measure < Neutral(f x).size := by
      grind
    match f.quote level, x.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .app h₁ h₂⟩
    | _, _ => .none
termination_by v.size

def Val.quote (level : ℕ) (v : Val) : Option ((e : Expr) × v.Quote level e) :=
  match v with
  | Val(neutral(neut)) =>
    have h_dec : neut.size < Val(neutral(neut)).measure := by
      grind
    match neut.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .neut h⟩
    | _ => .none
  | Val(λ env n => bdy) =>
    match Val(λ env n => bdy).apply Val(neutral(var(level))) with
    | .some ⟨Val(neutral(f' neutral(var(level₂)))), h₁⟩ =>
      if heq : level₂ = level then
        match f'.quote level.succ with
        | .some ⟨_, h₂⟩ =>
          heq ▸ .some ⟨_, .lam₁ (heq.symm ▸ h₁) (heq ▸ h₂)⟩
        | _ => .none
      else .none
    | .some ⟨Val(λ env' n' => bdy'), h₁⟩ =>
      match Val(λ env' n' => bdy').quote level.succ with
      | .some ⟨_, h₂⟩ =>
        .some ⟨_, .lam₂ h₁ h₂⟩
      | _ => .none
    | _ => .none
  | Val(Π (f_α) ⟦⟧ 2, f_β) =>
    match f_α.apply Val(neutral(var(level))), f_β.apply Val(neutral(var(level))) with
    | .some ⟨Val(neutral(f_α' neutral(var(level₂)))), h₁⟩,
      .some ⟨Val(neutral(f_β' neutral(var(level₃)))), h₂⟩ =>
      if heq₁ : level₂ = level then
        if heq₂ : level₃ = level then
          match f_α'.quote level.succ, f_β'.quote level.succ.succ with
          | .some ⟨_, h₃⟩, .some ⟨_, h₄⟩ => by
            cases heq₁; cases heq₂
            exact .some ⟨_, .pi₁ h₁ h₂ h₃ h₄⟩
          | _, _ => .none
        else .none
      else .none
    | .some ⟨Val(λ env' n' => bdy'), h₁⟩,
      .some ⟨Val(neutral(f_β' neutral(var(level₂)))), h₂⟩ =>
      if heq₁ : level₂ = level then
        match Val(λ env' n' => bdy').quote level.succ, f_β'.quote level.succ.succ with
        | .some ⟨_, h₃⟩, .some ⟨_, h₄⟩ => by
          cases heq₁
          exact .some ⟨_, .pi₂ h₁ h₂ h₃ h₄⟩
        | _, _ => .none
      else .none
    | .some ⟨Val(neutral(f_α' neutral(var(level₂)))), h₁⟩,
      .some ⟨Val(λ env' n' => bdy'), h₂⟩ =>
      if heq₁ : level₂ = level then
        match Val(λ env' n' => bdy').quote level.succ.succ, f_α'.quote level.succ with
        | .some ⟨_, h₄⟩, .some ⟨_, h₃⟩ => by
          cases heq₁
          exact .some ⟨_, .pi₃ h₁ h₂ h₃ h₄⟩
        | _, _ => .none
      else .none
    | .some ⟨Val(λ env'₁ n'₁ => bdy'₁), h₁⟩,
      .some ⟨Val(λ env'₂ n'₂ => bdy'₂), h₂⟩ =>
      match Val(λ env'₁ n'₁ => bdy'₁).quote level.succ, Val(λ env'₂ n'₂ => bdy'₂).quote level.succ.succ with
      | .some ⟨_, h₃⟩, .some ⟨_, h₄⟩ => .some ⟨_, .pi₄ h₁ h₂ h₃ h₄⟩
      | _, _ => .none
    | _, _ => .none
  | _ => .none
termination_by v.measure

end

end Semantic

/-
Pattern mtaching in some constructors might be able to use quote / the bullet technique to do a form of extensionality.

For example, β : α → Sort n.
Currently, we just check
Reduces (f_β env) `(α, ...).

We can instead check similarly to in the Π case.

Or probably just doing reduce_nbe would get us there. tbh.
-/
