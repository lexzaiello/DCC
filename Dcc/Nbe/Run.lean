import Dcc.Nbe.Value
import Dcc.Nbe.ApplyEval
import Dcc.Metatheory.Value

mutual

def Expr.TyValue.evaluate (env : List Semantic.Val) (hval : Expr.TyValue e) : ((e' : Semantic.Val) × Semantic.Eval env e e') :=
  match e with
  | (DCC ⊤) => ⟨_, .simple .top⟩
  | (DCC ∗) => ⟨_, .simple .tintro⟩
  | (DCC ⊥) => ⟨_, .simple .bot⟩
  | (DCC Sort _m) => ⟨_, .simple .sort⟩
  | (DCC !<_f>) => ⟨_, .simple .map⟩
  | (DCC $<_f>) => ⟨_, .simple .fmap⟩
  | (DCC *(x)) => ⟨_, .simple .unbox⟩
  | (DCC Eval(α, β, x)) => ⟨_, .simple .eval⟩
  | (DCC `(β, x)) => ⟨_, .simple .quot⟩
  | (DCC Id(α)) => ⟨_, .simple .id⟩
  | (DCC Fstc(β)) => ⟨_, .simple .fstc⟩
  | (DCC Sndc(β)) => ⟨_, .simple .sndc⟩
  | (DCC Λ(α, β, x)) => ⟨_, .simple .curr⟩
  | (DCC !Λ(α, β, x)) => ⟨_, .simple .curr'⟩
  | (DCC Π(f_α, f_β)) => ⟨_, .simple .pi⟩
  | (DCC ⟦β⟧⟨M, N⟩) => ⟨_, .simple .pair⟩
  | (DCC Σ(α, β)) => ⟨_, .simple .sigma⟩
  | (DCC Eql(f_α)) => ⟨_, .simple .eql⟩
  | (DCC refl(f_α)) => ⟨_, .simple .refl⟩
  | (DCC f ∘ g) => ⟨_, .simple .comp⟩
  | (DCC f ∘' g) => ⟨_, .simple .comp'⟩
  | (DCC f ∘∘ g) => ⟨_, .simple .comp₂⟩
  | (DCC &(x)) => ⟨_, .compound (.boxed (x.evaluate env).snd)⟩
  | (DCC !(x)) => ⟨_, .compound (.bang (x.evaluate env).snd)⟩
  | (DCC ⟦β⟧(x, y)) => ⟨_, .compound (.coup (β.evaluate env).snd (x.evaluate env).snd (y.evaluate env).snd)⟩
  | (DCC Coup(β)) => ⟨_, .compound (.t_coup (β.evaluate env).snd)⟩
  | (DCC (x = y)) => ⟨_, .compound (.eq (x.evaluate env).snd (y.evaluate env).snd)⟩
  | (DCC (f x)) =>
    let ⟨f', h₁⟩ := f.evaluate env
    let ⟨x', h₂⟩ := x.evaluate env
    let ⟨e', h₃⟩ := f'.apply x'
    ⟨_, .app h₁ h₂ h₃⟩

def Semantic.Val.apply (f x : Semantic.Val) : ((e' : Semantic.Val) × Semantic.Apply f x e') :=
  match f, x with
  | Val(λ xs 2 => Eql(f_α)), Val(neutral(&(env))) => ⟨_, .simple .eql₁⟩
  | Val(λ env 1 => Eql(f_α)), Val(neutral(&(x))) => ⟨_, .simple .eql₂⟩
  | Val(λ env 1 => *(α)), Val(neutral(&(x))) => ⟨_, .simple .unbox⟩
  | Val(λ env 1 => Id(α)), x => ⟨_, .simple .id⟩
  | Val(λ env 1 => Fstc(_α)), Val(neutral(⟦β⟧(a, b))) => ⟨_, .simple .fstc⟩
  | Val(λ env 1 => Sndc(_α)), Val(neutral(⟦β⟧(a, b))) => ⟨_, .simple .sndc⟩
  | Val(λ env 2 => Λ(α, β, x)), Val(neutral(&(y))) => ⟨_, .simple .curr₁⟩
  | Val(λ env 2 => !Λ(α, β, x)), Val(neutral(&(y))) => ⟨_, .simple .curr'₁⟩
  | Val(λ env 1 => !<f>), Val(neutral(&(x))) =>
    let ⟨f', h₁⟩ :=  f.eval []
    let e' := 

end

mutual

def Expr.evaluate (env : List Semantic.Val) (e : Expr) : ((e' : Semantic.Val) × Semantic.Eval env e e') :=
  match e with
  | (DCC ⊤) => ⟨_, .simple .top⟩
  | (DCC ∗) => ⟨_, .simple .tintro⟩
  | (DCC ⊥) => ⟨_, .simple .bot⟩
  | (DCC Sort _m) => ⟨_, .simple .sort⟩
  | (DCC !<_f>) => ⟨_, .simple .map⟩
  | (DCC $<_f>) => ⟨_, .simple .fmap⟩
  | (DCC *(x)) => ⟨_, .simple .unbox⟩
  | (DCC Eval(α, β, x)) => ⟨_, .simple .eval⟩
  | (DCC `(β, x)) => ⟨_, .simple .quot⟩
  | (DCC Id(α)) => ⟨_, .simple .id⟩
  | (DCC Fstc(β)) => ⟨_, .simple .fstc⟩
  | (DCC Sndc(β)) => ⟨_, .simple .sndc⟩
  | (DCC Λ(α, β, x)) => ⟨_, .simple .curr⟩
  | (DCC !Λ(α, β, x)) => ⟨_, .simple .curr'⟩
  | (DCC Π(f_α, f_β)) => ⟨_, .simple .pi⟩
  | (DCC ⟦β⟧⟨M, N⟩) => ⟨_, .simple .pair⟩
  | (DCC Σ(α, β)) => ⟨_, .simple .sigma⟩
  | (DCC Eql(f_α)) => ⟨_, .simple .eql⟩
  | (DCC refl(f_α)) => ⟨_, .simple .refl⟩
  | (DCC f ∘ g) => ⟨_, .simple .comp⟩
  | (DCC f ∘' g) => ⟨_, .simple .comp'⟩
  | (DCC f ∘∘ g) => ⟨_, .simple .comp₂⟩
  | (DCC &(x)) => ⟨_, .compound (.boxed (x.evaluate env).snd)⟩
  | (DCC !(x)) => ⟨_, .compound (.bang (x.evaluate env).snd)⟩
  | (DCC ⟦β⟧(x, y)) => ⟨_, .compound (.coup (β.evaluate env).snd (x.evaluate env).snd (y.evaluate env).snd)⟩
  | (DCC Coup(β)) => ⟨_, .compound (.t_coup (β.evaluate env).snd)⟩
  | (DCC (x = y)) => ⟨_, .compound (.eq (x.evaluate env).snd (y.evaluate env).snd)⟩
  | (DCC (f x)) =>
    let ⟨f', h₁⟩ := f.evaluate env
    let ⟨x', h₂⟩ := x.evaluate env
    let ⟨e', h₃⟩ := f'.apply x'
    ⟨_, .app h₁ h₂ h₃⟩

def Semantic.Val.apply (f x : Semantic.Val) : ((e' : Semantic.Val) × Semantic.Apply f x e') :=
  match f, x with
  | Val(λ xs 2 => Eql(f_α)), Val(neutral(&(env))) => ⟨_, .simple .eql₁⟩
  | Val(λ env 1 => Eql(f_α)), Val(neutral(&(x))) => ⟨_, .simple .eql₂⟩
  | Val(λ env 1 => *(α)), Val(neutral(&(x))) => ⟨_, .simple .unbox⟩
  | Val(λ env 1 => Id(α)), x => ⟨_, .simple .id⟩
  | Val(λ env 1 => Fstc(_α)), Val(neutral(⟦β⟧(a, b))) => ⟨_, .simple .fstc⟩
  | Val(λ env 1 => Sndc(_α)), Val(neutral(⟦β⟧(a, b))) => ⟨_, .simple .sndc⟩
  | Val(λ env 2 => Λ(α, β, x)), Val(neutral(&(y))) => ⟨_, .simple .curr₁⟩
  | Val(λ env 2 => !Λ(α, β, x)), Val(neutral(&(y))) => ⟨_, .simple .curr'₁⟩
  | Val(λ env 1 => !<f>), Val(neutral(&(x))) =>
    let ⟨f', h₁⟩ :=  f.eval []
    let e' := 

end

