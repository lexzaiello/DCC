import Dcc.Nbe.Value
import Dcc.Nbe.Size
import Dcc.Nbe.ApplyEval
import Dcc.Metatheory.Value

mutual

def Expr.evaluate (env : List Semantic.Val) (e : Expr) : ((e' : Semantic.Val) × Semantic.Eval env e e') :=
  match e with
  | (DCC ⊤) => ⟨_, .top⟩
  | (DCC ∗) => ⟨_, .tintro⟩
  | (DCC ⊥) => ⟨_, .bot⟩
  | (DCC Sort _m) => ⟨_, .sort⟩
  | (DCC !<f>) => ⟨_, .map (f.evaluate env).snd⟩
  | (DCC $<f>) => ⟨_, .fmap (f.evaluate env).snd⟩
  | (DCC *(x)) => ⟨_, .unbox (x.evaluate env).snd⟩
  | (DCC Eval(α, β, x)) => ⟨_, .eval (α.evaluate env).snd (β.evaluate env).snd (x.evaluate env).snd⟩
  | (DCC `(β, x)) => ⟨_, .quot (β.evaluate env).snd (x.evaluate env).snd⟩
  | (DCC Id(α)) => ⟨_, .id (α.evaluate env).snd⟩
  | (DCC Fstc(β)) => ⟨_, .fstc (β.evaluate env).snd⟩
  | (DCC Sndc(β)) => ⟨_, .sndc (β.evaluate env).snd⟩
  | (DCC Λ(α, β, x)) => ⟨_, .curr (α.evaluate env).snd (β.evaluate env).snd (x.evaluate env).snd⟩
  | (DCC !Λ(α, β, x)) => ⟨_, .curr' (α.evaluate env).snd (β.evaluate env).snd (x.evaluate env).snd⟩
  | (DCC Π(f_α, f_β)) => ⟨_, .pi (f_α.evaluate env).snd (f_β.evaluate env).snd⟩
  | (DCC ⟦β⟧⟨M, N⟩) => ⟨_, .pair (β.evaluate env).snd (M.evaluate env).snd (N.evaluate env).snd⟩
  | (DCC Σ(α, β)) => ⟨_, .sigma (α.evaluate env).snd (β.evaluate env).snd⟩
  | (DCC Eql(f_α)) => ⟨_, .eql (f_α.evaluate env).snd⟩
  | (DCC refl(f_α)) => ⟨_, .refl (f_α.evaluate env).snd⟩
  | (DCC f ∘ g) => ⟨_, .comp (f.evaluate env).snd (g.evaluate env).snd⟩
  | (DCC f ∘' g) => ⟨_, .comp' (f.evaluate env).snd (g.evaluate env).snd⟩
  | (DCC f ∘∘ g) => ⟨_, .comp₂ (f.evaluate env).snd (g.evaluate env).snd⟩
  | (DCC &(x)) => ⟨_, .boxed (x.evaluate env).snd⟩
  | (DCC !(x)) => ⟨_, .bang (x.evaluate env).snd⟩
  | (DCC ⟦β⟧(x, y)) => ⟨_, .coup (β.evaluate env).snd (x.evaluate env).snd (y.evaluate env).snd⟩
  | (DCC Coup(β)) => ⟨_, .t_coup (β.evaluate env).snd⟩
  | (DCC (x = y)) => ⟨_, .eq (x.evaluate env).snd (y.evaluate env).snd⟩
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

