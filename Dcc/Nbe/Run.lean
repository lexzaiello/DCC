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
      
      sorry
    match f.apply x with
    | .some ⟨_, h⟩ => .some ⟨_, .map h⟩
    | _ => .none
  | Val(λ env 1 => $<f>), Val(neutral(&(x))) =>
    match f.apply x with
    | .some ⟨_, h⟩ => .some ⟨_, .fmap h⟩
    | _ => .none
  | Val(λ env 1 => ⟦β⟧⟨M, N⟩), Val(neutral(&(x))) =>
    match M.apply x, N.apply x with
    | .some ⟨A, h₁⟩, .some ⟨B, h₂⟩ =>
      have h_dec₁ := h₁.decreasing
      have h_dec₂ := h₂.decreasing
      match B.apply A with
      | .some ⟨_, h₃⟩ =>
        .some ⟨_, .pair h₁ h₂ h₃⟩
      | _ => .none
    | _, _ => .none
  | Val(λ env 1 => Eval(_α, _β, x)), Val(neutral(⟦__β⟧(y, z))) =>
    match x.apply y with
    | .some ⟨f', h₁⟩ =>
      have h_dec₁ := h₁.decreasing
      match f'.apply z with
      | .some ⟨_, h₂⟩ =>
        .some ⟨_, .eval h₁ h₂⟩
      | _ => .none
    | _ => .none
  | Val(λ env 1 => `(β, x)), _y =>
    .some ⟨_, .quot⟩
  | Val(λ env 1 => f ∘' g), x =>
    match g.apply x with
    | .some ⟨A, h₁⟩ =>
      have h_dec := h₁.decreasing
      match f.apply A with
      | .some ⟨_, h₂⟩ => .some ⟨_, .comp' h₁ h₂⟩
      | _ => .none
    | _ => .none
  | Val(λ env 1 => f ∘ g), x =>
    match g.apply x with
    | .some ⟨A, h₁⟩ =>
      have h_dec := h₁.decreasing
      match f.apply A with
      | .some ⟨_, h₂⟩ => .some ⟨_, .comp h₁ h₂⟩
      | _ => .none
    | _ => .none
  | Val(λ env 1 => f ∘∘ g), x =>
    match g.apply x with
    | .some ⟨A, h₁⟩ =>
      have h_dec := h₁.decreasing
      match f.apply A with
      | .some ⟨_, h₂⟩ => .some ⟨_, .comp₂ h₁ h₂⟩
      | _ => .none
    | _ => .none
  | Val(λ y::env 1 => Λ(α, β, x)), z =>
    match x.apply Val(neutral(⟦β⟧(y, z))) with
    | .some ⟨_, h⟩ => .some ⟨_, .curr₂ h⟩
    | _ => .none
  | Val(λ neutral(&(y))::env 1 => !Λ(α, β, x)), Val(neutral(&(z))) =>
    match x.apply Val(neutral(&(neutral(⟦β⟧(y, z))))) with
    | .some ⟨_, h⟩ => .some ⟨_, .curr'₂ h⟩
    | _ => .none
  | _, _ => .none
termination_by f.measure + x.measure

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

