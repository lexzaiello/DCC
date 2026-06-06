import Dcc.Nbe.Value
import Dcc.Types
import Dcc.Nbe.Size
import Dcc.Nbe.SizeDecreasing
import Dcc.Nbe.ApplyEval
import Dcc.Metatheory.Value

mutual

def Expr.evaluate (env : List Semantic.Val) (e : Expr) : ((e' : Semantic.Val) × Semantic.Eval env e e') :=
  match e with
  | (DCC ⊤) => ⟨_, .top⟩
  | (DCC ∗) => ⟨_, .tintro⟩
  | (DCC ⊥) => ⟨_, .bot⟩
  | (DCC Sort _m) => ⟨_, .sort⟩
  | (DCC !<f>) =>
    match f.evaluate env with
    | ⟨_, h⟩ => ⟨_, .map h⟩
  | (DCC $<f>) =>
    match f.evaluate env with
    | ⟨_, h⟩ => ⟨_, .fmap h⟩
  | (DCC *(x)) =>
    match x.evaluate env with
    | ⟨_, h⟩ => ⟨_, .unbox h⟩
  | (DCC Eval(α, β, x)) =>
    match α.evaluate env, β.evaluate env, x.evaluate env with
    | ⟨_, h_α⟩, ⟨_, h_β⟩, ⟨_, h_x⟩ => ⟨_, .eval h_α h_β h_x⟩
  | (DCC `(β, x)) =>
    match β.evaluate env, x.evaluate env with
    | ⟨_, h_β⟩, ⟨_, h_x⟩ => ⟨_, .quot h_β h_x⟩
  | (DCC Id(α)) =>
    match α.evaluate env with
    | ⟨_, h_α⟩ => ⟨_, .id h_α⟩
  | (DCC Fstc(β)) =>
    match β.evaluate env with
    | ⟨_, h_β⟩ => ⟨_, .fstc h_β⟩
  | (DCC Sndc(β)) =>
    match β.evaluate env with
    | ⟨_, h_β⟩ => ⟨_, .sndc h_β⟩
  | (DCC Λ(α, β, x)) =>
    match α.evaluate env, β.evaluate env, x.evaluate env with
    | ⟨_, h_α⟩, ⟨_, h_β⟩, ⟨_, h_x⟩ => ⟨_, .curr h_α h_β h_x⟩
  | (DCC !Λ(α, β, x)) =>
    match α.evaluate env, β.evaluate env, x.evaluate env with
    | ⟨_, h_α⟩, ⟨_, h_β⟩, ⟨_, h_x⟩ => ⟨_, .curr' h_α h_β h_x⟩
  | (DCC Π(f_α, f_β)) =>
    match f_α.evaluate env, f_β.evaluate env with
    | ⟨_, h_α⟩, ⟨_, h_β⟩ => ⟨_, .pi h_α h_β⟩
  | (DCC ⟦β⟧⟨M, N⟩) =>
    match β.evaluate env, M.evaluate env, N.evaluate env with
    | ⟨_, h_β⟩, ⟨_, h_M⟩, ⟨_, h_N⟩ => ⟨_, .pair h_β h_M h_N⟩
  | (DCC Σ(α, β)) =>
    match α.evaluate env, β.evaluate env with
    | ⟨_, h_α⟩, ⟨_, h_β⟩ => ⟨_, .sigma h_α h_β⟩
  | (DCC Eql(f_α)) =>
    match f_α.evaluate env with
    | ⟨_, h_α⟩ => ⟨_, .eql h_α⟩
  | (DCC refl(f_α)) =>
    match f_α.evaluate env with
    | ⟨_, h_α⟩ => ⟨_, .refl h_α⟩
  | (DCC f ∘ g) =>
    match f.evaluate env, g.evaluate env with
    | ⟨_, h_f⟩, ⟨_, h_g⟩ => ⟨_, .comp h_f h_g⟩
  | (DCC f ∘' g) =>
    match f.evaluate env, g.evaluate env with
    | ⟨_, h_f⟩, ⟨_, h_g⟩ => ⟨_, .comp' h_f h_g⟩
  | (DCC f ∘∘ g) =>
    match f.evaluate env, g.evaluate env with
    | ⟨_, h_f⟩, ⟨_, h_g⟩ => ⟨_, .comp₂ h_f h_g⟩
  | (DCC &(x)) =>
    match x.evaluate env with
    | ⟨_, h_x⟩ => ⟨_, .boxed h_x⟩
  | (DCC !(x)) =>
    match x.evaluate env with
    | ⟨_, h_x⟩ => ⟨_, .bang h_x⟩
  | (DCC ⟦β⟧(x, y)) =>
    match β.evaluate env, x.evaluate env, y.evaluate env with
    | ⟨_, h_β⟩, ⟨_, h_x⟩, ⟨_, h_y⟩ => ⟨_, .coup h_β h_x h_y⟩
  | (DCC Coup(β)) =>
    match β.evaluate env with
    | ⟨_, h_β⟩ => ⟨_, .t_coup h_β⟩
  | (DCC (x = y)) =>
    match x.evaluate env, y.evaluate env with
    | ⟨_, h_x⟩, ⟨_, h_y⟩ => ⟨_, .eq h_x h_y⟩
  | (DCC (f x)) =>
    match f.evaluate env, x.evaluate env with
    | ⟨f', h₁⟩, ⟨x', h₂⟩ =>
      match f'.apply x' with
      | .some ⟨_, h₃⟩ => ⟨_, .app h₁ h₂ h₃⟩
      | _ => .none
    | _, _ => .none

def Semantic.Val.apply (f x : Semantic.Val) : Option ((e' : Semantic.Val) × Semantic.Apply f x e') :=
  match f, x with
  | Val(Π (f_α) env 1, f_β), x => .some ⟨_, .pi⟩
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
