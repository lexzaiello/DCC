import Dcc.Nbe.Value
import Dcc.Nbe.Size
import Dcc.Metatheory.Value
import Dcc.Nbe.RunEvalApply

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
    → Val.Quote level Val(Π (f_α) ⟦⟧ 1, f_β) (DCC (Π(f_α'', f_β'')))
  | pi₂  : Apply f_α Val(neutral(var(level))) Val(λ env' n' => bdy')
    → Apply f_β Val(neutral(var(level))) Val(neutral(f_β' neutral(var(level))))
    → Val.Quote level.succ Val(λ env' n' => bdy') f_α''
    → Neutral.Quote level.succ.succ f_β' f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 1, f_β) (DCC (Π(f_α'', f_β'')))
  | pi₃  : Apply f_α Val(neutral(var(level))) Val(neutral(f_α' neutral(var(level))))
    → Apply f_β Val(neutral(var(level))) Val(λ env' n' => bdy')
    → Neutral.Quote level.succ f_α' f_α''
    → Val.Quote level.succ.succ Val(λ env' n' => bdy') f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 1, f_β) (DCC (Π(f_α'', f_β'')))
  | pi₄ : Apply f_α Val(neutral(var(level))) Val(λ env'₁ n'₁ => bdy'₁)
    → Apply f_β Val(neutral(var(level))) Val(λ env'₂ n'₂ => bdy'₂)
    → Val.Quote level.succ Val(λ env'₁ n'₁ => bdy'₁) f_α''
    → Val.Quote level.succ.succ Val(λ env'₂ n'₂ => bdy'₂) f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 1, f_β) (DCC (Π(f_α'', f_β'')))
  | pi' : Apply f_α env f_α₁
    → Apply f_α₁ Val(neutral(var(level))) Val(neutral(f_α₂ neutral(var(level))))
    → Apply f_β env f_β₁
    → Apply f_β₁ Val(neutral(var(level.succ))) Val(neutral(f_β₂ neutral(var(level.succ))))
    → Neutral.Quote level.succ f_α₂ f_α'
    → Neutral.Quote level.succ.succ f_β₂ f_β'
    → Val.Quote level env env'
    → Val.Quote level Val(Π (f_α) ⟦env⟧ 0, f_β) (DCC (Π(f_α', f_β') env'))

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
termination_by (v.size, sizeOf v)

def Val.quote (level : ℕ) (v : Val) : Option ((e : Expr) × v.Quote level e) :=
  match v with
  | Val(neutral(neut)) =>
    have h_dec : neut.size ≤ Val(neutral(neut)).measure := by
      grind
    match neut.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .neut h⟩
    | _ => .none
  | Val(λ env n => bdy) =>
    match Val(λ env n => bdy).apply Val(neutral(var(level))) with
    | .some ⟨Val(neutral(f' neutral(var(level₂)))), h₁⟩ =>
      have h_dec₁ := h₁.decreasing
      have h_dec₂ : f'.size < (Val.neut (Neutral.tm (NeutralTm.app f' (Val.neut (Neutral.var level₂))))).measure := by
        grind
      have h_dec₃ : f'.size < Val(λ env n => bdy).measure := by
        grind
      if heq : level₂ = level then
        match f'.quote level.succ with
        | .some ⟨_, h₂⟩ =>
          heq ▸ .some ⟨_, .lam₁ (heq.symm ▸ h₁) (heq ▸ h₂)⟩
        | _ => .none
      else .none
    | .some ⟨Val(λ env' n' => bdy'), h₁⟩ =>
      have h_dec₁ : Val(λ env' n' => bdy').measure < Val(λ env n => bdy).measure + Val(neutral(var(level))).measure := h₁.decreasing
      have h_dec₂ : Val(λ env' n' => bdy').measure < Val(λ env n => bdy).measure := by
        grind
      match Val(λ env' n' => bdy').quote level.succ with
      | .some ⟨_, h₂⟩ =>
        .some ⟨_, .lam₂ h₁ h₂⟩
      | _ => .none
    | _ => .none
  | Val(Π (f_α) ⟦⟧ 1, f_β) =>
    match f_α.apply Val(neutral(var(level))), f_β.apply Val(neutral(var(level))) with
    | .some ⟨Val(neutral(f_α' neutral(var(level₂)))), h₁⟩,
      .some ⟨Val(neutral(f_β' neutral(var(level₃)))), h₂⟩ =>
      have h_dec₁ := h₁.decreasing
      have h_dec₂ : f_α'.size < Val(neutral(f_α' neutral(var(level)))).measure := by
        grind
      have h_dec₃ : f_α'.size < f_α.measure := by
        grind
      have h_dec₄ : f_α'.size < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        conv =>
          right
          simp [Val.measure]
          rfl
        grind
      have h_dec₅ := h₂.decreasing
      have h_dec₆ : f_β'.size < Val(neutral(f_β' neutral(var(level)))).measure := by
        grind
      have h_dec₇ : f_β'.size < f_β.measure := by
        grind
      have h_dec₈ : f_β'.size < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        conv =>
          right
          simp [Val.measure]
          rfl
        grind
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
      have h_dec₁ := h₁.decreasing
      have h_dec₂ : Val(λ env' n' => bdy').measure < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        grind
      have h_dec₅ := h₂.decreasing
      have h_dec₆ : f_β'.size < Val(neutral(f_β' neutral(var(level)))).measure := by
        grind
      have h_dec₇ : f_β'.size < f_β.measure := by
        grind
      have h_dec₈ : f_β'.size < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        conv =>
          right
          simp [Val.measure]
          rfl
        grind
      if heq₁ : level₂ = level then
        match Val(λ env' n' => bdy').quote level.succ, f_β'.quote level.succ.succ with
        | .some ⟨_, h₃⟩, .some ⟨_, h₄⟩ => by
          cases heq₁
          exact .some ⟨_, .pi₂ h₁ h₂ h₃ h₄⟩
        | _, _ => .none
      else .none
    | .some ⟨Val(neutral(f_α' neutral(var(level₂)))), h₁⟩,
      .some ⟨Val(λ env' n' => bdy'), h₂⟩ =>
      have h_dec₁ := h₂.decreasing
      have h_dec₂ : Val(λ env' n' => bdy').measure < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        grind
      have h_dec₅ := h₁.decreasing
      have h_dec₆ : f_α'.size < Val(neutral(f_α' neutral(var(level)))).measure := by
        grind
      have h_dec₇ : f_α'.size < f_α.measure := by
        grind
      have h_dec₈ : f_α'.size < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        conv =>
          right
          simp [Val.measure]
          rfl
        grind
      if heq₁ : level₂ = level then
        match Val(λ env' n' => bdy').quote level.succ.succ, f_α'.quote level.succ with
        | .some ⟨_, h₄⟩, .some ⟨_, h₃⟩ => by
          cases heq₁
          exact .some ⟨_, .pi₃ h₁ h₂ h₃ h₄⟩
        | _, _ => .none
      else .none
    | .some ⟨Val(λ env'₁ n'₁ => bdy'₁), h₁⟩,
      .some ⟨Val(λ env'₂ n'₂ => bdy'₂), h₂⟩ =>
      have h_dec₁ := h₁.decreasing
      have h_dec₂ := h₂.decreasing
      have h_dec₃ : Val(λ env'₁ n'₁ => bdy'₁).measure < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        grind
      have h_dec₃ : Val(λ env'₂ n'₂ => bdy'₂).measure < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        grind
      match Val(λ env'₁ n'₁ => bdy'₁).quote level.succ, Val(λ env'₂ n'₂ => bdy'₂).quote level.succ.succ with
      | .some ⟨_, h₃⟩, .some ⟨_, h₄⟩ => .some ⟨_, .pi₄ h₁ h₂ h₃ h₄⟩
      | _, _ => .none
    | _, _ => .none
  | Val(Π (f_α) ⟦env⟧ 0, f_β) => do
    let ⟨f_α₁, h₁⟩ ← f_α.apply env
    have h_dec₁ := h₁.decreasing
    have h_dec₁' : f_α₁.measure < Val(Π (f_α) ⟦env⟧ 0, f_β).measure := by
      grind
    let ⟨f_α₂, h₂⟩ ← f_α₁.apply Val(neutral(var(level)))
    let ⟨f_β₁, h₃⟩ ← f_β.apply env
    have h_dec₂ := h₂.decreasing
    have h_dec₃₃ := h₃.decreasing
    have h_dec₂' : f_β₁.measure < Val(Π (f_α) ⟦env⟧ 0, f_β).measure := by
      grind
    let ⟨f_β₂, h₄⟩ ← f_β₁.apply Val(neutral(var(level.succ)))
    have h_dec₃ := h₃.decreasing
    have h_dec₄ := h₄.decreasing
    match heq : f_α₂, f_β₂ with
    | Val(neutral(f_α₂' neutral(var(level₁)))), Val(neutral(f_β₂' neutral(var(level₂ + 1)))) =>
      if heq₁ : level₁ = level then
        if heq₂ : level₂ = level then
          have h_dec₅ : f_α₂'.size < (Val.pi [env] 0 f_α f_β).measure := by
            grind
          have h_dec₅ : f_β₂'.size < (Val.pi [env] 0 f_α f_β).measure := by
            grind
          let ⟨f_α', h₅⟩ ← f_α₂'.quote level.succ
          let ⟨f_β', h₆⟩ ← f_β₂'.quote level.succ.succ
          have h_env_dec : env.measure < (Val.pi [env] 0 f_α f_β).measure := by
            grind
          let ⟨env', h₇⟩ ← env.quote level
          by
            cases heq
            cases heq₁
            cases heq₂
            exact .some ⟨_, .pi' h₁ h₂ h₃ h₄ h₅ h₆ h₇⟩
        else .none
      else .none
    | _, _ => .none
  | _ => .none
termination_by (v.measure, sizeOf v)

end

#check Val.quote

end Semantic

/-
Pattern mtaching in some constructors might be able to use quote / the bullet technique to do a form of extensionality.

For example, β : α → Sort n.
Currently, we just check
Reduces (f_β env) `(α, ...).

We can instead check similarly to in the Π case.

Or probably just doing reduce_nbe would get us there. tbh.
-/
