import Dcc.Ast
import Dcc.Relation

namespace Expr

inductive EtaSize : Expr → ℕ → Prop
  | tintro : EtaSize (DCC ∗) 1
  | top    : EtaSize (DCC ⊤) 1
  | bot    : EtaSize (DCC ⊥) 1
  | subst  : EtaSize x m → EtaSize y n → EtaSize (DCC Subst(x, y)) (m + n).succ.succ
  | sig    : EtaSize β m → EtaSize (DCC Σ(β)) m.succ
  | coup   : EtaSize x m → EtaSize y n → EtaSize (DCC ⟦β⟧(x, y)) (m + n).succ
  | sort   : EtaSize (DCC Sort m) 1
  | pi     : EtaSize β m → EtaSize (DCC Π(α, β)) m.succ
  | quot   : EtaSize x m → EtaSize (DCC `(β, x)) m.succ.succ
  | id     : EtaSize (DCC Id(α)) 2
  | fst    : EtaSize (DCC Fst(_α)) 2
  | snd'   : EtaSize (DCC Snd'(δ, β)) 2
  | snd    : EtaSize (DCC Snd(_α)) 2
  | appl   : EtaSize f_α m → EtaSize (DCC App(_m, _n, f_α, f_β)) (m + 7)
  | app'   : EtaSize (DCC App'(_α, β)) 2
  | comp   : EtaSize f m → EtaSize g n → EtaSize (DCC (f ∘ g)) (m + n).succ.succ
  | pair   : EtaSize f m → EtaSize g n → EtaSize (DCC ⟦_m, α, β, γ⟧⟨f, g⟩) (m + n).succ.succ
  | curr   : EtaSize x m → EtaSize (DCC Λ(α, β, x)) m.succ.succ
  | app    : EtaSize f m → EtaSize x n → EtaSize (DCC (f x)) (m + n)

@[aesop norm, simp, grind] def eta_size (e : Expr) : ((n : ℕ) × (PULift.{1, 0} (EtaSize e n))) :=
  match e with
  | DCC ∗ => ⟨_, ⟨.tintro⟩⟩
  | DCC ⊤ => ⟨_, ⟨.top⟩⟩
  | DCC ⊥ => ⟨_, ⟨.bot⟩⟩
  | DCC Subst(x, y) =>
    let ⟨_, ⟨h₁⟩⟩ := x.eta_size
    let ⟨_, ⟨h₂⟩⟩ := y.eta_size
    ⟨_, ⟨.subst h₁ h₂⟩⟩
  | DCC Sort _m => ⟨_, ⟨.sort⟩⟩
  | DCC Σ(β) =>
    let ⟨_, ⟨h₁⟩⟩ := β.eta_size
    ⟨_, ⟨.sig h₁⟩⟩
  | DCC `(_β, x) =>
    let ⟨_, ⟨h₁⟩⟩ := x.eta_size
    ⟨_, ⟨.quot h₁⟩⟩
  | DCC ⟦_β⟧(x, y) =>
    let ⟨_, ⟨h₁⟩⟩ := x.eta_size
    let ⟨_, ⟨h₂⟩⟩ := y.eta_size
    ⟨_, ⟨.coup h₁ h₂⟩⟩
  | DCC Id(_α)      => ⟨_, ⟨.id⟩⟩
  | DCC Fst(_α) => ⟨_, ⟨.fst⟩⟩
  | DCC Snd'(_α,_β) => ⟨_, ⟨.snd'⟩⟩
  | DCC Snd(_α) => ⟨_, ⟨.snd⟩⟩
  | DCC Π(_α, β) =>
    let ⟨_, ⟨h₁⟩⟩ := β.eta_size
    ⟨_, ⟨.pi h₁⟩⟩
  | DCC App'(_α, _β) => ⟨_, ⟨.app'⟩⟩
  | DCC App(_m, _n, α, _β)  =>
    let ⟨_, ⟨h⟩⟩ := α.eta_size
    ⟨_, ⟨.appl h⟩⟩
  | DCC (f ∘ g) =>
    let ⟨_m, ⟨h₁⟩⟩ := f.eta_size
    let ⟨_n, ⟨h₂⟩⟩ := g.eta_size
    ⟨_, ⟨.comp h₁ h₂⟩⟩
  | DCC ⟦_m, _α, _β, _γ⟧⟨a, b⟩ =>
    let ⟨_o, ⟨h₁⟩⟩ := a.eta_size
    let ⟨_p, ⟨h₂⟩⟩ := b.eta_size
    ⟨_, ⟨.pair h₁ h₂⟩⟩
  | DCC Λ(_α, _β, x) =>
    let ⟨_n, ⟨h₁⟩⟩ := x.eta_size
    ⟨_, ⟨.curr h₁⟩⟩
  | DCC (f x) =>
    let ⟨_, ⟨h₁⟩⟩ := f.eta_size
    let ⟨_, ⟨h₂⟩⟩ := x.eta_size
    ⟨_, ⟨.app h₁ h₂⟩⟩

@[simp] instance Size.instMeasure : Measure EtaSize where
  run := eta_size

end Expr
