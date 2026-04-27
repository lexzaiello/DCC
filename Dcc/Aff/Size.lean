import Dcc.Ast
import Mathlib.Tactic

namespace Expr

inductive Size : Expr → ℕ → Prop
  | tintro : Size (DCC ∗) 0
  | top    : Size (DCC ⊤) 0
  | bot    : Size (DCC ⊥) 0
  | subst  : Size x m → Size y n → Size (DCC Subst(x, y)) (m + n).succ
  | sig    : Size (DCC Σ(β)) 0
  | coup   : Size x m → Size y n → Size (DCC ⟦β⟧(x, y)) (m + n)
  | sort   : Size (DCC Sort m) 0
  | pi     : Size (DCC Π(α, β)) 0
  | quot   : Size x m → Size (DCC `(β, x)) m.succ
  | id     : Size (DCC Id(α)) 1
  | fst    : Size (DCC Fst(_α)) 1
  | snd'   : Size (DCC Snd'(δ, β)) 1
  | snd    : Size (DCC Snd(_α)) 1
  | appl   : Size f_α m → Size (DCC App(_m, _n, f_α, f_β)) (m + 6)
  | app'   : Size (DCC App'(_α, β)) 1
  | comp   : Size f m → Size g n → Size (DCC (f ∘ g)) (m + n).succ.succ
  | pair   : Size f m → Size g n → Size (DCC ⟦_m, α, β, γ⟧⟨f, g⟩) (m + n).succ
  | curr   : Size x m → Size (DCC Λ(α, β, x)) m.succ
  | app    : Size f m → Size x n → Size (DCC (f x)) (m + n)

@[simp, grind] def size (e : Expr) : ((n : ℕ) × (PLift (Size e n))) :=
  match e with
  | DCC ∗ => ⟨_, ⟨.tintro⟩⟩
  | DCC ⊤ => ⟨_, ⟨.top⟩⟩
  | DCC ⊥ => ⟨_, ⟨.bot⟩⟩
  | DCC Subst(x, y) =>
    let ⟨_, ⟨h₁⟩⟩ := x.size
    let ⟨_, ⟨h₂⟩⟩ := y.size
    ⟨_, ⟨.subst h₁ h₂⟩⟩
  | DCC Sort _m => ⟨_, ⟨.sort⟩⟩
  | DCC Σ(_β) => ⟨_, ⟨.sig⟩⟩
  | DCC `(_β, x) =>
    let ⟨_, ⟨h₁⟩⟩ := x.size
    ⟨_, ⟨.quot h₁⟩⟩
  | DCC ⟦_β⟧(x, y) =>
    let ⟨_, ⟨h₁⟩⟩ := x.size
    let ⟨_, ⟨h₂⟩⟩ := y.size
    ⟨_, ⟨.coup h₁ h₂⟩⟩
  | DCC Id(_α)      => ⟨_, ⟨.id⟩⟩
  | DCC Fst(_α) => ⟨_, ⟨.fst⟩⟩
  | DCC Snd'(_α,_β) => ⟨_, ⟨.snd'⟩⟩
  | DCC Snd(_α) => ⟨_, ⟨.snd⟩⟩
  | DCC Π(_α, _β) => ⟨_, ⟨.pi⟩⟩
  | DCC App'(_α, _β) => ⟨_, ⟨.app'⟩⟩
  | DCC App(_m, _n, α, _β)  =>
    let ⟨_, ⟨h⟩⟩ := α.size
    ⟨_, ⟨.appl h⟩⟩
  | DCC (f ∘ g) =>
    let ⟨_m, ⟨h₁⟩⟩ := f.size
    let ⟨_n, ⟨h₂⟩⟩ := g.size
    ⟨_, ⟨.comp h₁ h₂⟩⟩
  | DCC ⟦_m, _α, _β, _γ⟧⟨a, b⟩ =>
    let ⟨_o, ⟨h₁⟩⟩ := a.size
    let ⟨_p, ⟨h₂⟩⟩ := b.size
    ⟨_, ⟨.pair h₁ h₂⟩⟩
  | DCC Λ(_α, _β, x) =>
    let ⟨_n, ⟨h₁⟩⟩ := x.size
    ⟨_, ⟨.curr h₁⟩⟩
  | DCC (f x) =>
    let ⟨_, ⟨h₁⟩⟩ := f.size
    let ⟨_, ⟨h₂⟩⟩ := x.size
    ⟨_, ⟨.app h₁ h₂⟩⟩

theorem Size.sound (_h : Expr.size e = ⟨n, ⟨h⟩⟩) : Size e n := h

@[aesop safe destruct, grind =_, grind →, simp] theorem Size.complete (h : Size e n) : size e = ⟨n, .up h⟩ := by
  induction h with
  | sig | app' | pi | tintro | bot | top | snd' | id | snd | fst | sort => rfl
  | comp _ _ ih₁ ih₂ | coup _ _ ih₁ ih₂ => rw [size, ih₁, ih₂]
  | appl _ ih | quot _ ih | curr _ ih => rw [size, ih]
  | subst _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ => rw [size, ih₁, ih₂]

end Expr
