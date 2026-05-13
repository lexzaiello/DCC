import Dcc.Attrs
import Dcc.Ast
import Dcc.Relation
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
  | fstc   : Size (DCC Fstc(_α)) 1
  | snd'   : Size (DCC Snd'(δ, β)) 1
  | sndc   : Size (DCC Sndc(_α)) 1
  | snd    : Size (DCC Snd(_α)) 1
  | comp'  : Size f m → Size g n → Size (DCC (f ∘' g)) (m + n).succ
  | comp   : Size f m → Size g n → Size (DCC (f ∘ g)) (m + n).succ
  | pair   : Size f m → Size g n → Size (DCC ⟨f, g⟩) (m + n).succ
  | curr   : Size x m → Size (DCC Λ(α, β, x)) m.succ
  | app    : Size f m → Size x n → Size (DCC (f x)) (m + n)

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind] def size (e : Expr) : ((n : ℕ) × (PULift.{1, 0} (Size e n))) :=
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
  | DCC Fstc(_α) => ⟨_, ⟨.fstc⟩⟩
  | DCC Snd'(_α,_β) => ⟨_, ⟨.snd'⟩⟩
  | DCC Snd(_α) => ⟨_, ⟨.snd⟩⟩
  | DCC Sndc(_α) => ⟨_, ⟨.sndc⟩⟩
  | DCC Π(_α, _β) => ⟨_, ⟨.pi⟩⟩
  | DCC (f ∘' g) =>
    let ⟨_m, ⟨h₁⟩⟩ := f.size
    let ⟨_n, ⟨h₂⟩⟩ := g.size
    ⟨_, ⟨.comp' h₁ h₂⟩⟩
  | DCC (f ∘ g) =>
    let ⟨_m, ⟨h₁⟩⟩ := f.size
    let ⟨_n, ⟨h₂⟩⟩ := g.size
    ⟨_, ⟨.comp h₁ h₂⟩⟩
  | DCC ⟨a, b⟩ =>
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

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance Size.instMeasure : Measure Size where
  run := size

end Expr
