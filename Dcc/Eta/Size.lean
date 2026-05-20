import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Size
import Dcc.Aff.Red

namespace Expr

inductive EtaSize : Expr → ℕ → Prop
  | tintro : EtaSize (DCC ∗) 1
  | top    : EtaSize (DCC ⊤) 1
  | bot    : EtaSize (DCC ⊥) 1
  | subst  : EtaSize x m → EtaSize y n → EtaSize (DCC Subst(x, y)) (m + m + n).succ.succ.succ
  | sig    : EtaSize α m → EtaSize β n → EtaSize (DCC Σ(α, β)) (m + n).succ
  | coup   : EtaSize β m → EtaSize (DCC Coup(β)) m
  | mk     : EtaSize x m → EtaSize y n → EtaSize (DCC ⟦β⟧(x, y)) (m + n).succ
  | sort   : EtaSize (DCC Sort m) 1
  | pi     : EtaSize β m → EtaSize (DCC Π(α, β)) m.succ
  | quot   : EtaSize x m → EtaSize (DCC `(β, x)) m.succ
  | id     : EtaSize (DCC Id(α)) 2
  | fst    : EtaSize (DCC Fst(_α, _β)) 2
  | fstc   : EtaSize (DCC Fstc(_α)) 2
  | snd'   : EtaSize (DCC Snd'(δ, β)) 2
  | sndc   : EtaSize (DCC Sndc(_α)) 2
  | snd    : EtaSize (DCC Snd(_α, _β)) 2
  | comp   : EtaSize f m → EtaSize g n → EtaSize (DCC (f ∘ g)) (m + m + n).succ.succ
  | comp'  : EtaSize f m → EtaSize g n → EtaSize (DCC (f ∘' g)) (m + m + n).succ.succ
  | pair   : EtaSize f m → EtaSize g n → EtaSize (DCC ⟨f, g⟩) (m + n).succ.succ
  | curr   : EtaSize x m → EtaSize (DCC Λ(α, β, x)) m.succ.succ
  | eq     : EtaSize α m → EtaSize β n → EtaSize (DCC =(α, β)) (m + n).succ
  | refl   : EtaSize α m → EtaSize (DCC refl(α)) m.succ
  | app    : EtaSize f m → EtaSize x n → EtaSize (DCC (f x)) (m + n)

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind] def eta_size (e : Expr) : ((n : ℕ) × (PULift.{1, 0} (EtaSize e n))) :=
  match e with
  | DCC ∗ => ⟨_, ⟨.tintro⟩⟩
  | DCC ⊤ => ⟨_, ⟨.top⟩⟩
  | DCC ⊥ => ⟨_, ⟨.bot⟩⟩
  | DCC Subst(x, y) =>
    let ⟨_, ⟨h₁⟩⟩ := x.eta_size
    let ⟨_, ⟨h₂⟩⟩ := y.eta_size
    ⟨_, ⟨.subst h₁ h₂⟩⟩
  | DCC Sort _m => ⟨_, ⟨.sort⟩⟩
  | DCC Σ(α, β) =>
    let ⟨_, ⟨h₁⟩⟩ := α.eta_size
    let ⟨_, ⟨h₂⟩⟩ := β.eta_size
    ⟨_, ⟨.sig h₁ h₂⟩⟩
  | DCC Coup(β) =>
    let ⟨_, ⟨h₁⟩⟩ := β.eta_size
    ⟨_, ⟨.coup h₁⟩⟩
  | DCC `(_β, x) =>
    let ⟨_, ⟨h₁⟩⟩ := x.eta_size
    ⟨_, ⟨.quot h₁⟩⟩
  | DCC ⟦_β⟧(x, y) =>
    let ⟨_, ⟨h₁⟩⟩ := x.eta_size
    let ⟨_, ⟨h₂⟩⟩ := y.eta_size
    ⟨_, ⟨.mk h₁ h₂⟩⟩
  | DCC Id(_α)      => ⟨_, ⟨.id⟩⟩
  | DCC Fst(_α, _β) => ⟨_, ⟨.fst⟩⟩
  | DCC Fstc(_α) => ⟨_, ⟨.fstc⟩⟩
  | DCC Sndc(_α) => ⟨_, ⟨.sndc⟩⟩
  | DCC Snd'(_α,_β) => ⟨_, ⟨.snd'⟩⟩
  | DCC =(α, β) =>
    let ⟨_, ⟨h₁⟩⟩ := α.eta_size
    let ⟨_, ⟨h₂⟩⟩ := β.eta_size
    ⟨_, ⟨.eq h₁ h₂⟩⟩
  | DCC refl(α) =>
    let ⟨_, ⟨h₁⟩⟩ := α.eta_size
    ⟨_, ⟨.refl h₁⟩⟩
  | DCC Snd(_α, _β) => ⟨_, ⟨.snd⟩⟩
  | DCC Π(_α, β) =>
    let ⟨_, ⟨h₁⟩⟩ := β.eta_size
    ⟨_, ⟨.pi h₁⟩⟩
  | DCC (f ∘ g) =>
    let ⟨_m, ⟨h₁⟩⟩ := f.eta_size
    let ⟨_n, ⟨h₂⟩⟩ := g.eta_size
    ⟨_, ⟨.comp h₁ h₂⟩⟩
  | DCC (f ∘' g) =>
    let ⟨_m, ⟨h₁⟩⟩ := f.eta_size
    let ⟨_n, ⟨h₂⟩⟩ := g.eta_size
    ⟨_, ⟨.comp' h₁ h₂⟩⟩
  | DCC ⟨a, b⟩ =>
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

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance EtaSize.instMeasure : Measure EtaSize where
  run := eta_size

@[dcc_size, grind ., grind! .] theorem size_lte_eta_size : (Expr.size A).fst < A.eta_size.fst := by
  induction A <;> grind

/-@[dcc_size] theorem aff_eta_decreasing? (h : Relation.ReflTransGen RedAff A B) : (Expr.eta_size B).fst ≤ A.eta_size.fst := by
  rw [← Relation.reflGen_transGen] at h
  if hn : (Expr.eta_size B).fst = (Expr.eta_size A).fst then
    simp_all
  else
    match h with
    | .refl =>
      sorry
    | .single h =>
      have h_dec : (size B).fst < (size A).fst := RedAff.instRedRel.to_trans.decreasing h
      simp_all
      
      sorry-/

end Expr
