import Dcc.CC.Ast
import Mathlib.Tactic

namespace Expr

inductive Red : Expr → Expr → Prop
  | app      : Red (DCC (App(_δ, _τ) ⟦β⟧(f, x))) (DCC (f x))
  | fst      : Red (DCC (Fst(_δ, _τ) ⟦β⟧(a, b))) a
  | snd      : Red (DCC (Snd(_δ, _τ) ⟦β⟧(a, b))) b
  | flip     : Red (DCC (Flip(e) x y)) (DCC (e y x))
  | id       : Red (DCC (Id(_α) x)) x
  | quot     : Red (DCC (`(_α, _β, x) y)) x
  | comp     : Red (DCC ((x ∘ y) z)) (DCC (x (y z)))
  | pair     : Red (DCC (⟦β⟧⟨f, g⟩ x)) (DCC ⟦β⟧((f x), (g x)))
  | curr     : Red (DCC (Λ(β, x) y z)) (DCC (x ⟦β⟧(y, z)))
  | sigl     : Red a a' → Red (DCC ⟦β⟧(a, b)) (DCC ⟦β⟧(a', b))
  | sigr     : Red b b' → Red (DCC ⟦β⟧(a, b)) (DCC ⟦β⟧(a, b'))
  | congrFun : Red f f' → Red (DCC (f x)) (DCC (f' x))
  | congrArg : Red x x' → Red (DCC (f x)) (DCC (f x'))

/-
Affine reduction: the base combinator types do not require any
duplication of arguments in the context. Affine reduction is used
for def-eq, as such.

This is essentially reduction, but without the pair rule.
-/
inductive RedAff : Expr → Expr → Prop
  | app      : RedAff (DCC (App(_δ, _τ) ⟦β⟧(f, x))) (DCC (f x))
  | fst      : RedAff (DCC (Fst(_δ, _τ) ⟦β⟧(a, b))) a
  | snd      : RedAff (DCC (Snd(_δ, _τ) ⟦β⟧(a, b))) b
  | flip     : RedAff (DCC (Flip(e) x y)) (DCC (e y x))
  | id       : RedAff (DCC (Id(_α) x)) x
  | quot     : RedAff (DCC (`(_α, _β, x) y)) x
  | comp     : RedAff (DCC ((x ∘ y) z)) (DCC (x (y z)))
  | curr     : RedAff (DCC (Λ(β, x) y z)) (DCC (x ⟦β⟧(y, z)))
  | sigl     : RedAff a a' → RedAff (DCC ⟦β⟧(a, b)) (DCC ⟦β⟧(a', b))
  | sigr     : RedAff b b' → RedAff (DCC ⟦β⟧(a, b)) (DCC ⟦β⟧(a, b'))
  | congrFun : RedAff f f' → RedAff (DCC (f x)) (DCC (f' x))
  | congrArg : RedAff x x' → RedAff (DCC (f x)) (DCC (f x'))

inductive Size : Expr → ℕ → Prop
  | sort   : Size (DCC Sort m) 1
  | flip   : Size e m → Size (DCC Flip(e)) m.succ
  | id     : Size α m → Size (DCC Id(α)) m.succ
  | quot   : Size α m → Size β n → Size x o → Size (DCC `(α, β, x)) (m + n + o).succ
  | comp   : Size f m → Size g n → Size (DCC (f ∘ g)) (m + n).succ
  | coup   : Size β m → Size f n → Size g o → Size (DCC ⟦β⟧(f, g)) (m + n + o).succ
  | pair   : Size β m → Size f n → Size g o → Size (DCC ⟦β⟧⟨f, g⟩) (m + n + o).succ
  | fst    : Size α m → Size β n → Size (DCC Fst(α, β)) (m + n).succ
  | snd    : Size α m → Size β n → Size (DCC Snd(α, β)) (m + n).succ
  | curr   : Size β m → Size x n → Size (DCC Λ(β, x)) (m + n).succ.succ
  | pi     : Size (DCC Π(_m, _n)) 1
  | appl   : Size α m → Size β n → Size (DCC App(α, β)) (m + n).succ
  | app    : Size f m → Size x n → Size (DCC (f x)) (m + n)
  | sig    : Size α m → Size β n → Size (DCC Σ(α, β)) (m + n).succ

def size (e : Expr) : ((n : ℕ) × (PLift (Size e n))) :=
  match e with
  | DCC Sort _m => ⟨1, ⟨.sort⟩⟩
  | DCC Σ(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    ⟨(m + n).succ, ⟨.sig h₁ h₂⟩⟩
  | DCC Flip(e) =>
    let ⟨m, ⟨h₁⟩⟩ := e.size
    ⟨m.succ, ⟨.flip h₁⟩⟩
  | DCC Id(α) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    ⟨m.succ, ⟨.id h₁⟩⟩
  | DCC `(α, β, x) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    let ⟨o, ⟨h₃⟩⟩ := x.size
    ⟨(m + n + o).succ, ⟨.quot h₁ h₂ h₃⟩⟩
  | DCC (f ∘ g) =>
    let ⟨m, ⟨h₁⟩⟩ := f.size
    let ⟨n, ⟨h₂⟩⟩ := g.size
    ⟨(m + n).succ, ⟨.comp h₁ h₂⟩⟩
  | DCC ⟦β⟧(a, b) =>
    let ⟨m, ⟨h₁⟩⟩ := β.size
    let ⟨n, ⟨h₂⟩⟩ := a.size
    let ⟨o, ⟨h₃⟩⟩ := b.size
    ⟨(m + n + o).succ, ⟨.coup h₁ h₂ h₃⟩⟩
  | DCC ⟦β⟧⟨a, b⟩ =>
    let ⟨m, ⟨h₁⟩⟩ := β.size
    let ⟨n, ⟨h₂⟩⟩ := a.size
    let ⟨o, ⟨h₃⟩⟩ := b.size
    ⟨(m + n + o).succ, ⟨.pair h₁ h₂ h₃⟩⟩
  | DCC Fst(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    ⟨(m + n).succ, ⟨.fst h₁ h₂⟩⟩
  | DCC Snd(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    ⟨(m + n).succ, ⟨.snd h₁ h₂⟩⟩
  | DCC Λ(β, x) =>
    let ⟨m, ⟨h₁⟩⟩ := β.size
    let ⟨n, ⟨h₂⟩⟩ := x.size
    ⟨(m + n).succ.succ, ⟨.curr h₁ h₂⟩⟩
  | DCC Π(_m, _n) =>
    ⟨1, ⟨.pi⟩⟩
  | DCC App(α, β) =>
    let ⟨m, ⟨h₁⟩⟩ := α.size
    let ⟨n, ⟨h₂⟩⟩ := β.size
    ⟨(m + n).succ, ⟨.appl h₁ h₂⟩⟩
  | DCC (f x) =>
    let ⟨m, ⟨h₁⟩⟩ := f.size
    let ⟨n, ⟨h₂⟩⟩ := x.size
    ⟨(m + n), ⟨.app h₁ h₂⟩⟩

theorem Size.no_zero (h : Size e n) : n ≠ 0 := by
  induction h
  repeat simp
  case app f m x n hf hx ih₁ ih₂ =>
    intro h
    simp_all only [ne_eq, not_true_eq_false]
  simp

theorem Size.sound (_h : Expr.size e = ⟨n, ⟨h⟩⟩) : Size e n := h

theorem no_zero_size' : (size e).fst ≠ 0 := by
  intro ha
  have h := (size e).snd.down.no_zero
  simp_all only

theorem size_pos : 0 < (size e).fst := by
  have h := no_zero_size' (e := e)
  if h : (size e).fst = 0 then
    contradiction
  else grind

theorem Size.complete (h : Size e n) : size e = ⟨n, .up h⟩ := by
  induction h with
  | sort | pi => rfl
  | flip h ih₁ =>
    unfold size
    rw [ih₁]
  | curr h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | quot h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    unfold size
    rw [ih₁, ih₂, ih₃]
  | fst h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | snd h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | sig h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | id h₁ ih₁ =>
    unfold size
    rw [ih₁]
  | appl h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | comp h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]
  | pair h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    unfold size
    rw [ih₁, ih₂, ih₃]
  | coup h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    unfold size
    rw [ih₁, ih₂, ih₃]
  | app h₁ h₂ ih₁ ih₂ =>
    unfold size
    rw [ih₁, ih₂]

instance instSizeOf : SizeOf Expr := ⟨fun e => e.size.fst⟩

def RedAffTrans     := Relation.TransGen RedAff
def RedAffReflTrans := Relation.ReflTransGen RedAff

theorem RedAff.decreasing : RedAff e e' → (size e').fst < (size e).fst := by
  intro h
  induction h
  repeat (simp [size]; (repeat grind))

theorem RedAffTrans.decreasing : RedAffTrans e e' → (size e').fst < (size e).fst := by
  intro h
  induction h with
  | single h =>
    exact h.decreasing
  | tail h₁ hr ih =>
    have h := hr.decreasing
    grind

def RedAff.SN (e : Expr) : Acc (fun b a => RedAff a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing
  exact RedAff.SN e')
termination_by e

def RedAffTrans.SN (e : Expr) : Acc (fun b a => RedAffTrans a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing
  exact RedAffTrans.SN e')
termination_by e

theorem RedAffTrans.congrArg (h_red : RedAffTrans x x') : RedAffTrans (DCC (f x)) (DCC (f x')) := by
  induction h_red with
  | single h => exact .single (.congrArg (by assumption))
  | tail h => exact .trans (by assumption) (.single (.congrArg (by assumption)))

theorem RedAffTrans.congrFun (h_red : RedAffTrans f f') : RedAffTrans (DCC (f x)) (DCC (f' x)) := by
  induction h_red with
  | single h => exact .single (.congrFun (by assumption))
  | tail h => exact .trans (by assumption) (.single (.congrFun (by assumption)))

theorem RedAffReflTrans.congrArg (h_red : RedAffReflTrans x x') : RedAffReflTrans (DCC (f x)) (DCC (f x')) := by
  unfold RedAffReflTrans at h_red
  rw [← Relation.reflGen_transGen] at h_red
  match heq : h_red with
  | .refl => exact .refl
  | .single h =>
    unfold RedAffReflTrans
    rw [← Relation.reflGen_transGen]
    exact .single (RedAffTrans.congrArg h)

theorem RedAffReflTrans.congrFun (h_red : RedAffReflTrans f f') : RedAffReflTrans (DCC (f x)) (DCC (f' x)) := by
  unfold RedAffReflTrans at h_red
  rw [← Relation.reflGen_transGen] at h_red
  match heq : h_red with
  | .refl => exact .refl
  | .single h =>
    unfold RedAffReflTrans
    rw [← Relation.reflGen_transGen]
    exact .single (RedAffTrans.congrFun h)

theorem RedAff.conf (h₁ : RedAff A B) (h₂ : RedAff A C) : ∃ D, RedAffReflTrans B D ∧ RedAffReflTrans C D := by
  induction h₁ generalizing C with
  | app =>
    cases h₂ with
    | app => exact ⟨_, .refl, .refl⟩
    | congrFun h =>
      cases h
    | congrArg h =>
      cases h with
      | sigl => exact ⟨_, .single (.congrFun (by assumption)), .single .app⟩
      | sigr => exact ⟨_, .single (.congrArg (by assumption)), .single .app⟩
  | fst =>
    cases h₂ with
    | fst => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h =>
      cases h with
      | sigl => exact ⟨_, .single (by assumption), .single .fst⟩
      | sigr => exact ⟨_, .refl, .single .fst⟩
  | snd =>
    cases h₂ with
    | snd => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h =>
      cases h with
      | sigl => exact ⟨_, .refl, .single .snd⟩
      | sigr => exact ⟨_, .single (by assumption), .single .snd⟩
  | id =>
    cases h₂ with
    | id => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single (by assumption), .single .id⟩
  | flip =>
    cases h₂ with
    | flip => exact ⟨_, .refl, .refl⟩
    | congrFun h =>
      cases h with
      | congrFun h => cases h
      | congrArg => exact ⟨_, .single (.congrArg (by assumption)), .single .flip⟩
    | congrArg => exact ⟨_, .single (.congrFun (.congrArg (by assumption))), .single .flip⟩
  | quot =>
    cases h₂ with
    | quot => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .refl, .single .quot⟩
  | comp =>
    cases h₂ with
    | comp => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single (.congrArg (.congrArg (by assumption))), .single .comp⟩
  | curr =>
    cases h₂ with
    | curr => exact ⟨_, .refl, .refl⟩
    | congrFun h =>
      cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single (.congrArg (.sigl (by assumption))), .single .curr⟩
    | congrArg h => exact ⟨_, .single (.congrArg (.sigr (by assumption))), .single .curr⟩
  | sigl h_r ih =>
    cases h₂ with
    | sigl h_r₂ =>
      have ⟨D, h₁, h₂⟩ := ih h_r₂
      exact ⟨_, .single (.sigl h₁), .single (.sigl (by assumption))⟩
      
    | sigr =>
      sorry

end Expr

/-
Types reduce under SN:

- set of all possible types
- conversion is the only way to get another type

-/
