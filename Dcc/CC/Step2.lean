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

def sn (e : Expr) : Acc (fun b a => RedAff a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing
  exact e'.sn)
termination_by e

def sn_trans (e : Expr) : Acc (fun b a => RedAffTrans a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing
  exact e'.sn_trans)
termination_by e

instance instWellFounded : WellFounded (fun a b => RedAff b a) := ⟨sn⟩

instance instWellFoundedTrans : WellFounded (fun a b => RedAffTrans b a) := ⟨sn_trans⟩

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

theorem RedAffTrans.sigr (h_red : RedAffTrans x x') : RedAffTrans (DCC (⟦β⟧(f, x))) (DCC (⟦β⟧(f, x'))) := by
  induction h_red with
  | single h => exact .single (.sigr (by assumption))
  | tail h => exact .trans (by assumption) (.single (.sigr (by assumption)))

theorem RedAffTrans.sigl (h_red : RedAffTrans f f') : RedAffTrans (DCC (⟦β⟧(f, x))) (DCC (⟦β⟧(f', x))) := by
  induction h_red with
  | single h => exact .single (.sigl (by assumption))
  | tail h => exact .trans (by assumption) (.single (.sigl (by assumption)))

theorem RedAffReflTrans.sigr (h_red : RedAffReflTrans x x') : RedAffReflTrans (DCC (⟦β⟧(f, x))) (DCC (⟦β⟧(f, x'))) := by
  unfold RedAffReflTrans at h_red
  rw [← Relation.reflGen_transGen] at h_red
  match heq : h_red with
  | .refl => exact .refl
  | .single h =>
    unfold RedAffReflTrans
    rw [← Relation.reflGen_transGen]
    exact .single (RedAffTrans.sigr h)

theorem RedAffReflTrans.sigl (h_red : RedAffReflTrans f f') : RedAffReflTrans (DCC (⟦β⟧(f, x))) (DCC (⟦β⟧(f', x))) := by
  unfold RedAffReflTrans at h_red
  rw [← Relation.reflGen_transGen] at h_red
  match heq : h_red with
  | .refl => exact .refl
  | .single h =>
    unfold RedAffReflTrans
    rw [← Relation.reflGen_transGen]
    exact .single (RedAffTrans.sigl h)

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
    cases heq₂ : h₂ with
    | sigl h_r₂ =>
      have ⟨D, h₁, h₂⟩ := ih h_r₂
      exact ⟨_, .sigl h₁, .sigl (by assumption)⟩
    | sigr h_r₂ =>
      exact ⟨_, .sigr (.single (by assumption)), .sigl (.single (by assumption))⟩
  | sigr h_r ih =>
    cases heq₂ : h₂ with
    | sigr h_r₂ =>
      have ⟨D, h₁, h₂⟩ := ih h_r₂
      exact ⟨_, .sigr h₁, .sigr (by assumption)⟩
    | sigl h_r₂ =>
      exact ⟨_, .sigl (.single (by assumption)), .sigr (.single (by assumption))⟩
  | congrFun h_r ih =>
    cases h₂
    repeat cases h_r
    · rename_i h; cases h
    · exact ⟨_, .single .flip, .single (.congrArg (by assumption))⟩
    repeat cases h_r
    · rename_i h; cases h
    · exact ⟨_, .single .curr, .single (.congrArg (.sigl (by assumption)))⟩
    case congrFun f f' x f'' h =>
      have ⟨D, h₁, h₂⟩ := ih h
      exact ⟨_, .congrFun h₁, .congrFun h₂⟩
    case congrArg f f' x x'' h_x =>
      exact ⟨_, .congrArg (.single (by assumption)), .congrFun (.single (by assumption))⟩
  | congrArg h_r ih =>
    cases h₂ with
    | app =>
      cases h_r
      · exact ⟨_, .single .app, .congrFun (.single (by assumption))⟩
      · exact ⟨_, .single .app, .congrArg (.single (by assumption))⟩
    | fst =>
      cases h_r
      · rename_i h
        exact ⟨_, .single .fst, .single h⟩
      · exact ⟨_, .single .fst, .refl⟩
    | snd =>
      cases h_r
      · exact ⟨_, .single .snd, .refl⟩
      · rename_i h
        exact ⟨_, .single .snd, .single h⟩
    | id => exact ⟨_, .single .id, .single (by assumption)⟩
    | flip => exact ⟨_, .single .flip, .single (.congrFun (.congrArg (by assumption)))⟩
    | quot => exact ⟨_, .single .quot, .refl⟩
    | comp => exact ⟨_, .single .comp, .congrArg (.congrArg (.single (by assumption)))⟩
    | curr => exact ⟨_, .single .curr, .congrArg (.sigr (.single (by assumption)))⟩
    | congrFun => exact ⟨_, .congrFun (.single (by assumption)), .congrArg (.single (by assumption))⟩
    | congrArg h =>
      have ⟨D, h₁, h₂⟩ := ih h
      exact ⟨_, .congrArg h₁, .congrArg h₂⟩

theorem RedAffReflTrans.conf (h₁ : RedAffReflTrans A B) (h₂ : RedAffReflTrans A C) : ∃ D, RedAffReflTrans B D ∧ RedAffReflTrans C D := by
  have h := A.sn
  induction h generalizing B C with
  | intro _ ih₁ ih₂ =>
    match h₁.cases_head, h₂.cases_head with
    | .inr ⟨c₁, ha, hrefl₁⟩, .inr ⟨c₂, hb, hrefl₂⟩ =>
      have ⟨D₃, h₅, h₆⟩ := ha.conf hb
      have ⟨D₄, hB_D₄, hD₃_D₄⟩ := ih₂ c₁ ha hrefl₁ h₅
      have hc₂_D₄ : c₂.RedAffReflTrans D₄ := .trans h₆ hD₃_D₄
      have ⟨D₅, hC_D₅, hD₄_D₅⟩ := ih₂ c₂ hb hrefl₂ hc₂_D₄
      have hB_D₅ : B.RedAffReflTrans D₅ := .trans hB_D₄ hD₄_D₅
      exact ⟨D₅, hB_D₅, hC_D₅⟩
    | .inl heq₁, .inl heq₂ =>
      rw [← heq₁, ← heq₂]
      exact ⟨_, .refl, .refl⟩
    | .inl heq₁, .inr _ =>
      rw [← heq₁]
      exact ⟨_, h₂, .refl⟩
    | .inr _, .inl heq₁ =>
      rw [← heq₁]
      exact ⟨_, .refl, h₁⟩

def step? (e : Expr) : Option ((e' : Expr) × (PLift (RedAff e e'))) :=
  match e with
  | (DCC (App(_δ, _τ) ⟦_β⟧(f, x)))  => .some ⟨(DCC (f x)), ⟨.app⟩⟩
  | (DCC (Fst(_δ, _τ) ⟦_β⟧(a, _b))) => .some ⟨a, ⟨.fst⟩⟩
  | (DCC (Snd(_δ, _τ) ⟦_β⟧(_a, b))) => .some ⟨b, ⟨.snd⟩⟩
  | (DCC (Flip(e) x y))             => .some ⟨(DCC (e y x)), ⟨.flip⟩⟩
  | (DCC (Id(_α) x))                => .some ⟨x, ⟨.id⟩⟩
  | (DCC (`(_α, _β, x) _y))         => .some ⟨x, ⟨.quot⟩⟩
  | (DCC ((x ∘ y) z))               => .some ⟨(DCC (x (y z))), ⟨.comp⟩⟩
  | (DCC (Λ(β, x) y z))             => .some ⟨(DCC (x ⟦β⟧(y, z))), ⟨.curr⟩⟩
  | (DCC ⟦β⟧(a, b))                 =>
    match a.step?, b.step? with
    | .some ⟨a', ⟨h₁⟩⟩, _ => .some ⟨(DCC ⟦β⟧(a', b)), ⟨.sigl h₁⟩⟩
    | _, .some ⟨b', ⟨h₁⟩⟩ => .some ⟨(DCC ⟦β⟧(a, b')), ⟨.sigr h₁⟩⟩
    | _, _ => .none
  | DCC (f x) =>
    match f.step?, x.step? with
    | .some ⟨f', ⟨h₁⟩⟩, _ => .some ⟨(DCC (f' x)), ⟨.congrFun h₁⟩⟩
    | _, .some ⟨x', ⟨h₁⟩⟩ => .some ⟨(DCC (f x')), ⟨.congrArg h₁⟩⟩
    | _, _ => .none
  | _ => .none

def reduce (e : Expr) : ((e' : Expr) × (PLift (RedAffReflTrans e e'))) :=
  match heq : step? e with
  | .some ⟨e', ⟨h⟩⟩ =>
    -- This hypothesis allows the recursion. Easy to prove.
    have _h_size : e'.size.fst < e.size.fst := h.decreasing
    let ⟨e'', ⟨h⟩⟩ := e'.reduce
    ⟨e'', ⟨.trans (.single (by assumption)) h⟩⟩
  | .none => ⟨e, ⟨.refl⟩⟩

/-
TODO: using global confluence, prove uniqueness of normal forms to show completeness of a full beta-reducer
- change Judge types to only use Affine reduction
-/

end Expr
