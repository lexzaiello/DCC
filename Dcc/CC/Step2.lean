import Dcc.CC.Ast
import Mathlib.Tactic

namespace Expr

inductive Red : Expr → Expr → Type
  | app      : Red (DCC (App(_n, _δ, _τ) ⟦α, β⟧(f, x))) (DCC (f x))
  | fst      : Red (DCC (Fst(_δ, _τ) ⟦α, β⟧(a, b))) a
  | snd      : Red (DCC (Snd(_δ, _τ) ⟦α, β⟧(a, b))) b
  | snd'     : Red (DCC (Snd'(_δ, _τ) ⟦α, β⟧(a, b))) b
  | flip     : Red (DCC (Flip(e) x y)) (DCC (e y x))
  | id       : Red (DCC (Id(_α) x)) x
  | quot     : Red (DCC (`(_α, _β, x) y)) x
  | comp     : Red (DCC ((⟦α, β, γ⟧∘ x y) z)) (DCC (x (y z)))
  | comp'    : Red (DCC ((x ∘' y) z)) (DCC (x (y z)))
  | pair     : Red (DCC (⟦α, β⟧⟨f, g⟩ x)) (DCC ⟦α, β⟧((f x), (g x)))
  | curr     : Red (DCC (Λ(α, x) y z)) (DCC (x ⟦α, Id(α)⟧(y, z)))
  | curr'    : Red (DCC (Λ'(α, β, x) y z)) (DCC (x ⟦α, β⟧(y, z)))
  | congrFun : Red f f' → Red (DCC (f x)) (DCC (f' x))
  | congrArg : Red x x' → Red (DCC (f x)) (DCC (f x'))

/-
Affine reduction: the base combinator types do not require any
duplication of arguments in the context. Affine reduction is used
for def-eq, as such.

This is essentially reduction, but without the pair rule.
-/
inductive RedAff : Expr → Expr → Prop
  | app      : RedAff (DCC (App(_n, _δ, _τ) ⟦α, β⟧(f, x))) (DCC (f x))
  | fst      : RedAff (DCC (Fst(_δ, _τ) ⟦α, β⟧(a, b))) a
  | snd      : RedAff (DCC (Snd(_δ, _τ) ⟦α, β⟧(a, b))) b
  | snd'     : RedAff (DCC (Snd'(_δ, _τ) ⟦α, β⟧(a, b))) b
  | flip     : RedAff (DCC (Flip(e) x y)) (DCC (e y x))
  | id       : RedAff (DCC (Id(_α) x)) x
  | quot     : RedAff (DCC (`(_α, _β, x) y)) x
  | comp     : RedAff (DCC ((⟦α, β, γ⟧∘ x y) z)) (DCC (x (y z)))
  | comp'    : RedAff (DCC ((x ∘' y) z)) (DCC (x (y z)))
  | curr     : RedAff (DCC (Λ(α, x) y z)) (DCC (x ⟦α, Id(α)⟧(y, z)))
  | curr'    : RedAff (DCC (Λ'(α, β, x) y z)) (DCC (x ⟦α, β⟧(y, z)))
  | congrFun : RedAff f f' → RedAff (DCC (f x)) (DCC (f' x))
  | congrArg : RedAff x x' → RedAff (DCC (f x)) (DCC (f x'))

inductive Size : Expr → ℕ → Prop
  | sig    : Size (DCC Σ(_m, _n)) 0
  | coup   : Size (DCC ⟦α, β⟧(,)) 0
  | pi     : Size (DCC Π(_m, _n)) 0
  | sort   : Size (DCC Sort m) 0
  | id     : Size (DCC Id(α)) 1
  | comp   : Size (DCC ⟦α, β, γ⟧∘) 1
  | fst    : Size (DCC Fst(α, β)) 1
  | snd    : Size (DCC Snd(α, β)) 1
  | snd'   : Size (DCC Snd'(α, β)) 1
  | appl   : Size (DCC App(_n, α, β)) 1
  | flip   : Size e m → Size (DCC Flip(e)) m.succ
  | quot   : Size x m → Size (DCC `(α, β, x)) m.succ
  | comp'  : Size f m → Size g n → Size (DCC (f ∘' g)) (m + n).succ
  | pair   : Size f m → Size g n → Size (DCC ⟦α, β⟧⟨f, g⟩) (m + n).succ
  | curr   : Size x m → Size (DCC Λ(α, x)) m.succ
  | curr'  : Size x m → Size (DCC Λ'(α, β, x)) m.succ
  | app    : Size f m → Size x n → Size (DCC (f x)) (m + n)

def size (e : Expr) : ((n : ℕ) × (PLift (Size e n))) :=
  match e with
  | DCC Sort _m => ⟨_, ⟨.sort⟩⟩
  | DCC Σ(_m, _n) => ⟨_, ⟨.sig⟩⟩
  | DCC Id(_α) => ⟨_, ⟨.id⟩⟩
  | DCC ⟦_α, _β⟧(,) => ⟨_, ⟨.coup⟩⟩
  | DCC Fst(_α, _β) => ⟨_, ⟨.fst⟩⟩
  | DCC Snd(_α, _β) => ⟨_, ⟨.snd⟩⟩
  | DCC Snd'(_α, _β) => ⟨_, ⟨.snd'⟩⟩
  | DCC Π(_m, _n) => ⟨_, ⟨.pi⟩⟩
  | DCC App(_n, _α, _β) => ⟨_, ⟨.appl⟩⟩
  | DCC (⟦_α, _β, _γ⟧∘) => ⟨_, ⟨.comp⟩⟩
  | DCC Flip(e) =>
    let ⟨_m, ⟨h₁⟩⟩ := e.size
    ⟨_, ⟨.flip h₁⟩⟩
  | DCC `(_α, _β, x) =>
    let ⟨_, ⟨h₁⟩⟩ := x.size
    ⟨_, ⟨.quot h₁⟩⟩
  | DCC (f ∘' g) =>
    let ⟨m, ⟨h₁⟩⟩ := f.size
    let ⟨n, ⟨h₂⟩⟩ := g.size
    ⟨(m + n).succ, ⟨.comp' h₁ h₂⟩⟩
    | DCC ⟦_α, _β⟧⟨a, b⟩ =>
    let ⟨_o, ⟨h₁⟩⟩ := a.size
    let ⟨_p, ⟨h₂⟩⟩ := b.size
    ⟨_, ⟨.pair h₁ h₂⟩⟩
  | DCC Λ(_α, x) =>
    let ⟨_n, ⟨h₁⟩⟩ := x.size
    ⟨_, ⟨.curr h₁⟩⟩
  | DCC Λ'(_α, _β, x) =>
    let ⟨_o, ⟨h₁⟩⟩ := x.size
    ⟨_, ⟨.curr' h₁⟩⟩
  | DCC (f x) =>
    let ⟨m, ⟨h₁⟩⟩ := f.size
    let ⟨n, ⟨h₂⟩⟩ := x.size
    ⟨(m + n), ⟨.app h₁ h₂⟩⟩

theorem Size.sound (_h : Expr.size e = ⟨n, ⟨h⟩⟩) : Size e n := h

theorem Size.complete (h : Size e n) : size e = ⟨n, .up h⟩ := by
  induction h with
  | appl | coup | id | snd' | snd | fst | comp | pi | sig | sort => rfl
  | quot _ ih | curr' _ ih | curr _ ih | flip _ ih => rw [size, ih]
  | app _ _ ih₁ ih₂ | comp' _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ => rw [size, ih₁, ih₂]

instance instSizeOf : SizeOf Expr := ⟨fun e => e.size.fst⟩

def RedAffTrans     := Relation.TransGen RedAff
def RedAffReflTrans := Relation.ReflTransGen RedAff

theorem RedAff.decreasing (h : RedAff e e') : (size e').fst < (size e).fst := by
  induction h <;> (simp [size]; try grind)

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
termination_by e.size.fst

def sn_trans (e : Expr) : Acc (fun b a => RedAffTrans a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing
  exact e'.sn_trans)
termination_by e.size.fst

instance instWellFounded : WellFounded (fun a b => RedAff b a) := ⟨sn⟩

instance instWellFoundedTrans : WellFounded (fun a b => RedAffTrans b a) := ⟨sn_trans⟩

instance instWellFoundedRel : WellFoundedRelation Expr := ⟨fun a b => RedAff b a, instWellFounded⟩

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

theorem RedAff.sigl (h_red : RedAff f f') : RedAff (DCC (⟦α, β⟧(f, x))) (DCC (⟦α, β⟧(f', x))) :=
  .congrFun (.congrArg h_red)

theorem RedAff.sigr (h_red : RedAff x x') : RedAff (DCC (⟦α, β⟧(f, x))) (DCC (⟦α, β⟧(f, x'))) :=
  .congrArg h_red

theorem RedAffTrans.sigr (h_red : RedAffTrans x x') : RedAffTrans (DCC (⟦α, β⟧(f, x))) (DCC (⟦α, β⟧(f, x'))) := by
  induction h_red with
  | single h => exact .single (.congrArg h)
  | tail h => exact .trans (by assumption) (.single (.congrArg (by assumption)))

theorem RedAffTrans.sigl (h_red : RedAffTrans f f') : RedAffTrans (DCC (⟦α, β⟧(f, x))) (DCC (⟦α, β⟧(f', x))) := by
  induction h_red with
  | single h => exact .single (.congrFun (.congrArg (by assumption)))
  | tail h => exact .trans (by assumption) (.single (.congrFun (.congrArg (by assumption))))

theorem RedAffReflTrans.sigr (h_red : RedAffReflTrans x x') : RedAffReflTrans (DCC (⟦α, β⟧(f, x))) (DCC (⟦α, β⟧(f, x'))) := by
  unfold RedAffReflTrans at h_red
  rw [← Relation.reflGen_transGen] at h_red
  match heq : h_red with
  | .refl => exact .refl
  | .single h =>
    unfold RedAffReflTrans
    rw [← Relation.reflGen_transGen]
    exact .single (RedAffTrans.sigr h)

theorem RedAffReflTrans.sigl (h_red : RedAffReflTrans f f') : RedAffReflTrans (DCC (⟦α, β⟧(f, x))) (DCC (⟦α, β⟧(f', x))) := by
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
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h =>
          exact ⟨_, .single (.congrFun h), .single .app⟩
      | congrArg => exact ⟨_, .single (.congrArg (by assumption)), .single .app⟩
  | fst =>
    cases h₂ with
    | fst => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h =>
      cases h with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h =>
          exact ⟨_, .single h, .single .fst⟩
      | congrArg => exact ⟨_, .refl, .single .fst⟩
  | snd =>
    cases h₂ with
    | snd => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h =>
      cases h with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h => exact ⟨_, .refl, .single .snd⟩
      | congrArg h => exact ⟨_, .single h, .single .snd⟩
  | snd' =>
    cases h₂ with
    | snd' => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h =>
      cases h with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h => exact ⟨_, .refl, .single .snd'⟩
      | congrArg h => exact ⟨_, .single h, .single .snd'⟩
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
    | congrFun h =>
      cases h with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h => exact ⟨_, .single (.congrFun h), .single .comp⟩
      | congrArg h => exact ⟨_, .single (.congrArg (.congrFun h)), .single .comp⟩
    | congrArg h => exact ⟨_, .single (.congrArg (.congrArg (by assumption))), .single .comp⟩
  | comp' =>
    cases h₂ with
    | comp' => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single (.congrArg (.congrArg (by assumption))), .single .comp'⟩
  | curr =>
    cases h₂ with
    | curr => exact ⟨_, .refl, .refl⟩
    | congrFun h =>
      cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single (.congrArg (.sigl (by assumption))), .single .curr⟩
    | congrArg h => exact ⟨_, .single (.congrArg (.sigr (by assumption))), .single .curr⟩
  | curr' =>
    cases h₂ with
    | curr' => exact ⟨_, .refl, .refl⟩
    | congrFun h =>
      cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single (.congrArg (.sigl (by assumption))), .single .curr'⟩
    | congrArg h => exact ⟨_, .single (.congrArg (.sigr (by assumption))), .single .curr'⟩
  | congrFun h_r ih =>
    cases h₂
    case comp' | quot | id | app | fst | snd | snd' => cases h_r
    case flip =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .flip, .single (.congrArg h)⟩
    case comp =>
      cases h_r with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h => exact ⟨_, .single .comp, .congrFun (.single h)⟩
      | congrArg h => exact ⟨_, .single .comp, .congrArg (.congrFun (.single h))⟩
    case curr =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .curr, .single (.congrArg (.sigl (by assumption)))⟩
    case curr' =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .curr', .single (.congrArg (.sigl (by assumption)))⟩
    case congrFun f f' x f'' h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, .congrFun h₁, .congrFun h₂⟩
    case congrArg f f' x x'' h_x =>
      exact ⟨_, .congrArg (.single h_x), .congrFun (.single h_r)⟩
  | congrArg h_r ih =>
    cases h₂ with
    | app =>
      cases h_r with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h =>
          exact ⟨_, .single .app, .congrFun (.single h)⟩
      | congrArg h =>
        · exact ⟨_, .single .app, .congrArg (.single (by assumption))⟩
    | fst =>
      cases h_r with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h => exact ⟨_, .single .fst, .single h⟩
      | congrArg h => exact ⟨_, .single .fst, .refl⟩
    | snd =>
      cases h_r with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h => exact ⟨_, .single .snd, .refl⟩
      | congrArg h => exact ⟨_, .single .snd, .single h⟩
    | snd' =>
      cases h_r with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h => exact ⟨_, .single .snd', .refl⟩
      | congrArg h => exact ⟨_, .single .snd', .single h⟩
    | id => exact ⟨_, .single .id, .single (by assumption)⟩
    | flip  => exact ⟨_, .single .flip, .single (.congrFun (.congrArg (by assumption)))⟩
    | quot  => exact ⟨_, .single .quot, .refl⟩
    | comp  => exact ⟨_, .single .comp, .congrArg (.congrArg (.single (by assumption)))⟩
    | comp' => exact ⟨_, .single .comp', .congrArg (.congrArg (.single (by assumption)))⟩
    | curr  => exact ⟨_, .single .curr, .congrArg (.sigr (.single (by assumption)))⟩
    | curr' => exact ⟨_, .single .curr', .congrArg (.sigr (.single (by assumption)))⟩
    | congrFun => exact ⟨_, .congrFun (.single (by assumption)), .congrArg (.single (by assumption))⟩
    | congrArg h =>
      have ⟨D, h₁, h₂⟩ := ih h
      exact ⟨_, .congrArg h₁, .congrArg h₂⟩

theorem RedAffReflTrans.conf (h₁ : RedAffReflTrans A B) (h₂ : RedAffReflTrans A C) : ∃ D, RedAffReflTrans B D ∧ RedAffReflTrans C D := by
  induction A using instWellFounded.induction generalizing B C with
  | h _ ih =>
    match h₁.cases_head, h₂.cases_head with
    | .inr ⟨_, hra, hrc⟩, .inr ⟨_, hra', hrc'⟩ =>
      have ⟨_, c₁', c₂'⟩ := hra.conf hra'
      have ⟨_, hrB, hrB'⟩ := ih _ hra hrc c₁'
      have ⟨_, hrC, hrC'⟩ := ih _ hra' hrc' c₂'
      have ⟨_, h₁, h₂⟩ := ih _ hra (c₁'.trans hrB') (c₁'.trans hrC')
      exact ⟨_, .trans hrB h₁, .trans hrC h₂⟩
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
  | (DCC (App(_n, _δ, _τ) ⟦_α, _β⟧(f, x)))  => .some ⟨(DCC (f x)), ⟨.app⟩⟩
  | (DCC (Fst(_δ, _τ) ⟦_α, _β⟧(a, _b)))     => .some ⟨a, ⟨.fst⟩⟩
  | (DCC (Snd(_δ, _τ) ⟦_α, _β⟧(_a, b)))     => .some ⟨b, ⟨.snd⟩⟩
  | (DCC (Snd'(_δ, _τ) ⟦_α, _β⟧(_a, b)))    => .some ⟨b, ⟨.snd'⟩⟩
  | (DCC (Flip(e) x y))                     => .some ⟨(DCC (e y x)), ⟨.flip⟩⟩
  | (DCC (Id(_α) x))                        => .some ⟨x, ⟨.id⟩⟩
  | (DCC (`(_α, _β, x) _y))                 => .some ⟨x, ⟨.quot⟩⟩
  | (DCC ((⟦_α, _β, _γ⟧∘ x y) z))           => .some ⟨(DCC (x (y z))), ⟨.comp⟩⟩
  | (DCC ((x ∘' y) z))                      => .some ⟨(DCC (x (y z))), ⟨.comp'⟩⟩
  | (DCC (Λ(α, x) y z))                     => .some ⟨(DCC (x ⟦α, Id(α)⟧(y, z))), ⟨.curr⟩⟩
  | (DCC (Λ'(α, β, x) y z))                 => .some ⟨(DCC (x ⟦α, β⟧(y, z))), ⟨.curr'⟩⟩
  | DCC (f x) =>
    match f.step?, x.step? with
    | .some ⟨f', ⟨h₁⟩⟩, _ => .some ⟨(DCC (f' x)), ⟨.congrFun h₁⟩⟩
    | _, .some ⟨x', ⟨h₁⟩⟩ => .some ⟨(DCC (f x')), ⟨.congrArg h₁⟩⟩
    | _, _ => .none
  | _ => .none

def IsNormAff (e : Expr) : Prop := ¬ ∃ e', RedAff e e'

/-
TODO: using global confluence, prove uniqueness of normal forms to show completeness of a full beta-reducer
- change Judge types to only use Affine reduction
-/

theorem RedAff.norm_unique (h₁ : RedAff A B) (h_norm : B.IsNormAff) (h₂ : RedAff A C) (h_norm₂ : C.IsNormAff) : B = C := by
  have ⟨D, ha, hb⟩ := h₁.conf h₂
  match ha.cases_head, hb.cases_head with
  | .inl h₁, .inl h₂ =>
    simp_all
  | .inr ⟨c₁, h₁, h₂⟩, _ =>
    exact h_norm.elim ⟨_, h₁⟩
  | _, .inr ⟨c₁, h₁, h₂⟩ =>
    exact h_norm₂.elim ⟨_, h₁⟩

theorem RedAffReflTrans.norm_unique (h₁ : RedAffReflTrans A B) (h_norm : B.IsNormAff) (h₂ : RedAffReflTrans A C) (h_norm₂ : C.IsNormAff) : B = C := by
  have ⟨D, ha, hb⟩ := h₁.conf h₂
  match ha.cases_head, hb.cases_head with
  | .inl h₁, .inl h₂ =>
    simp_all
  | .inr ⟨c₁, h₁, h₂⟩, _ =>
    exact h_norm.elim ⟨_, h₁⟩
  | _, .inr ⟨c₁, h₁, h₂⟩ =>
    exact h_norm₂.elim ⟨_, h₁⟩

@[simp] theorem RedAff.no_refl : ¬ RedAff A A := fun h => by
  have h := h.decreasing
  omega

theorem IsNormAff.complete (h : A.IsNormAff) : (step? A) = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨e', ⟨h₂⟩⟩ heq
  exact (h ⟨_, h₂⟩)

@[simp] theorem IsNormAff.congrFun (h : (DCC (f x)).IsNormAff) : f.IsNormAff := fun ⟨_, h₂⟩ =>
  h ⟨_, .congrFun h₂⟩

@[simp] theorem IsNormAff.congrArg (h : (DCC (f x)).IsNormAff) : x.IsNormAff := fun ⟨_, h₂⟩ =>
  h ⟨_, .congrArg h₂⟩

@[simp] theorem IsNormAff.sigl (h : (DCC ⟦α, β⟧(a, b)).IsNormAff) : a.IsNormAff := fun ⟨_, h₂⟩ =>
  h ⟨_, .sigl h₂⟩

@[simp] theorem IsNormAff.sigr (h : (DCC ⟦α, β⟧(a, b)).IsNormAff) : b.IsNormAff := fun ⟨_, h₂⟩ =>
  h ⟨_, .sigr h₂⟩

theorem RedAff.complete (h₁ : RedAff A B) (h_norm : B.IsNormAff) : (step? A) = .some ⟨B, ⟨h₁⟩⟩ := by
  unfold step?
  split
  case h_4 | h_3 | h_2 | h_1  =>
    cases heq : h₁
    · rfl
    · rename_i h_r
      have h := h_r.complete h_norm.congrFun
      simp [step?] at h
    · rename_i h_r
      cases h_r
      · rename_i h_r
        cases h_r
        · rename_i h; cases h
        · have h := h_norm.complete
          simp [step?] at h
      · have h := h_norm.complete
        simp [step?] at h
  case h_5 =>
    cases heq : h₁
    · simp
    · rename_i h
      cases h
      · rename_i h; cases h
      · have h := h_norm.complete
        simp [step?] at h
    · have h := h_norm.complete
      simp [step?] at h
  case h_7 | h_6 =>
    cases heq : h₁
    · rfl
    · rename_i h; cases h
    · have h := h_norm.complete
      simp [step?] at h
  case h_8 =>
    cases heq : h₁
    · rfl
    · rename_i h
      cases h with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h =>
          have h := h_norm.complete
          simp [step?] at h
      | congrArg h =>
        have h := h_norm.complete
        simp [step?] at h
    · have h := h_norm.complete
      simp [step?] at h
  case h_9 =>
    cases heq : h₁
    · rfl
    · rename_i h; cases h
    · have h := h_norm.complete
      simp [step?] at h
  case h_10 | h_11 =>
    cases heq : h₁
    · rfl
    · rename_i h
      cases h
      · rename_i h
        have h := h.complete
        simp [step?] at h
        have h := h_norm.congrFun.congrFun
        simp_all
      · have h := h_norm.complete
        simp [step?] at h
    · have h := h_norm.complete
      simp [step?] at h
  case h_12 =>
    cases h₁ with
    | congrFun =>
      rename_i h
      simp [h.complete h_norm.congrFun]
    | congrArg =>
      rename_i h
      simp [h.complete h_norm.congrArg, h_norm.congrFun.complete]
    | snd | snd' | fst =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl).elim
    | app =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl).elim
    | comp' | quot | flip | id => simp_all
    | comp =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ rfl rfl rfl rfl rfl).elim
    | curr' =>
      simp_all
      rename_i h
      exact (h _ _ _ _ rfl rfl rfl rfl).elim
    | curr => simp_all
  case h_13 =>
    simp_all
    cases A
    repeat cases h₁
    repeat simp_all

theorem RedAff.complete' (h_red : RedAff A B) : (step? A).isSome := by
  unfold step?
  split
  repeat rfl
  · rename_i e f x _ _ _ _ _ _ _ _ _ _ _
    cases h_red
    case fst | snd | snd' =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl).elim
    case app =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl).elim
    case flip | quot | id | comp' =>
      simp_all
    case comp =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ rfl rfl rfl rfl rfl).elim
    case curr' =>
      simp_all
      rename_i h
      exact (h _ _ _ _ rfl rfl rfl rfl).elim
    case curr => simp_all
    case congrFun =>
      split
      · rfl
      · rfl
      · rename_i ih₁ ih₂
        rename_i _ f₀ _ _ _ _ _ _ _ _ h_r_f _ _
        have h_some := h_r_f.complete'
        have heq : f.step? = .some ⟨(f.step?.get h_some).fst, (f.step?.get h_some).snd⟩ := by
          simp_all
        exact (ih₁ (f.step?.get h_some).fst (f.step?.get h_some).snd.down heq).elim
    case congrArg =>
      split
      · rfl
      · rfl
      · rename_i ih₁ ih₂
        rename_i _ _ x₀ _ _ _ _ _ _ _ h_r_x _ _
        have h_some := h_r_x.complete'
        have heq : x.step? = .some ⟨(x.step?.get h_some).fst, (x.step?.get h_some).snd⟩ := by
          simp_all
        exact (ih₂ (x.step?.get h_some).fst (x.step?.get h_some).snd.down heq).elim
  · cases h_red with
    | congrFun | congrArg | snd' | curr | curr' | app | snd | fst | id | comp' | comp | quot | flip =>
      simp at *

instance : Decidable (IsNormAff A) :=
  if heq : (step? A).isSome then
    let h := (step? A).get heq
    .isFalse (fun _h => by
      let h' := _h.complete
      obtain ⟨fst, snd⟩ := h
      simp_all only [Option.isSome_none, Bool.false_eq_true])
  else .isTrue (fun ⟨_, h⟩ =>
    have h := h.complete'
    by simp_all)

instance : Decidable (RedAff A B ∧ B.IsNormAff) :=
  if h : (step? A).isSome then
    if heq : ((step? A).get h).fst = B then
      if h_norm : IsNormAff ((step? A).get h).fst then
        .isTrue (⟨heq ▸ ((step? A).get h).snd.down, heq ▸ h_norm⟩)
      else
        .isFalse (fun ⟨h_r_a, h_norm⟩ => by
          have h := h_r_a.complete h_norm
          simp_all)
    else
      .isFalse (fun ⟨h_r_a, h_norm⟩ => by
        have heq₂ := h_r_a.complete h_norm
        have heq₃ : A.step? = .some ⟨((step? A).get h).fst, (A.step?.get h).snd⟩ := by
          simp_all
        simp_all)
  else
    .isFalse (fun ⟨h_red, h_norm⟩ =>
      have h := h_red.complete h_norm
      by simp_all)

instance : Decidable (∃ A', RedAff A A') :=
  if h : (step? A).isSome then
    .isTrue ⟨_, ((step? A).get h).snd.down⟩
  else
    .isFalse (fun ⟨A', hred⟩ => by simp [hred.complete'] at *)

def reduce (e : Expr) : Expr :=
  match step? e with
  | .some ⟨e', ⟨h⟩⟩ =>
    -- This hypothesis allows the recursion. Easy to prove.
    have _h_size : e'.size.fst < e.size.fst := h.decreasing
    e'.reduce
  | .none => e

theorem reduce_sound (heq : reduce A = B) : RedAffReflTrans A B := by
  induction A using instWellFounded.induction generalizing B with
  | h a ih =>
    unfold reduce at heq
    split at heq
    case h_1 h_red h_step_eq =>
      exact Relation.ReflTransGen.trans (.single h_red) (ih _ h_red heq)
    case h_2 => simp_all only [forall_eq']; exact .refl

def reduce_diamond (A B : Expr) : Option ((C : Expr) × (PLift (RedAffReflTrans A C ∧ RedAffReflTrans B C))) :=
  if heq : reduce A = reduce B then
    .some ⟨reduce A, ⟨⟨reduce_sound rfl, reduce_sound heq.symm⟩⟩⟩
  else
    .none

theorem IsNormAff.complete_reduce (h : A.IsNormAff) : reduce A = A := by
  unfold reduce
  rw [h.complete]

theorem step?_none : step? A = .none → A.IsNormAff := fun h_step ⟨e', h_red⟩ => by
  have h := h_red.complete'
  simp_all

theorem reduce_norm (h : reduce A = B) : B.IsNormAff := by
  induction A using instWellFounded.induction generalizing B with
  | h a ih =>
    unfold reduce at h
    split at h
    · rename_i hred heq
      have h := ih _ hred rfl
      simp_all
    · rename_i heq
      have h := step?_none heq
      simp_all

theorem reduce_self : reduce A = reduce (reduce A) :=
  (reduce_norm (A := A) rfl).complete_reduce.symm

theorem RedAff.reduce_same (h : RedAff A B) : reduce A = reduce B := by
  apply RedAffReflTrans.norm_unique
  · exact reduce_sound rfl
  · exact reduce_norm rfl
  · exact .trans (.single h) (reduce_sound rfl)
  · exact reduce_norm rfl

theorem RedAffReflTrans.reduce_same (h : RedAffReflTrans A B) : reduce A = reduce B := by
  apply RedAffReflTrans.norm_unique
  · exact reduce_sound rfl
  · exact reduce_norm rfl
  · exact .trans h (reduce_sound rfl)
  · exact reduce_norm rfl

theorem RedAffReflTrans.complete (h₁ : RedAffReflTrans A B) (h_norm : B.IsNormAff) : reduce A = B := by
  match h₁.cases_head with
  | .inl h =>
    simp_all
    exact h_norm.complete_reduce
  | .inr ⟨c, h₁, h₂⟩ =>
    have _h : sizeOf c < sizeOf A := h₁.decreasing
    have h := RedAffReflTrans.complete h₂ h_norm
    rw [h₁.reduce_same, h]
termination_by A.size.fst

instance : Decidable (RedAffReflTrans A B ∧ B.IsNormAff) :=
  if h : reduce A = B then
    .isTrue (⟨reduce_sound h, reduce_norm h⟩)
  else
    .isFalse (fun ⟨h_red, heq⟩ => by simp [h_red.complete heq] at *)

instance : Decidable (∃ C, RedAffReflTrans A C ∧ RedAffReflTrans B C ∧ C.IsNormAff) :=
  if heq : reduce A = reduce B then .isTrue
    ⟨_, reduce_sound rfl, reduce_sound heq.symm, reduce_norm rfl⟩
  else
    .isFalse (fun ⟨C, h₁, h₂, h_norm⟩ => by
      have ha := h₁.complete h_norm
      have hb := h₂.complete h_norm
      simp_all)

end Expr
