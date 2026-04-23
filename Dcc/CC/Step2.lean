import Dcc.CC.Ast
import Mathlib.Tactic

namespace Expr

/-

-/

inductive Red : Expr → Expr → Type
  | subst₁    : Red (DCC (Subst(x, Fst(f_β)) env ⟦β⟧(y, z))) (DCC (x env y))
  | subst₂    : Red (DCC (Subst(x, Snd(f_β)) env ⟦β⟧(y, z))) (DCC (x env y z))
  | snd'      : Red (DCC (Snd'(α, β) ⟦γ⟧(x, y))) x
  | quot      : Red (DCC (`(β, x) y)) x
  | id        : Red (DCC (Id(α) x)) x
  | app       : Red (DCC (App(_α, _β, _γ) _env f ⟦β⟧(x, y))) (DCC (f x y))
  | fst       : Red (DCC (Fst(_β) _env ⟦β⟧(a, b))) a
  | snd       : Red (DCC (Snd(_β) _env ⟦β⟧(a, b))) b
  | comp      : Red (DCC ((x ∘ y) z)) (DCC (x (y z)))
  | pair      : Red (DCC (⟦m, α, β, γ⟧⟨f, g⟩ x)) (DCC ⟦`((β ⟦Id(Sort m)⟧(α, x)), (γ ⟦Id(Sort m)⟧(α, x)))⟧((f x), (g x)))
  | curr      : Red (DCC (Λ(α, β, x) y z)) (DCC (x ⟦β⟧(y, z)))
  | sigl      : Red x x' → Red (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x', y))
  | sigr      : Red y y' → Red (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x, y'))
  | congrFun  : Red f f' → Red (DCC (f x)) (DCC (f' x))
  | congrArg  : Red x x' → Red (DCC (f x)) (DCC (f x'))

/-
Affine reduction: the base combinator types do not require any
duplication of arguments in the context. Affine reduction is used
for def-eq, as such.

This is essentially reduction, but without the pair rule.
-/
inductive RedAff : Expr → Expr → Prop
  | subst₁   : RedAff (DCC (Subst(x, Fst(f_β)) env ⟦β⟧(y, z))) (DCC (x env y))
  | subst₂   : RedAff (DCC (Subst(x, Snd(f_β)) env ⟦β⟧(y, z))) (DCC (x env y z))
  | snd'     : RedAff (DCC (Snd'(_δ, _τ) ⟦β⟧(a, b))) b
  | quot     : RedAff (DCC (`(β, x) y)) x
  | id       : RedAff (DCC (Id(α) x)) x
  | app      : RedAff (DCC (App(_α, _β, _γ) _env f ⟦β⟧(x, y))) (DCC (f x y))
  | fst      : RedAff (DCC (Fst(_α) _env ⟦β⟧(a, b))) a
  | snd      : RedAff (DCC (Snd(_α) _env ⟦β⟧(a, b))) b
  | comp     : RedAff (DCC ((x ∘ y) z)) (DCC (x (y z)))
  | curr     : RedAff (DCC (Λ(α, β, x) y z)) (DCC (x ⟦β⟧(y, z)))
  | sigl     : RedAff x x' → RedAff (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x', y))
  | sigr     : RedAff y y' → RedAff (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x, y'))
  | congrFun : RedAff f f' → RedAff (DCC (f x)) (DCC (f' x))
  | congrArg : RedAff x x' → RedAff (DCC (f x)) (DCC (f x'))

inductive Size : Expr → ℕ → Prop
  | tintro : Size (DCC ∗) 0
  | top    : Size (DCC ⊤) 0
  | bot    : Size (DCC ⊥) 0
  | subst  : Size x m → Size y n → Size (DCC Subst(x, y)) (m + n).succ
  | sig    : Size (DCC Σ(_n)) 0
  | coup   : Size x m → Size y n → Size (DCC ⟦β⟧(x, y)) (m + n)
  | sort   : Size (DCC Sort m) 0
  | pi     : Size (DCC Π(α, β)) 0
  | quot   : Size x m → Size (DCC `(β, x)) m.succ
  | id     : Size (DCC Id(α)) 1
  | fst    : Size (DCC Fst(_α)) 1
  | snd'   : Size (DCC Snd'(δ, β)) 1
  | snd    : Size (DCC Snd(_α)) 1
  | appl   : Size (DCC App(_α, β, _γ)) 1
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
  | DCC Σ(_n) => ⟨_, ⟨.sig⟩⟩
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
  | DCC Π(_α, _β) =>
    ⟨_, ⟨.pi⟩⟩
  | DCC App(_α, _β, _γ) => ⟨_, ⟨.appl⟩⟩
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
  | pi | tintro | bot | top | appl | snd' | id | snd | fst | sig | sort => rfl
  | comp _ _ ih₁ ih₂ | coup _ _ ih₁ ih₂ => rw [size, ih₁, ih₂]
  | quot _ ih | curr _ ih => rw [size, ih]
  | subst _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ => rw [size, ih₁, ih₂]

instance instSizeOf : SizeOf Expr := ⟨fun e => e.size.fst⟩

def RedAffTrans     := Relation.TransGen RedAff
def RedAffReflTrans := Relation.ReflTransGen RedAff

@[aesop safe apply, grind ., grind →, simp] theorem RedAff.decreasing (h : RedAff e e') : (size e').fst < (size e).fst := by
  induction h <;> (try grind)

@[aesop safe apply, grind ., grind →, simp] theorem RedAffTrans.decreasing : RedAffTrans e e' → (size e').fst < (size e).fst := by
  intro h
  induction h with
  | single h => exact h.decreasing
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

theorem RedAffTrans.sigr (h_red : RedAffTrans y y') : RedAffTrans (DCC (⟦β⟧(x, y))) (DCC (⟦β⟧(x, y'))) := by
  induction h_red with
  | single h => exact .single (.sigr h)
  | tail h => exact .trans (by assumption) (.single (.sigr (by assumption)))

theorem RedAffTrans.sigl (h_red : RedAffTrans x x') : RedAffTrans (DCC (⟦β⟧(x, y))) (DCC (⟦β⟧(x', y))) := by
  induction h_red with
  | single h => exact .single (.sigl h)
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
  | subst₁ =>
    cases h₂ with
    | subst₁ => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .congrFun (.congrArg (.single h)), .single .subst₁⟩
    | congrArg h => cases h with
      | sigl h => exact ⟨_, .congrArg (.single h), .single .subst₁⟩
      | sigr h => exact ⟨_, .refl, .single .subst₁⟩
  | subst₂ =>
    cases h₂ with
    | subst₂ => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .congrFun (.congrFun (.congrArg (.single h))), .single .subst₂⟩
    | congrArg h => cases h with
      | sigl h => exact ⟨_, .congrFun (.congrArg (.single h)), .single .subst₂⟩
      | sigr h => exact ⟨_, .congrArg (.single h), .single .subst₂⟩
  | quot =>
    cases h₂ with
    | quot => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .refl, .single .quot⟩
  | id =>
    cases h₂ with
    | id => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single h, .single .id⟩
  | sigl h ih =>
    cases h₂ with
    | sigl h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, .sigl h₁, .sigl h₂⟩
    | sigr h =>
      exact ⟨_, .single (.sigr h), .single (.sigl (by assumption))⟩
  | sigr h ih =>
    cases h₂ with
    | sigl h =>
      exact ⟨_, .single (.sigl h), .single (.sigr (by assumption))⟩
    | sigr h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, .sigr h₁, .sigr h₂⟩
  | app =>
    cases h₂ with
    | app => exact ⟨_, .refl, .refl⟩
    | congrFun h =>
      cases h with
      | congrFun h => cases h with
        | congrFun h => cases h
        | congrArg h => exact ⟨_, .refl, .single .app⟩
      | congrArg h => exact ⟨_, .congrFun (.congrFun (.single h)), .single .app⟩
    | congrArg h =>
      cases h with
      | sigl h =>
        exact ⟨_, .congrFun (.congrArg (.single h)), .single .app⟩
      | sigr h =>
        exact ⟨_, .congrArg (.single h), .single .app⟩
  | fst =>
    cases h₂ with
    | fst => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .refl, .single .fst⟩
    | congrArg h =>
      cases h with
      | sigl h =>
        exact ⟨_, .single h, .single .fst⟩
      | sigr h =>
        exact ⟨_, .refl, .single .fst⟩
  | snd =>
    cases h₂ with
    | snd => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .refl, .single .snd⟩
    | congrArg h =>
      cases h with
      | sigl h =>
        exact ⟨_, .refl, .single .snd⟩
      | sigr h =>
        exact ⟨_, .single h, .single .snd⟩
  | snd' =>
    cases h₂ with
    | snd' => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h =>
      cases h with
      | sigl h =>
        exact ⟨_, .refl, .single .snd'⟩
      | sigr h =>
        exact ⟨_, .single h, .single .snd'⟩
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
      | congrArg h => exact ⟨_, .single (.congrArg (.sigl h)), .single .curr⟩
    | congrArg h => exact ⟨_, .single (.congrArg (.sigr (by assumption))), .single .curr⟩
  | congrFun h_r ih =>
    cases h₂
    case subst₁ =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .subst₁, .congrFun (.congrArg (.single h))⟩
    case subst₂ =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .subst₂, .congrFun (.congrFun (.congrArg (.single h)))⟩
    case fst =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .fst, .refl⟩
    case snd =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .snd, .refl⟩
    case snd' | quot | id | comp => cases h_r
    case app =>
      cases h_r with
      | congrFun h => cases h with
        | congrFun h => cases h
        | congrArg h => exact ⟨_, .single .app, .refl⟩
      | congrArg h => exact ⟨_, .single .app, .single (.congrFun (.congrFun h))⟩
    case curr =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .curr, .single (.congrArg (.sigl (by assumption)))⟩
    case congrFun f f' x f'' h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, .congrFun h₁, .congrFun h₂⟩
    case congrArg f f' x x'' h_x =>
      exact ⟨_, .congrArg (.single h_x), .congrFun (.single h_r)⟩
  | congrArg h_r ih =>
    cases h₂ with
    | subst₁ => cases h_r with
      | sigl h => exact ⟨_, .single .subst₁, .congrArg (.single h)⟩
      | sigr h => exact ⟨_, .single .subst₁, .refl⟩
    | subst₂ => cases h_r with
      | sigl h => exact ⟨_, .single .subst₂, .congrFun (.congrArg (.single h))⟩
      | sigr h => exact ⟨_, .single .subst₂, .congrArg (.single h)⟩
    | quot => exact ⟨_, .single .quot, .refl⟩
    | id => exact ⟨_, .single .id, .single h_r⟩
    | app =>
      cases h_r with
      | sigl h => exact ⟨_, .single .app, .congrFun (.congrArg (.single h))⟩
      | sigr h => exact ⟨_, .single .app, .congrArg (.single h)⟩
    | fst =>
      cases h_r with
      | sigl h => exact ⟨_, .single .fst, .single h⟩
      | sigr h =>  exact ⟨_, .single .fst, .refl⟩
    | snd =>
      cases h_r with
      | sigl h => exact ⟨_, .single .snd, .refl⟩
      | sigr h => exact ⟨_, .single .snd, .single h⟩
    | snd' =>
      cases h_r with
      | sigl h => exact ⟨_, .single .snd', .refl⟩
      | sigr h => exact ⟨_, .single .snd', .single h⟩
    | comp  => exact ⟨_, .single .comp, .congrArg (.congrArg (.single (by assumption)))⟩
    | curr  => exact ⟨_, .single .curr, .congrArg (.sigr (.single (by assumption)))⟩
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
  | (DCC (Subst(_x, Fst(_f_β)) _env ⟦_β⟧(_y, _z))) => .some ⟨_, ⟨.subst₁⟩⟩
  | (DCC (Subst(_x, Snd(_f_β)) _env ⟦_β⟧(_y, _z))) => .some ⟨_, ⟨.subst₂⟩⟩
  | (DCC (Snd'(_α, _τ) ⟦_β⟧(_a, b)))               => .some ⟨b, ⟨.snd'⟩⟩
  | (DCC (`(_β, x) _y))                            => .some ⟨x, ⟨.quot⟩⟩
  | (DCC (Id(_α) x))                               => .some ⟨x, ⟨.id⟩⟩
  | (DCC (App(_α, _β, _γ) _env _f ⟦_β₂⟧(_x, _y)))  => .some ⟨_, ⟨.app⟩⟩
  | (DCC (Fst(_α) _env ⟦_γ⟧(a, _b)))               => .some ⟨a, ⟨.fst⟩⟩
  | (DCC (Snd(_α) _env ⟦_γ⟧(_a, b)))               => .some ⟨b, ⟨.snd⟩⟩
  | (DCC ((x ∘ y) z))                              => .some ⟨(DCC (x (y z))), ⟨.comp⟩⟩
  | (DCC (Λ(_α, β, x) y z))                        => .some ⟨(DCC (x ⟦β⟧(y, z))), ⟨.curr⟩⟩
  | DCC ⟦β⟧(x, y) =>
    match x.step?, y.step? with
    | .some ⟨x', ⟨h₁⟩⟩, _ => .some ⟨(DCC ⟦β⟧(x', y)), ⟨.sigl h₁⟩⟩
    | _, .some ⟨y', ⟨h₁⟩⟩ => .some ⟨(DCC ⟦β⟧(x, y')), ⟨.sigr h₁⟩⟩
    | _, _ => .none
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

theorem RedAffTrans.norm_unique (h₁ : RedAffTrans A B) (h_norm : B.IsNormAff) (h₂ : RedAffTrans A C) (h_norm₂ : C.IsNormAff) : B = C :=
  RedAffReflTrans.norm_unique (Relation.TransGen.to_reflTransGen h₁) h_norm (Relation.TransGen.to_reflTransGen h₂) h_norm₂

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

@[simp] theorem IsNormAff.sigl (h : (DCC ⟦β⟧(a, b)).IsNormAff) : a.IsNormAff := fun ⟨_, h₂⟩ =>
  h ⟨_, .sigl h₂⟩

@[simp] theorem IsNormAff.sigr (h : (DCC ⟦β⟧(a, b)).IsNormAff) : b.IsNormAff := fun ⟨_, h₂⟩ =>
  h ⟨_, .sigr h₂⟩

theorem RedAff.complete (h₁ : RedAff A B) (h_norm : B.IsNormAff) : (step? A) = .some ⟨B, ⟨h₁⟩⟩ := by
  unfold step?
  split
  case h_1 | h_2 =>
    cases heq : h₁ with
    | congrFun h => cases h with
      | congrFun h => cases h
      | congrArg h => have h := h_norm.complete; simp [step?] at h
    | congrArg h => cases h with
      | sigl h => have h := h_norm.complete; simp [step?] at h
      | sigr h => have h := h_norm.complete; simp [step?] at h
    | _ => rfl
  case h_4 =>
    cases heq : h₁ with
    | quot => rfl
    | congrFun h => cases h
    | congrArg h => have h := h_norm.complete; simp [step?] at h
  case h_5 =>
    cases heq : h₁ with
    | id =>
      rfl
    | congrFun h => cases h
    | congrArg h => have h := h_norm.complete; simp [step?] at h
  case h_3  =>
    cases heq : h₁
    · rfl
    · rename_i h_r
      have h := h_r.complete h_norm.congrFun
      simp [step?] at h
    · rename_i h_r
      cases h_r
      · rename_i h_r
        have h := h_norm.complete
        simp [step?] at h
      · have h := h_norm.complete
        simp [step?] at h
  case h_6 =>
    cases heq : h₁
    · rfl
    · rename_i h_r
      cases h_r
      · rename_i h; cases h
        · rename_i h; cases h
        · have h := h_norm.complete; simp [step?] at h
      · have h := h_norm.complete
        simp [step?] at h
    · rename_i h
      cases h
      · have h := h_norm.complete; simp [step?] at h
      · have h := h_norm.complete; simp [step?] at h
  case h_8 | h_7 =>
    cases heq : h₁
    · rfl
    · rename_i h_r
      cases h_r
      · rename_i h; cases h
      · have h := h_norm.complete
        simp [step?] at h
    · rename_i h
      cases h
      · have h := h_norm.complete
        simp [step?] at h
      · have h := h_norm.complete
        simp [step?] at h
  case h_9 =>
    cases heq : h₁
    · simp
    · rename_i h
      cases h
    · have h := h_norm.complete
      simp [step?] at h
  case h_10 =>
    cases heq : h₁ with
    | curr => simp
    | congrArg h =>
      have h := h_norm.complete
      simp [step?] at h
    | congrFun h =>
      cases h with
      | congrArg h =>
        have h := h_norm.complete
        simp [step?] at h
      | congrFun h =>
        cases h
  case h_11 =>
    cases h₁ with
    | sigl h => simp [h.complete h_norm.sigl]
    | sigr h => simp [h.complete h_norm.sigr, h_norm.sigl.complete]
  case h_12 =>
    cases h₁ with
    | subst₁ =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl).elim
    | subst₂ =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl).elim
    | congrFun =>
      rename_i h
      simp [h.complete h_norm.congrFun]
    | congrArg =>
      rename_i h
      simp [h.complete h_norm.congrArg, h_norm.congrFun.complete]
    | snd | fst =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ rfl rfl rfl rfl rfl).elim
    | snd'  =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ rfl rfl rfl rfl rfl).elim
    | app =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl).elim
    | quot | id | comp => simp_all
    | curr =>
      rename_i h
      exact (h _ _ _ _ rfl).elim
  case h_13 =>
    simp_all
    cases A with
    | tintro | top | bot | subst | snd' | quot | id | curr | appl | pi | sigma | snd | fst | pair | comp | sort => cases h₁
    | app | mk => simp_all

set_option maxHeartbeats 1000000000 in theorem RedAff.complete' (h_red : RedAff A B) : (step? A).isSome := by
  unfold step?
  split
  repeat rfl
  case h_11 =>
    cases heq : h_red with
    | sigl h =>
      rename_i x x' _
      have h := h.complete'
      have heq' : x.step? = .some ⟨(x.step?.get h).fst, (x.step?.get h).snd⟩ := by
        aesop
      rw [heq']
      simp
    | sigr h =>
      rename_i x y y'
      have h := h.complete'
      have heq' : y.step? = .some ⟨(y.step?.get h).fst, (y.step?.get h).snd⟩ := by
        aesop
      if h_maybe : x.step?.isSome then
        have heq'₁ : x.step? = .some ⟨(x.step?.get h_maybe).fst, (x.step?.get h_maybe).snd⟩ := by
          aesop
        rw [heq'₁, heq']
        simp
      else
        simp at h_maybe
        rw [h_maybe, heq']
        simp
  · rename_i e f x _ _ _ _ _ _ _ _ _ _
    cases h_red
    case fst | snd =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ rfl rfl rfl rfl rfl).elim
    case snd' =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ rfl rfl rfl rfl rfl).elim
    case app =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl).elim
    case quot | id | comp =>
      simp_all
    case subst₁ | subst₂ =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl).elim
    case curr =>
      rename_i h
      exact (h _ _ _ _ rfl).elim
    case congrFun =>
      split
      · rfl
      · rfl
      · rename_i ih₁ ih₂
        rename_i h_r_f _ _
        have h_some := h_r_f.complete'
        have heq : f.step? = .some ⟨(f.step?.get h_some).fst, (f.step?.get h_some).snd⟩ := by
          simp_all
        exact (ih₁ (f.step?.get h_some).fst (f.step?.get h_some).snd.down heq).elim
    case congrArg =>
      split
      · rfl
      · rfl
      · rename_i ih₁ ih₂
        rename_i h_r_x _ _
        have h_some := h_r_x.complete'
        have heq : x.step? = .some ⟨(x.step?.get h_some).fst, (x.step?.get h_some).snd⟩ := by
          simp_all
        exact (ih₂ (x.step?.get h_some).fst (x.step?.get h_some).snd.down heq).elim
  · cases h_red with
    | subst₂ | subst₁ | snd' | quot | id | sigl | sigr | congrFun | congrArg | curr | app | snd | fst | comp =>
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

def step_star? (e : Expr) : Option Expr :=
  if (reduce e) = e then
    .none
  else reduce e

theorem reduce_sound (heq : reduce A = B) : RedAffReflTrans A B := by
  induction A using instWellFounded.induction generalizing B with
  | h a ih =>
    unfold reduce at heq
    split at heq
    case h_1 h_red h_step_eq =>
      exact Relation.ReflTransGen.trans (.single h_red) (ih _ h_red heq)
    case h_2 => simp_all only [forall_eq']; exact .refl

theorem star_reduce (heq : step_star? A = .some B) : reduce A = B := by
  unfold step_star? at heq
  simp_all

theorem star_no_self (heq : step_star? A = .some B) : A ≠ B := fun h => by
  unfold step_star? at heq
  simp_all

theorem step_star?_sound (heq : step_star? A = .some B) : RedAffTrans A B := by
  have h : Relation.ReflTransGen _ _ _ := reduce_sound (star_reduce heq)
  rw [← Relation.reflGen_transGen] at h
  match h with
  | .refl => have hn := star_no_self heq; simp_all
  | .single h => exact h

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

theorem RedAffTrans.next (h : RedAffTrans A B) : ∃ C, RedAff A C := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

theorem RedAffTrans.complete' (h₁ : RedAffTrans A B) : (step_star? A).isSome := by
  simp [step_star?]
  induction h₁ with
  | single h => exact (reduce_norm · ⟨_, h⟩)
  | tail h => exact fun h => by simp_all

theorem RedAffTrans.complete (h₁ : RedAffTrans A B) (h_norm : IsNormAff B) : (step_star? A) = .some B := by
  have h := RedAffReflTrans.complete h₁.to_reflTransGen h_norm
  simp [step_star?]
  exact ⟨fun h₂ => (((h₂ ▸ h).symm ▸ h_norm) h₁.next), h⟩

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
