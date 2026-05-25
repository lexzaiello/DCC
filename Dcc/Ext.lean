import Dcc.Judge
import Dcc.Relation
import Dcc.Types
--import Dcc.Tactic.Reduce
import Dcc.Aff.Red
import Dcc.Eta.Red

namespace Expr

/-
Reduces (f x)
view (Reduces (f x)) B
=> .pi (Reduces x x')

match B to

-/

namespace Reduces

@[dcc_force_reduce, inline] abbrev red_aff (e : Expr) := (reduce RedAff e).fst
@[dcc_force_reduce, inline] abbrev red_eta (e : Expr) := (reduce RedEta e).fst

/-
if r A B, then reduce A = reduce B

Red A B

need some way to slot RedAff back into reduce
-/

@[dcc_force_reduce, grind =]
theorem reduce_aff_pi : (reduce RedAff (DCC (Π(f_α, f_β) env))).fst = (DCC (Π(f_α, f_β) #((reduce RedAff env).fst))) := by
  induction env using RedAff.instRedRel.wellFounded.induction with
  | h x a =>
    conv =>
      left
      dcc_simp (! ! !)
      rfl
    split
    case h_1 hr heq =>
      cases hr with
      | congrFun h => cases h
      | congrArg h =>
        have h := a _ h
        split at heq
        · contradiction
        · dcc_simp_all (! !)
          have ⟨ha, _⟩ := heq
          cases ha
          rfl
        · contradiction
    case h_2 heq =>
      split at heq
      · contradiction
      · contradiction
      case h_3 =>
        dcc_simp (! !)
        split
        case h_1 ih _ _ hr heq =>
          exact (ih _ hr heq).elim
        · rfl



inductive View : Expr → Expr → Expr → Prop
  | pi        : View
    (DCC (Π(f_α, f_β) env))
    (DCC (Π(f_α, f_β) #(red_aff env)))
    (red_eta (DCC (Π(f_α, f_β) #(red_aff env))))

def view (hR : Reduces A C) : Option ((B : Expr) × PLift (View A B C)) :=
  match A with
  | (DCC (Π(f_α, f_β) env)) =>
    .some ⟨(DCC (Π(f_α, f_β) #(red_aff env))), ⟨by
      have heq := hR.complete
      dcc_simp (! !) at heq
      rw [reduce_aff_pi] at heq
      have mk_heq : C = (red_eta (DCC (Π(f_α, f_β) #(red_aff env)))) := by
        dcc_simp_all (! !)
      rw [mk_heq]
      exact View.pi⟩⟩
  | _ => .none

end Reduces

end Expr

namespace Expr

theorem eq_norm_refl (h_step : RedEta A (DCC (=(f_α) env x y))) (h : IsNorm RedEta (DCC (=(f_α) env x y))) : x = y := by
  cases h_step with
  | pi h =>
    cases h
  | eql => rfl

def head (e : Expr) : Expr :=
  match e with
  | .app f _x => f.head
  | e => e

theorem no_red_pi_aff (h_r : RedAff (DCC (Π(f_α, f_β) env)) (DCC (=(a) b c d))) : False := by
  cases h_r with
  | congrFun h => cases h

theorem no_red_pi_eta (h_r : RedEta (DCC (Π(f_α, f_β) env)) (DCC (=(a) b c d))) : False := by
  cases h_r with
  | pi h => cases h

theorem no_red_coup_aff_trans (h_r : Relation.ReflTransGen RedAff (DCC Coup(β)) (DCC (=(a) b c d))) : False := by
  cases h_r.cases_head with
  | inl h => simp_all
  | inr h =>
    have ⟨C, h₁, h₂⟩ := h
    cases h₁ with
    | coup h =>
      have h_dec := RedAff.instRedRel.decreasing h
      exact no_red_coup_aff_trans h₂
termination_by β.size

theorem no_red_coup_eta_trans (h_r : Relation.ReflTransGen RedEta (DCC Coup(β)) (DCC (=(a) b c d))) : False := by
  cases h_r.cases_head with
  | inl h => simp_all
  | inr h =>
    have ⟨C, h₁, h₂⟩ := h
    cases h₁

theorem no_red_pi_aff_trans (h_r : Relation.ReflTransGen RedAff (DCC (Π(f_α, f_β) env)) (DCC (=(a) b c d))) : False := by
  cases h_r.cases_head with
  | inl h => simp_all
  | inr h =>
    have ⟨C, h₁, h₂⟩ := h
    cases h₁ with
    | congrFun h => cases h
    | congrArg h =>
      rename_i x'
      have h_dec := RedAff.instRedRel.decreasing h
      exact no_red_pi_aff_trans h₂
termination_by env.size

theorem no_red_pi_eta_trans (h_r : Relation.ReflTransGen RedEta (DCC (Π(f_α, f_β) env)) (DCC (=(a) b c d))) : False := by
  let f_β₀ := f_β
  cases h_r.cases_head with
  | inl h => simp_all
  | inr h =>
    have ⟨C, h₁, h₂⟩ := h
    cases heq₁ : h₁ with
    | pi h =>
      cases h with
      | pi_quot h=>
        rename_i p'
        have h_dec := RedEta.instRedRel.decreasing p'
        rename_i x x' β
        have _heq : (β.quot x').eta_size < f_β₀.eta_size := by
          grind
        exact no_red_pi_eta_trans h₂
      | pi' h =>
        have h_dec := RedEta.instRedRel.decreasing h
        exact no_red_pi_eta_trans h₂
termination_by f_β.eta_size

theorem Judge.norm_eta (ht : Judge e τ) : IsNorm RedEta τ := by
  cases ht
  any_goals (exact Reduces.norm_eta (by assumption))
  case tintro | bot | top | sort =>
    intro ⟨_, h⟩
    cases h
  case app => exact Reduced.norm_eta (by assumption)

theorem only_eql_reduces_eq (h : RedEta A (DCC (=(f_α) env x y))) : A = (DCC (Eql(f_α) env x)) := by
  cases h with
  | pi h =>
    cases h
  | _ => rfl

theorem red_aff_pi (h : RedAff (DCC (Π(f_α, f_β) env)) B) : ∃ env', B = (DCC (Π(f_α, f_β) env')) := by
  cases h with
  | congrFun h => cases h
  | congrArg h =>
    rename_i x'
    exact ⟨x', rfl⟩

theorem red_aff_pi' (h : Relation.ReflTransGen RedAff (DCC (Π(f_α, f_β) env)) B) : ∃ env', (B = (DCC (Π(f_α, f_β) env')) ∧ Relation.ReflTransGen RedAff env env') := by
  match h.cases_head with
  | .inl h => exact ⟨_, ⟨h.symm, .refl⟩⟩
  | .inr ⟨C, hr₁, hr⟩ =>
    have ⟨env', heq⟩ := red_aff_pi hr₁
    have h_dec : env'.size < env.size := by
      rw [heq] at hr₁
      cases hr₁ with
      | congrFun h => cases h
      | congrArg h =>
        exact RedAff.instRedRel.decreasing h
    have ⟨env', ⟨heq, hr⟩⟩ := red_aff_pi' (heq ▸ hr)
    exact ⟨env', heq, by
      cases hr₁ with
      | congrFun h => cases h
      | congrArg h =>
        cases heq
        exact .trans (.single h) (by assumption)⟩
termination_by env.size

inductive NfType : Expr → Prop
  | sort  : NfType (DCC Sort m)
  | eql   : NfType (DCC (=(f_α) env x x))
  | fn    : NfType (DCC (Π(f_α, f_β) env))
  | top   : NfType (DCC ⊤)
  | coup  : NfType (DCC Coup(f_β))
  | sigma : NfType (DCC (Σ(f_α, f_β) env))

theorem red_aff_pi_norm
  (h : Relation.ReflTransGen RedAff (DCC (Π(f_α, f_β) env)) B)
  (hn : IsNorm RedAff B) :
    ∃ env', (B = (DCC (Π(f_α, f_β) env'))
      ∧ Relation.ReflTransGen RedAff env env'
      ∧ IsNorm RedAff env') := by
  match h.cases_head with
  | .inl h =>
    exact ⟨env, h.symm, .refl, (h ▸ hn).congrArg⟩
  | .inr ⟨C, h₁, h₂⟩ =>
    cases h₁ with
    | congrFun h => cases h
    | congrArg h =>
      rename_i x'
      have h_dec : x'.size < env.size := RedAff.instRedRel.decreasing h
      have ⟨env', heq, hrt, hn⟩ := red_aff_pi_norm h₂ hn
      exact ⟨env', heq, .trans (.single h) hrt, hn⟩
termination_by env.size

theorem red_eta_pi_norm
  (h : Relation.ReflTransGen RedEta (DCC (Π(f_α, f_β) env)) B)
  (hn : IsNorm RedEta B) :
    ∃ f_β', B = (DCC (Π(f_α, f_β') env)) := by
  match h.cases_head with
  | .inl h => exact ⟨_, h.symm⟩
  | .inr ⟨c, h₁, h₂⟩ =>
    cases h₁ with
    | pi h =>
      cases h with
      | pi_quot hr =>
        rename_i x x' β
        have h_dec : (DCC `(β, x')).eta_size < (DCC `(β, x)).eta_size := by
          have h := RedEta.instRedRel.decreasing hr
          grind
        exact red_eta_pi_norm h₂ hn
      | pi' hr =>
        rename_i β'
        have h_dec : β'.eta_size < f_β.eta_size := by
          exact RedEta.instRedRel.decreasing hr
        exact red_eta_pi_norm h₂ hn
termination_by f_β.eta_size

def NfType.eq_elim (heq : τ = (DCC (=(f_α) env x y))) (is_nf : NfType τ) : x = y := by
  cases heq; cases is_nf; rfl

--theorem IsNorm.coup_

theorem no_step_coup_eta (h : RedEta (DCC Coup(β)) B) : False := by
  cases h

theorem no_step_coup_eta_trans (h : Relation.ReflTransGen RedEta (DCC Coup(β)) B) : (DCC Coup(β)) = B := by
  match h.cases_head with
  | .inl h => exact h
  | .inr ⟨C, h₁, h₂⟩ => cases h₁

theorem Reduces.coup (h : Reduces (DCC Coup(β)) B) : ∃ β', B = (DCC Coup(β')) :=
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ => by
    match hr₁.cases_head with
    | .inl h =>
      cases h
      match hr₂.cases_head with
      | .inl h => exact ⟨_, h.symm⟩
      | .inr ⟨_, h₁, h₂⟩ => cases h₁
    | .inr ⟨C, h₁, h₂⟩ =>
      have h_dec := RedAff.instRedRel.decreasing h₁
      cases h₁ with
      | coup hβ =>
        exact Reduces.coup ⟨h₂, hn₁, hr₂, hn₂⟩
termination_by (DCC Coup(β)).size

@[grind]
def type_size (τ : Expr) : ℕ :=
  match τ with
  | DCC ⊤ | DCC Sort _m => 0
  | DCC (Π(f_α, f_β)) =>
    (type_size f_α) + (type_size f_β)
  | DCC (Π(f_α, f_β) _env) =>
    (type_size f_α) + (type_size f_β)
  | DCC Coup(_f_β) => 1
  | DCC (=(_x, _y)) => 0
  | DCC (f _x) => f.type_size
  | _ => 0

@[grind ., grind →]
theorem RedEta.maintains_type_size (hr : RedEta A B) : type_size B = type_size A := by
  induction A generalizing B
  any_goals (
    focus
    cases hr <;> grind
  )
  case app =>
    cases hr
    any_goals (grind)
    · rename_i h ih
      cases h
      · have h := ih (.pi_quot (by assumption))
        grind
      · have h := ih (.pi' (by assumption))
        grind

theorem RedAff.

def is_canon_type (τ e : Expr) : Prop :=
  match τ with
  | DCC Sort m + 1 => e = DCC Sort m
  | DCC (=(x, y)) => ∃ f_α env, x = y ∧ e = (DCC (refl(f_α) env x))
  | DCC ⊤ => e = DCC ∗
  | DCC Coup(f_β) =>
    ∃ x y t_y, e = DCC ⟦f_β⟧(x, y) ∧ Judge y t_y ∧ Reduces (DCC (f_β x)) t_y
  | DCC (Π(f_α, f_β) env) =>
    ∀ (x : Expr)
      (_h_size₁ : (DCC (f_α env)).type_size < (DCC (Π(f_α, f_β) env)).type_size)
      (_h_size₂ : (DCC (f_β env x)).type_size < (DCC (Π(f_α, f_β) env)).type_size),
      is_canon_type (DCC (f_α env)) x → is_canon_type (DCC (f_β env x)) (DCC (e x))
  | τ =>
    ∀ (τ' : Expr) (hr : Reduced τ τ')
      (h_size₀ : τ.type_size = 0)
      (h_size : τ'.size < τ.size), is_canon_type τ' e → is_canon_type τ e
termination_by τ.type_size

/-def Judge.is_nf (ht : Judge e τ) : NfType τ := by
  cases ht with
  | eql _ hred
  | sigma _ _ hred
  | pair _ _ _ _ _ _ hred
  | sndc _ _ hred | fstc _ _ hred
  | quot _ _ hred | pi _ _ hred | curr _ _ _ _ _ hred | comp _ _ _ hred
  | comp' _ _ _ _ _ hred | id _ hred | refl _ hred | eq _ hred =>
    match hred with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      have ⟨env', heq, hr₁', hn₁'⟩ := red_aff_pi_norm hr₁ hn₁
      cases heq
      have ⟨a, τ_eq⟩ := red_eta_pi_norm hr₂ hn₂
      cases τ_eq
      exact .fn
  | bot | top | sort => exact NfType.sort
  | tintro => exact .top
  | coup _ _ hr =>
    match hr with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      match hr₁.cases_head with
      | .inl h =>
        cases h
        match hr₂.cases_head with
        | .inl h =>
          cases h
          exact .sort
        | .inr ⟨C, h₁, h₂⟩ => cases h₁
      | .inr ⟨C, h₁, h₂⟩ => cases h₁
  | mk h_t_x _ _ _ _ h =>
    rename_i x α y τ₂ _ _ _ _ _ _ _ _ _
    have ⟨β', τ_eq⟩ := h.coup
    cases τ_eq
    exact .coup
  | app h_t_f hr_f h_t_x hr_cod =>
    have h_nf_f := h_t_f.is_nf
    have h_nf_x := h_t_x.is_nf
    cases h_nf_f with
    | fn =>
      
      sorry-/

theorem refl_canon (ht : Judge e (DCC (=(f_α) env x x))) : Reduces e (DCC (refl(f_α) env x)) := by
  cases ht with
  | app _ _ _ hr =>
    
    sorry

inductive IsComb : Expr → Type
  | eq    : IsComb (DCC =(f_α))
  | refl  : IsComb (DCC refl(f_α))
  | eql   : IsComb (DCC Eql(f_α))
  | id    : IsComb (DCC Id(α))
  | comp  : IsComb (DCC (f ∘ g))
  | comp' : IsComb (DCC (f ∘' g))
  | fstc  : IsComb (DCC Fstc(β))
  | sndc  : IsComb (DCC Fstc(β))
  | sigma : IsComb (DCC Σ(f_α, f_β))
  | quot  : IsComb (DCC `(β, x))
  | pair  : IsComb (DCC ⟨f, g⟩)
  | curr  : IsComb (DCC Λ(α, β, x))
  | pi    : IsComb (DCC (Π(f_α, f_β)))

/-
An expression that reduces to an equality.
This only includes equalities that can be introduced by
type formers.
-/
inductive EqlTerm : Expr → Prop
  

/-
A function that, when applied a single argument,
yields some =(f_α) env x y

the output type reduces to =(f_α) env x x
-/
inductive EqlFn : Expr → Prop
  | eql  : EqlFn (DCC (Eql(f_α) env))
  | quot : Reduces x (DCC (
    EqlFn (DCC `(

/-
def Judge.is_nf (ht : Judge e τ) : NfType τ := by
  cases ht with
  | eql _ hred | comp' _ _ _ _ _ hred | comp id _ _ hred | id _ hred | eq _ hred =>
    match hred with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      have ⟨env', heq, hr₁', hn₁'⟩ := red_aff_pi_norm hr₁ hn₁
      cases heq
      have ⟨a, τ_eq⟩ := red_eta_pi_norm hr₂ hn₂
      cases τ_eq
      exact .fn

def Judge.is_nf (ht : Judge e τ) : NfType τ := by
  cases ht with
  | eql _ hred | comp' _ _ _ _ _ hred | comp id _ _ hred | id _ hred | eq _ hred =>
    match hred with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      have ⟨env', heq, hr₁', hn₁'⟩ := red_aff_pi_norm hr₁ hn₁
      cases heq
      have ⟨a, τ_eq⟩ := red_eta_pi_norm hr₂ hn₂
      cases τ_eq
      exact .fn-/
  

/-
If it type-checks, it's either:
- the same equality
- a different equality, rejecting argument,
  but one that was ultimately created with refl
-/

/-
Type normal forms:

- Sort
- =(f_α) env x (y? should leave y or force x?)
- (Π(f_α, f_β) env)
- ⊤
- Coup(f_β)
- Σ(f_α, f_β) env

What can reduce to =(f_α) env x y?

Id(_) (=(f_α) env x y)

Fstc(_) (⟦_⟧((=(f_α) env x y), ...))

What is well-typed at =(f_α) env x y?

  - an app. that's it.

    What kind of app?

    - an app with LHS type:
    Π(f_α, 

How does this help us?

- =(f_α) is only a valid type under an app.
  - it is only valid under something that reduces to refl

Theorem: the only combinator that duplicates its spine is Eql
-/

/-theorem elim_eq (ht : Judge e (DCC (=(f_α) env x y))) : x = y := by
  have h := ht.norm_eta
  induction e with
  | refl =>
    cases ht with
    | refl _ hr =>
      match hr with
      | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
        have ⟨env', heq, hrt⟩ := red_aff_pi' hr₁
        cases heq
        exact (no_red_pi_eta_trans hr₂).elim
  | app =>
    cases ht with
    | app _ _ _ hr =>
      match hr with
      | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
        cases hr₂ with
        | refl =>
          
          sorry
        | tail hrt h =>
          have h := only_eql_reduces_eq h
          cases h; cases h; rfl

theorem elim_eq (ht : Judge e (DCC (=(f_α) env x y))) : x = y := by
  have h := ht.norm_eta
  cases ht with
  | eql _ h
  | sigma _ _ h
  | pair _ _ _ _ _ _ h
  | sndc _ _ h | fstc _ _ h
  | quot _ _ h | pi _ _ h | curr _ _ _ _ _ h | comp _ _ _ h
  | comp' _ _ _ _ _ h | id _ h | refl _ h | eq _ h =>
    match h with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      cases hr₂ with
      | refl => exact (no_red_pi_aff_trans hr₁).elim
      | tail a b => exact eq_norm_refl b hn₂
  | mk _ _ _ _ _ h =>
    match h with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      cases hr₂ with
      | refl =>
        exact (no_red_coup_aff_trans hr₁).elim
      | tail a b =>
        exact eq_norm_refl b hn₂
  | coup _ _ h =>
    match h with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      unfold Coup.type at *
      match hr₁.cases_head with
      | .inl a =>
        simp_all
        match hr₂.cases_head with
        | .inl a => simp_all
        | .inr ⟨_, h, _⟩ => cases a ▸ h
  | app h_t_f h_r_α h_t_x h =>
    have hn_a := h_t_f.norm_eta
    have hn_b := h_t_x.norm_eta
    match h with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      cases heq : hr₂ with
      | refl =>
        simp_all
        
        sorry
      | tail _ hr => exact eq_norm_refl hr hn₂
      /-cases hr₁.cases_head with
      | inl a =>
        simp_all
        match hr₂.cases_head with
        | .inl a =>
          cases a; cases a
          rename_i h _ _
          exact eq_norm_refl (by sorry) hn₂
        | .inr ⟨_, h, h_red_other⟩ =>
          cases a ▸ h
          cases h_red_other.cases_head with
          | inl h =>
            cases h; rfl
          | inr h =>
            have ⟨c, h₁, h₂⟩ := h
            rename_i h_eta
            have h := h_eta.norm_aff (by assumption)
            cases h₁
      | inr h =>
        have ⟨c, h₁, h₂⟩ := h
        cases h₁ with
        | curr =>
          
          sorry
        | congrFun h =>
          sorry
        | congrArg h =>
          sorry-/

open Reduces in theorem reflect (ht : Judge e (DCC (=(f_α) env x y))) : x = y := by
  cases ht with
  | eq ht hr =>
    have h := hr.complete
    dcc_simp (! !) at h
    rw [reduce_aff_pi] at h
  | refl ht hr =>
    let heq := hr.complete
    sorry
  | _ => sorry-/

end Expr

/-
Need full reducer

reduce A = B

We need IsNorm for this.

but for this we need a proof of reduce A = B.
-/
