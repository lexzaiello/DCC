import Dcc.Judge
import Dcc.Relation
import Dcc.Types
import Dcc.Tactic.Reduce
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
  any_goals (
    exact Reduces.norm_eta (by assumption)
  )
  case tintro | bot | top | sort =>
    intro ⟨_, h⟩
    cases h

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

theorem red_aff_pi' (h : Relation.ReflTransGen RedAff (DCC (Π(f_α, f_β) env)) B) : ∃ env', B = (DCC (Π(f_α, f_β) env')) := by
  match h.cases_head with
  | .inl h => exact ⟨_, h.symm⟩
  | .inr ⟨C, hr₁, hr⟩ =>
    have ⟨env', heq⟩ := red_aff_pi hr₁
    have h_dec : env'.size < env.size := by
      rw [heq] at hr₁
      cases hr₁ with
      | congrFun h => cases h
      | congrArg h =>
        exact RedAff.instRedRel.decreasing h
    exact red_aff_pi' (heq ▸ hr)
termination_by env.size

/-inductive CanReduceEq : Expr → Expr → Prop
  | quot : CanReduceEq (DCC (`(-/

theorem no_reduce_eq_aff (h : RedAff A (DCC (=(f_α) env x y))) : False := by
  cases h
  

theorem elim_eq (ht : Judge e (DCC (=(f_α) env x y))) : x = y := by
  have h := ht.norm_eta
  induction e with
  | refl =>
    cases ht with
    | refl _ hr =>
      match hr with
      | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
        match hr₁.cases_head with
        | .inl h =>
          exact (no_red_pi_eta_trans (h ▸ hr₂)).elim
        | .inr ⟨C, h₁, h₂⟩ =>
          cases h₁ with
          | congrFun h => cases h
          | congrArg h =>
            
            sorry

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
  | _ => sorry

end Expr

/-
Need full reducer

reduce A = B

We need IsNorm for this.

but for this we need a proof of reduce A = B.
-/
