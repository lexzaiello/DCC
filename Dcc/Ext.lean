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


theorem elim_eq (ht : Judge e (DCC (=(f_α) env x y))) : x = y := by
  match ht with
  | .eq ht ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    
    sorry
  | _ => sorry

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
