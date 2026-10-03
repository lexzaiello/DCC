import Dcc2.Ast
import Mathlib.Tactic

namespace Expr

/-
Λ : (c : (Σ 2 (c : Comb 2), (Γ : Comb.sig 2 c)))
    (x : Comb.dom c)
    (y : Comb.dom ($ c x)) → (Λ Comb.cod ($ c x) y)

congr_arg congruence is done individually for the combinators that need it.
-/

open Dsl in
abbrev Comb.u_dom : Expr := (DCC (, (, 1 (' Comb.u_dom)) (∗ 0)))
open Dsl in
abbrev Comb.u_cod : Expr := (DCC (, (, 1 (' Comb.u_cod)) (∗ 0)))
open Dsl in
abbrev Comb.dom : Expr := (DCC (, (, 1 (' Comb.dom)) (∗ 0)))
open Dsl in
abbrev Comb.cod : Expr := (DCC (, (, 1 (' Comb.cod)) (∗ 0)))
open Dsl in
abbrev Comb.sig : Expr := (DCC (, (, 1 (' Comb.sig)) (∗ 0)))
open Dsl in
abbrev Comb.type : Expr := (DCC (, (, 1 (' Comb.type)) (∗ 0)))

open Dsl in
abbrev Id (u A : Expr) : Expr :=
  DCC (, (, 1 (' Id)) (, u A))

open Dsl in
inductive Red : Expr → Expr → Type
  | id         : Red (DCC ($ #(Id u A) x)) x
  | id_u_dom   : Red (DCC ($ Comb.u_dom #(Id u A))) u
  | id_u_cod   : Red (DCC ($ Comb.u_cod #(Id u A))) u
  | id_dom     : Red (DCC ($ Comb.dom #(Id u A))) A
  | id_cod     : Red (DCC ($ Comb.cod (, #(Id u A) __x))) A
  | id_sig     : Red (DCC ($ Comb.sig (, 1 (' Id)))) (DCC (Σ ($ (, (, 1 (' Sort)) (∗ 0)))))
  | comb_ty    : Red (DCC ($ Comb.type (, (, n f) Γ)))
                     (DCC (Π (Comb.u_dom)
                             (Comb.dom)
                             (Comb.u_cod)
                             (Λ (Comb.cod))
                             (, (, n f) Γ)))
  | parapp     : Red (DCC ($ (, (, (ℕ.succ (ℕ.succ n)) f) Γ) x)) (DCC (, (, (ℕ.succ n) f) (, Γ x)))
  | curr       : Red (DCC (Λ f x y)) (DCC ($ f (, x y)))
  | congr_fun  : Red (DCC ($ f x)) f' → Red (DCC ($ ($ f x) y)) (DCC ($ f' y))
  | congr_fun' : Red (DCC (Λ f x y)) f' → Red (DCC ($ (Λ f x y) z)) (DCC ($ f' z))
deriving Repr

theorem Red.decreasing (h : Red A B) : size B < size A := by
  induction h <;> grind

inductive RedChoiceReflTrans (r : Expr → Expr → Type) [∀ x y, Repr (r x y)] : Expr → Expr → Type
  | refl : RedChoiceReflTrans r A A
  | head : r A B → RedChoiceReflTrans r B C → RedChoiceReflTrans r A C
deriving Repr

def step? (e : Expr) : Option (Σ e', Red e e') :=
  open Dsl in match e with
  | (DCC' ($ (, (, 1 (' Id)) (, _u _A)) _x)) => .some ⟨_, .id⟩
  | (DCC' ($ (, (, 1 (' Comb.u_dom)) (∗ 0)) (, (, 1 (' Id)) (, _u _A)))) => .some ⟨_, .id_u_dom⟩
  | (DCC' ($ (, (, 1 (' Comb.u_cod)) (∗ 0)) (, (, 1 (' Id)) (, _u _A)))) => .some ⟨_, .id_u_cod⟩
  | (DCC' ($ (, (, 1 (' Comb.dom)) (∗ 0)) (, (, 1 (' Id)) (, _u _A)))) => .some ⟨_, .id_dom⟩
  | (DCC' ($ (, (, 1 (' Comb.cod)) (∗ 0)) (, (, (, 1 (' Id)) (, _u _A)) __x))) => .some ⟨_, .id_cod⟩
  | (DCC' ($ (, (, 1 (' Comb.sig)) (∗ 0)) (, 1 (' Id)))) => .some ⟨_, .id_sig⟩
  | (DCC' ($ (, (, 1 (' Comb.type)) (∗ 0)) (, (, _n _f) _Γ)))=> .some ⟨_, .comb_ty⟩
  | (DCC' ($ (, (, (ℕ.succ (ℕ.succ _n)) _f) _Γ) _x)) => .some ⟨_, .parapp⟩
  | (DCC' (Λ _f _x _y)) => .some ⟨_, .curr⟩
  | (DCC' ($ ($ f x) _y)) => do .some ⟨_, .congr_fun (← step? (DCC ($ f x))).snd⟩
  | (DCC' ($ (Λ f x y) _z)) => do .some ⟨_, .congr_fun' (← step? (DCC (Λ f x y))).snd⟩
  | _ => .none

def Red.complete (h : Red A B) : step? A = .some ⟨B, h⟩ := by
  induction h
  any_goals (
    unfold step?
    grind)

@[grind]
def IsNorm (r : Expr → Expr → Type) (A : Expr) := ∀ ⦃B : Expr⦄, r A B → False

def reduce (e : Expr) : Σ' (e' : Expr) (_hrt : RedChoiceReflTrans Red e e'), IsNorm Red e' :=
  match heq : step? e with
  | .some ⟨e', h⟩ =>
    have _h_dec := h.decreasing
    let ⟨_, hrt, hn⟩ := (reduce e')
    ⟨_, .head h hrt, hn⟩
  | .none => ⟨_, .refl, (fun _ h => by simp_all [h.complete])⟩
termination_by e.size

def reduce_complete (hrt : RedChoiceReflTrans Red A B) (hn : IsNorm Red B) : reduce A = ⟨B, hrt, hn⟩ :=
  match B, hrt with
  | _, .refl => by
    unfold reduce
    split
    · exact (hn (by assumption)).elim
    · rfl
  | _, .head hr hrt => by
    have heq := hr.complete
    unfold reduce
    split
    case h_1 heq' =>
      cases heq'.symm.trans heq
      have heq' := reduce_complete hrt hn
      simp_all
      congr!
      any_goals (grind)
      case _ heq_fst =>
        subst heq_fst
        grind
    · grind

open Dsl in
#eval (DCC ($* #(Id (DCC (: 1 Level)) (DCC (Sort 0))) (∗ 0)))
open Dsl in
#eval (reduce (DCC ($* #(Id (DCC (: 1 Level)) (DCC (Sort 0))) (∗ 0)))).1
open Dsl in
#eval (reduce (DCC ($* #(Id (DCC (: 1 Level)) (DCC (Sort 0))) (∗ 0)))).2.1

open Dsl in
#eval (reduce (DCC ($* #(Id (DCC (: 1 Level)) (DCC (Sort 0))) ($* #(Id (DCC (: 1 Level)) (DCC (Sort 0))) (∗ 0))))).1

end Expr
