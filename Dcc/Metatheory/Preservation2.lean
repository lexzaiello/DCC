import Dcc.Judge2
import Dcc.Aff.Red
import Dcc.Eta.Reduce
import Dcc.Value

namespace GenericExpr

def CR.{u} {τ_c : Type u} (τ : GenericExpr τ_c) (e : GenericExpr τ_c) : Prop :=
  match τ with
  | DCC? Sort m =>
    match e with
    | DCC? Sort n => m = n + 1
    | _ => False -- TOOD: Coup(β), Π types, etc.
  | DCC? (Π(f_α, f_β) x_α) =>
    
    sorry
termination_by e.size

theorem reduce'_bang : reduce' RedAff (DCC? (!(δ))) = (DCC? (!(#(reduce' RedAff δ)))) := sorry

namespace Reduces₂

instance instCongruent.{u} {τ_c : Type u} [DecidableEq τ_c] : Congruent (Reduces₂ (τ_c := τ_c)) := sorry

theorem invert_congr_fun.{u} {τ_c : Type u} [DecidableEq τ_c] {f x f' : GenericExpr τ_c} (hr : Reduces₂ (DCC? (f x)) (DCC? (f' x))) : Reduces₂ f f' := sorry

end Reduces₂

/-
Some combination of push_head

Reduces₂ A B
Reduces₂ B C

A -> A'
so Reduces₂ A' C

-/

namespace RedEta??

theorem red_sort.{u} {τ_c : Type u} [DecidableEq τ_c] {τ : GenericExpr τ_c} (h : RedEta?? (DCC? (Sort m)) τ) : τ = DCC? Sort m := by sorry

theorem decreasing?.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' : GenericExpr τ_c} (hr : RedEta?? e e') : size e' < size e := by sorry

end RedEta??

namespace RedEta₂

theorem decreasing?.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' : GenericExpr τ_c} (hr : RedEta₂ e e') : size e' < size e := by sorry

theorem reduce_self.{u} {τ_c : Type u} [DecidableEq τ_c] {A B C : GenericExpr τ_c} (hr₁ : RedEta₂ A B) (hr₂ : RedEta₂ B C) : B = C := by sorry

end RedEta₂

namespace Reduces₂

theorem congr_arg.{u} {τ_c : Type u} [DecidableEq τ_c] {x x' f B : GenericExpr τ_c} (hr₁ : Reduces₂ x x') (hr₂ : Reduces₂ (DCC? (f x')) B) : Reduces₂ (DCC? (f x)) B := by sorry

theorem congr_arg'.{u} {τ_c : Type u} [DecidableEq τ_c] {x x' f B : GenericExpr τ_c} (hr₁ : Reduces₂ x x') (hr₂ : Reduces₂ (DCC? (f x)) B) : Reduces₂ (DCC? (f x')) B := by sorry

theorem congr_fun.{u} {τ_c : Type u} [DecidableEq τ_c] {f f' x B : GenericExpr τ_c} (hr₁ : Reduces₂ f f') (hr₂ : Reduces₂ (DCC? (f' x)) B) : Reduces₂ (DCC? (f x)) B := by sorry

theorem pi_transport.{u} {τ_c : Type u} [DecidableEq τ_c] {f_α f_β x_α x_α₂ f_α₂ f_β₂ env e' e'' : GenericExpr τ_c}
  (hr₁ : Reduces₂ (DCC? (Π(f_α, f_β) x_α)) (DCC? (Π(f_α₂, f_β₂) x_α₂)))
  (hr₂ : RedAffReflTrans (DCC? (f_β x_α env)) e') (hr₃ : Reduces₂ (DCC? (f_β₂ x_α₂ env)) e'') : Reduces₂ (DCC? (f_β x_α env)) e'' := by
  sorry

theorem trans.{u} {τ_c : Type u} [DecidableEq τ_c] {A B C : GenericExpr τ_c} (hr₁ : Reduces₂ A B) (hr₂ : Reduces₂ B C) : Reduces₂ A C :=
  match hr₁, hr₂ with
  | ⟨hr₁, hn₁, hr₂⟩, ⟨hr₃, hn₂, hr₄⟩ => by
    have hn  := hr₂.is_norm_aff hn₁
    have heq := hn.unique_refl hr₃
    exact ⟨hr₁, by assumption, (RedEta₂.reduce_self hr₂ (by rw [heq]; exact hr₄)) ▸ hr₂⟩

theorem trans_head.{u} {τ_c : Type u} [DecidableEq τ_c] {A B C A' : GenericExpr τ_c} (hr₁ : Reduces₂ A B) (hr₂ : Reduces₂ B C) (hr₃ : RedAff A A') : Reduces₂ A' C :=
  have h := hr₁.trans hr₂
  match h with
  | ⟨hr₁, hn₁, hr₂⟩ => ⟨hr₁.push_head hn₁ hr₃, hn₁, hr₂⟩

end Reduces₂

namespace RedAffReflTrans

theorem elim_f_α_norm (hr : RedAffReflTrans (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α₂, f_β₂) env₂))) (hn : IsNorm RedAff f_α) : f_α₂ = f_α := by
  match hr.cases_head with
  | .inl h => simp_all
  | .inr ⟨_, h₁, h₂⟩ =>
    cases h₁ with
    | congrFun h =>
      cases h with
      | pil h => exact (hn ⟨_, h⟩).elim
      | pir h =>
        change RedAffReflTrans _ _ at h₂
        have h_dec := h.decreasing
        exact elim_f_α_norm h₂ hn
    | congrArg h =>
      change RedAffReflTrans _ _ at h₂
      have h_dec := h.decreasing
      exact elim_f_α_norm h₂ hn
termination_by f_β.size + env.size

theorem elim_f_β_norm (hr : RedAffReflTrans (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α₂, f_β₂) env₂))) (hn : IsNorm RedAff f_β) : f_β₂ = f_β := by
  match hr.cases_head with
  | .inl h => simp_all
  | .inr ⟨_, h₁, h₂⟩ =>
    cases h₁ with
    | congrFun h =>
      cases h with
      | pir h => exact (hn ⟨_, h⟩).elim
      | pil h =>
        change RedAffReflTrans _ _ at h₂
        have h_dec := h.decreasing
        exact elim_f_β_norm h₂ hn
    | congrArg h =>
      change RedAffReflTrans _ _ at h₂
      have h_dec := h.decreasing
      exact elim_f_β_norm h₂ hn
termination_by f_α.size + env.size

end RedAffReflTrans

namespace RedEta??

theorem pi_transport.{u} {τ_c : Type u} [DecidableEq τ_c] {f_α f_β env f_α₂ f_β₂ env₂ x e' : GenericExpr τ_c}
  (hr₁ : Reduces₂ (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α₂, f_β₂) env₂)))
  (hr₂ : RedAffReflTrans (DCC? (f_β env x)) e') (hn : IsNorm RedAff e') : RedAffReflTrans (DCC? (f_β₂ env₂ x)) e' := by
  let ⟨_, h₁, h₂⟩ := hr₁.pi_conf hr₂
  have h := hr₂.push_head' hn h₁
  exact .trans h₂ h

theorem transport.{u} {τ_c : Type u} [DecidableEq τ_c] {f x e' f' : GenericExpr τ_c}
  (hr₁ : Reduces₂ (DCC? (f x)) e') (hr₂ : RedEta?? f f') : Reduces₂ (DCC? (f' x)) e' := by
  
  sorry

end RedEta??

namespace RedEta₂

/-
Π transport:

(Π(f_α, f_β) env) RedEta₂ -> (Π(f_α₂, f_β₂) env₂)
and RedAffReflTrans (DCC? (f_β env x)) e'
then RedAffReflTrans (DCC? (f_β₂ env₂ x)) e'
-/

theorem pi_conf.{u} {τ_c : Type u} [DecidableEq τ_c] {f_α f_β env f_α₂ f_β₂ env₂ x e' : GenericExpr τ_c}
  (hr₁ : RedEta₂ (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α₂, f_β₂) env₂)))
  (hr₂ : RedAffReflTrans (DCC? (f_β env x)) e') : ∃ e'', RedAffReflTrans (DCC? (f_β env x)) e'' ∧ RedAffReflTrans (DCC? (f_β₂ env₂ x)) e'' := by
  sorry

theorem pi_transport.{u} {τ_c : Type u} [DecidableEq τ_c] {f_α f_β env f_α₂ f_β₂ env₂ x e' : GenericExpr τ_c}
  (hr₁ : RedEta₂ (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α₂, f_β₂) env₂)))
  (hr₂ : RedAffReflTrans (DCC? (f_β env x)) e') (hn : IsNorm RedAff e') : RedAffReflTrans (DCC? (f_β₂ env₂ x)) e' := by
  let ⟨_, h₁, h₂⟩ := hr₁.pi_conf hr₂
  have h := hr₂.push_head' hn h₁
  exact .trans h₂ h

theorem pi_transport'.{u} {τ_c : Type u} [DecidableEq τ_c] {f_α f_β env f_α₂ f_β₂ env₂ x e' : GenericExpr τ_c}
  (hr₁ : RedEta₂ (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α₂, f_β₂) env₂)))
  (hr₂ : Reduces₂ (DCC? (f_β env x)) e') : Reduces₂ (DCC? (f_β₂ env₂ x)) e' := by
  sorry

/-
Transport:

- if a function eta reduces f -> f', and Reduces₂ (DCC? (f x)) e', then Reduces₂ (DCC? (f' x))
-/

/-theorem transport₁.{u} {τ_c : Type u} [DecidableEq τ_c] {f x e' f' : GenericExpr τ_c}
  (h_comb : IsRedCombApp f (m + 1))
  (hr₁ : RedAff (DCC? (f x)) e') (hr₂ : RedEta₂ f f') : RedAff (DCC? (f' x)) e' := by
  cases hr₂ with
  | refl => assumption
  | step hr₂ =>
    induction hr₂ with
    | pi₁' | pi₁ =>
      cases h_comb with
      | app h => cases h
    | pi₂ => cases h_comb
    | pi₃ =>
      cases h_comb with
      | comp' =>
        
        sorry-/

@[grind ., grind →, dcc_reduce]
theorem no_op_sort.{u} {τ_c : Type u} [DecidableEq τ_c] {τ : GenericExpr τ_c} (h : RedEta₂ (τ_c := τ_c) (DCC? Sort m) τ) : τ = (DCC? Sort m) := by
  have h := h.complete
  simp [red_eta] at h
  split at h
  case h_1 heq =>
    rw [red_eta??] at heq
    simp [red_eta?, view_eta?, expr_to_eta, fn_reduces, tm_arity, is_eta_tm?] at heq
    simp_all
  · simp_all

end RedEta₂

namespace Reduces₂

def elim_head_norm.{u} {τ_c : Type u} [DecidableEq τ_c] {A B : GenericExpr τ_c} (hr₁ : Reduces₂ A B) (hn₁ : IsNorm RedAff A) : RedEta₂ A B :=
  match hr₁ with
  | ⟨hr₂, hn₂, hr₃⟩ => by
    cases hn₁.unique_refl hr₂
    exact hr₃

end Reduces₂

namespace RedEta₂

theorem cases_head.{u} {τ_c : Type u} [DecidableEq τ_c] {A B : GenericExpr τ_c} (h : RedEta₂ A B) : A = B ∨ RedEta?? A B := by
  cases h
  · exact .inl rfl
  · exact .inr (by assumption)

end RedEta₂

namespace RedAff

theorem reduce_red.{u} {τ : Type u} {A B : GenericExpr τ} (hr : RedAff A B) : reduce' RedAff A = reduce' RedAff B := by
  have h := (GenericExpr.reduce RedAff A).snd.down
  have hb := RedAffReflTrans.push_head h (reduce_norm rfl) hr
  have heq := reduce_complete hb (reduce_norm rfl)
  simp [reduce', heq]

end RedAff

end GenericExpr

namespace Relation

namespace ReflTransGen

theorem pi_shape (hr : ReflTransGen GenericExpr.RedAff (DCC? (Π(f_α, f_β) env)) B) : ∃ f_α' f_β' env', B = (DCC? (Π(f_α', f_β') env')) := by
  match hr.cases_head with
  | .inl h => exact ⟨_, _, _, by cases h; rfl⟩
  | .inr ⟨_, h₁, h₂⟩ =>
    match h₁ with
    | .congrFun (.pil h) =>
      have h_dec := h.decreasing
      exact pi_shape h₂
    | .congrFun (.pir h) =>
      have h_dec := h.decreasing
      exact pi_shape h₂
    | .congrArg h =>
      have h_dec := h.decreasing
      exact pi_shape h₂
termination_by (f_α.size + f_β.size + env.size)

end ReflTransGen

end Relation

namespace GenericExpr

def expr_to_eta_holds_red (hr : RedAff e e') : RedAff e.expr_to_eta e'.expr_to_eta := by
  induction hr
  any_goals (
    rename_i ih
    simp [expr_to_eta]
    constructor
    try assumption)

namespace IsNorm

def elim_head_norm.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c] {A B : GenericExpr τ_c}
  (h : Reduces₂ A B) (hn : IsNorm RedAff A) : (red_eta A).fst = B :=
  match h with
  | ⟨hr₁, hn₁, hr₂⟩ => by
    cases hr₁.elim_head_norm hn
    simp [hr₂.complete]

end IsNorm

namespace Arrow

theorem α_norm [DecidableEq τ_c] [BEq τ_c] {α β : GenericExpr τ_c} (harr : Arrow α β m τ) (h_judge : Judge₂ e τ) : IsNorm RedAff α := by sorry

--theorem α_norm_eta [DecidableEq τ_c] [BEq τ_c] {α β : GenericExpr τ_c} (harr : Arrow α β m τ) (h_judge : Judge₂ e τ

end Arrow

namespace RedEta??

theorem mk_pi₁ [DecidableEq τ_c] [BEq τ_c] {f_α f_β env : GenericExpr τ_c} (hr₁ : RedEta?? f_α f_α') (h_dom : Domain (expr_to_eta f_α) δ)
  (hn₁ : ¬ δ.contains_hole)
  (hr₂ : RedEta?? env env')
  (hr₃ : RedEta?? (reduce RedAff (DCC? (f_β env))).fst f_β')
  (hn₂ : f_β' ≠ (DCC? (f_β env))) : RedEta?? (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', `(#(eta_to_expr δ hn), f_β')) env')) :=
  RedEta??.pi₁ hr₁ h_dom hn₁ hr₂ (reduce_sound rfl) (reduce_norm rfl) hr₃ hn₂

theorem none_sound [DecidableEq τ_c] [BEq τ_c] {e : GenericExpr τ_c} (hneq : red_eta?? e = .none) : ¬ ∃ e', RedEta?? e e' := fun ⟨_, h⟩ => by
  simp_all [h.complete]

theorem pi_f_α_eq [DecidableEq τ_c] [BEq τ_c] {f_α f_β env : GenericExpr τ_c}
  (hr : RedEta?? (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', f_β) env))) : RedEta?? f_α f_α' := by
  sorry

theorem pi_env_eq [DecidableEq τ_c] [BEq τ_c] {f_α f_β env : GenericExpr τ_c}
  (hr : RedEta?? (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α, f_β) env'))) : RedEta?? env env' := by
  sorry

end RedEta??

namespace RedEta₂

theorem pi_f_β.{u} {τ_c : Type u} {f_α f_β env f_α₂ f_β₂ env₂ : GenericExpr τ_c} [DecidableEq τ_c] (h : RedEta₂ (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α₂, f_β₂) env₂))) (hn : IsNorm RedAff f_β) : RedEta?? f_β f_β₂ := by
  sorry

end RedEta₂

/-
Plan of attack:

Lining up Reduces₂ is super annoying. For example:

Eql(f_α) &(env) &(x) --> (x = x)

Type for this should be Prop

This is essentially a constant operation.

---- probably not necessary 1. No-op lemmas for RedEta₂. For each canonical-eta form, have that RedEta canon_val e' -> e' = canon_cal
2. Congruence lemmas for Π under RedEta₂.
  - Note: when an environment is supplied, f_β is η-reduced with env applied, then resulting η-val is quoted.

  Congruence lemma with env:
  - RedEta?? f_α
    + RedEta?? (reduce RedAff (f_β env)) f_β_env' (+ IsNorm)
      + ≠ (f_β env)
    then use smaller congruence lemmas

  Note: RedEta is unique. Hence, we can reverse by constructing RedEta on components, then rewriting

3. Assume we have:
  3a.
    - congr_pi (hr₁ : RedEta?? f_α f_α') (hr₂ : RedEta?? (reduce RedAff (DCC? (f_β env))) f_β_env)
      (hneq : f_β_env ≠ (DCC? (f_β env))) : RedEta?? (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', `(#(eta_to_expr δ hn), f_β')) env'))

    - none_sound (heq : red_eta? e = .none) : ¬ ∃ e', RedEta? e e'

    then we are RedEta Π(!<f_α>, Λ(!(δ), !<f_α>, `(Coup(!<f_α>), Sort 0)))
    - this is just recurse on α and β
    - !<f_α>

    η-reduction on this entire term collapses, I think, to just β-reduction, since !<f_α> is η-normal

    then we have succesfully gotten that hypothesis out.
    f_α := id
    f_β := ((GenericExpr.sort o).quot (f_α.map.pi (δ.bang.curr f_α.map (f_α.map.coup.quot (GenericExpr.sort 0)))))
    x_α := (reduce RedAff δ)

    α₁ := (reduce RedAff δ)

  BIG NOTE:
  - f_α congruence on Π kills most of this and gets us x_α eq for free
    theorem eta_pi_f_α (hr : RedEta₂ (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α₂, f_β₂) env₂))) : (red_eta₂ f_α) = f_α₂ := by sorry
    theorem eta_pi_env (hr : RedEta₂ (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α₂, f_β₂) env₂))) : (red_eta₂ env) = env₂ := by sorry

4. By eta_pi_env, since δ in Arrow is the α part of an Arrow, and it is in congrArg position, then it is Aff normal and since
  τ is a Judged type, then it is a reduced expr, so δ is unique
5. !(δ) is already normal and eta-reduced
6. x_α' := !(δ)
7. Need f_β as well, though. requires further congruences:

  theorem eta_pi_f_β (hr₁ : RedEta₂ f_β₁ f_β₂) (hr₂ : RedEta₂ (DCC? (Π(f_α, f_β₁))) (DCC? (Π(f_α, f_β₃)))) : f_β₃ = f_β₂ := by sorry

8. ((f_α¹.pi f_β¹).app x_α¹) := ((f_α.map.pi (δ.bang.curr f_α.map (f_α.map.coup.quot (GenericExpr.sort 0)))) &(x))
  same process as above
  f_α¹ is already η-reduced
  theorem eta_pi_f_α_norm (hr₁ : RedEta?? f_α f_α') (hr₂ : RedEta₂ (DCC? (Π(f_α', f_β) env)) (DCC? (Π(f_α₂, f_β₂) env₂))) : f_α₂ = f_α' := by sorry

9. with f_β¹ := (δ.bang.curr f_α.map (f_α.map.coup.quot (GenericExpr.sort 0)))

  then push_head (DCC? (f_β¹ x_α'¹ &(x))), aff reduction gives just Sort 0. Boom. done.
-/

namespace Reduces₂

/-
If there is some intermediate step A → B in a reduction

A =-=> C

then B =-=> C

This is useful for preservation, since you can do congruence as such.
-/
def push.{u} {τ : Type u} [DecidableEq τ] [BEq τ] {A B C : GenericExpr τ}
  (h₁ : Reduces₂ A C) (h₂ : RedAff A B) : Reduces₂ B C :=
  match h₁ with
  | ⟨hr₁, hn₁, hr₂⟩ =>
    have ⟨_D, h₁, h₂⟩  := hr₁.conf (.single h₂)
    have heq := h₁.elim_head_norm hn₁
    ⟨heq.symm ▸ h₂, hn₁, hr₂⟩

end Reduces₂

namespace Pi.f_β.type

def unqiue.{u} {τ : Type u} [DecidableEq τ] {f_α₁ δ₁ f_α₂ δ₂ τ : GenericExpr τ}
  (h₁ : Pi.f_β.type f_α₁ δ₁ o₁ n₁ τ)
  (h₂ : Pi.f_β.type f_α₂ δ₂ o₂ n₂ τ) : f_α₁ = f_α₂ ∧ δ₁ = δ₂ ∧ o₁ = o₂ ∧ n₁ = n₂ := by
  cases h₁ <;> (cases h₂; grind)

/-def is_norm.{u} {τ : Type u} [DecidableEq τ] {f_α₁ δ₁ τ : GenericExpr τ} (h₁ : Pi.f_β.type f_α₁ δ₁ o₁ n₁ τ) : IsNorm RedAff τ := by
  cases h₁

  sorry-/

/-
5. Turn "should already be a normal form" into a lemma. Your comment — δ is normal because it's in an arrow inside a judge — is a real invariant, so prove it: Arrow δ s o τ → Normal δ (or whatever the true statement is). Then hred : Reduces₂ δ δ' collapses via Normal.reduces_eq to δ' = δ and you subst. Right now you're re-deriving that fact inline every time it comes up; do it once.

prove these invariants.
-/

end Pi.f_β.type

namespace Reduces₂

theorem pi.{u} {τ_c : Type u} [DecidableEq τ_c] {f_α f_β env f_α₂ f_β₂ env₂ : GenericExpr τ_c} (h : Reduces₂ (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α₂, f_β₂) env₂)))
  (hn₁ : IsNorm RedAff f_α) (hn₂ : IsNorm RedAff f_β) : RedEta₂ (DCC? (Π(f_α, f_β) #(reduce' RedAff env))) (DCC? (Π(f_α₂, f_β₂) env₂)) :=
  match h with
  | ⟨hr₁, hn₃, hr₂⟩ =>
    match hr₁.cases_head with
    | .inl heq => by
      cases heq
      have heq₂ := reduce'_complete .refl hn₃.congrArg
      simp [heq₂]
      exact hr₂
    | .inr ⟨_, h₁, h₂⟩ => by
      cases h₁ with
      | congrFun h =>
        cases h with
        | pil h => exact (hn₁ ⟨_, h⟩).elim
        | pir h => exact (hn₂ ⟨_, h⟩).elim
      | congrArg hr =>
        have ⟨f_α', f_β', env', heq⟩ := h₂.pi_shape
        cases heq
        have h_dec := hr.decreasing
        have h := pi ⟨h₂, hn₃, hr₂⟩ hn₁ hn₂
        simp [hr.reduce_red, h]
termination_by (size env)

end Reduces₂

namespace Judge₂

theorem preservation.{u} {τ_c : Type u} [DecidableEq τ_c] {e e' τ : GenericExpr τ_c} (h : Judge₂ e τ) (hr : RedEta₂ e e') : Judge₂ e' τ := by
  sorry

theorem invert_app.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c]
  {f x τ : GenericExpr τ_c} (ht : Judge₂ (DCC? (f x)) τ) :
  (∃ (f_α f_β x_α α₂ : GenericExpr τ_c), (Judge₂ f (DCC? (Π(f_α, f_β) x_α))) ∧ (Judge₂ x α₂)
  ∧ (DefEq (reduce_all₂ (DCC? (f_α x_α))) α₂) ∧ (Reduces₂ (DCC? (f_β #(reduce_all₂ x_α) x)) τ)) :=
  match ht with
  | .app (f_α := f_α) (f_β := f_β) (x_α := x_α) (α₂ := α₂) h_t_f hr₁ h_t_x h_deq hr₂ hr₃ =>
    ⟨f_α, f_β, x_α, α₂, h_t_f, h_t_x, hr₁.complete ▸ h_deq, hr₂.complete ▸ hr₃⟩

/-
TODO: invariant that Judge _ τ and Arrow _ _ _ τ means τ IsNorm
-/

/-inductive InvertEql

theorem invert_eql.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c]
  {f_α τ : GenericExpr τ_c} (ht : Judge₂ (DCC? (Eql(f_α))) τ) :
  ∃ (τ_f_α δ : GenericExpr τ_c) (m o : Level), Judge₂ f_α τ_f_α ∧ Arrow δ (DCC? Sort m) o τ_f_α ∧ Reduces₂ (eql.type f_α δ o) τ -/

def is_norm.{u} {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c] {e τ : GenericExpr τ_c} (h : Judge₂ e τ) : IsNorm RedAff τ := by
  cases h
  any_goals (
    focus
    intro ⟨_, h⟩; cases h; done)
  any_goals (exact Reduces₂.is_norm (by assumption))
  case box ht =>
    intro ⟨_, h⟩; cases h
    exact (ht.is_norm) ⟨_, by assumption⟩

theorem preservation_eql [DecidableEq τ_c] {f_α env x : GenericExpr τ_c} (h_t : Judge₂ (DCC? (Eql(f_α) env &(x))) τ) : Judge₂ (DCC? x = x) τ := by
  cases h_t with
  | app h_t_f =>
    cases h_t_f with
    | app h_t_f =>
      cases h_t_f with
      | eql =>
        rename_i h_box h_r_τ _ _ _ _ _ _ hr₂ hdeq hr₃ _ hr₄ _ _ m o harr h_t_f_α h_r_τ_eql
        simp [eql.type] at h_r_τ_eql
        /-
        f_β is the main component we we need to link.
        It's a quotation, so it is already a normal value.
        -/
        --have h := RedEta₂.unique
        cases h_box with
        | box h_t_x =>
          have h := h_r_τ_eql.pi (fun ⟨_, h⟩ => by cases h) (fun ⟨_, h⟩ => by cases h)
          rename_i δ _ _
          rw [reduce'_bang] at h
          match h.cases_head with
          | .inl h =>
            cases h
            have h := hr₂.push .id
            rw [reduce'_complete (.refl) (harr.α_norm (by assumption))] at h
            match (h.elim_head_norm (fun ⟨_, h⟩ => by cases h with
            | bang h => exact (harr.α_norm (by assumption)) ⟨_, h⟩)).cases_head with
            | .inl h =>
              cases h
              have h := (hr₄.push (.congrFun .quot)).pi (fun ⟨_, h⟩ => by cases h) (fun ⟨_, h⟩ => by cases h)
              match h.cases_head with
              | .inl h =>
                cases h
                match (((h_r_τ.push .curr).push (.quot)).elim_head_norm (fun ⟨_, h⟩ => by cases h)).cases_head with
                | .inl h =>
                  cases h
                  exact .eq (by assumption) (by assumption)
                | .inr h =>
                  -- THIS TECHNIQUE FOR LATER: have h_dec := h.decreasing?
                  cases h with
                  | tm₁ h hr =>
                    cases hr with
                    | mk₁ hr => cases hr <;> grind
                    | mk₂ hr => cases hr <;> grind
                  | tm₂ => exact .eq (by assumption) (by assumption)
              | .inr h =>
                cases h with
                | pi₁ =>
                  sorry
                | tm₂ _ _ hr' =>
                  match (((h_r_τ.push .curr).push .quot).elim_head_norm (fun ⟨_, h⟩ => by cases h)).cases_head with
                  | .inl h =>
                    cases h
                    exact .eq (by assumption) (by assumption)
                  | .inr h =>
                    cases h.red_sort
                    exact .eq (by assumption) (by assumption)
                | tm₁ _ hr =>
                  
                  sorry
                | pi₁' =>
                  sorry
            | .inr h =>
              sorry
          | .inr h =>
            sorry
          /-have h := h_r_τ_eql.pi_transport (.single (.congrFun (x := env) .quot)) (Reduces₂.trans (Reduces₂.instCongruent.congrFun_ (x := env) (Reduces₂.instCongruent.congrArg_ hr₃)) hr₄)
          
          have h' := (h.pi_transport' ⟨.trans (.single (.congrFun (x := reduce' RedAff δ.bang) .quot)) (by rw [reduce'_bang]; exact .refl), fun ⟨_, h⟩ => by
            cases h with
            | congrFun h => cases h with
              | pil h => cases h
              | pir h => cases h
            | congrArg h =>
              cases h with
              | bang h =>
                exact reduce'_norm' (r := RedAff) (A := δ) ⟨_, h⟩, .step (.pi₁ (red_eta??_sound (by sorry)) (by sorry) (by sorry) (by sorry) (by sorry) (by sorry) (by sorry) (by sorry))⟩)
          have h_bang_norm : IsNorm RedAff δ.bang := fun ⟨_, h⟩ => by
            cases h with
            | bang hr =>
              exact harr.α_norm h_t_f_α ⟨_, hr⟩
          rw [reduce'_complete .refl h_bang_norm] at h'
          have heq₁ := h'.elim_norm' (fun ⟨_, h⟩ => by
            
            sorry)-/
          /-match h.cases_head with
          | .inl h =>
            simp_all
            rw [← h.left.right] at hr₄
            rw [← h.right] at hr₃
            have hr₄' := (hr₄.push (.congrFun .quot)).pi (fun ⟨_, h⟩ => by cases h) (fun ⟨_, h⟩ => by cases h)
            have h := hr₄'.complete
            simp [red_eta] at h
            match hr₄'.cases_head with
            | .inl h =>
              simp_all
              rw [← h.left.right] at h_r_τ
              have h := (((h_r_τ.push .curr).push .quot).elim_head_norm (fun ⟨_, h⟩ => by cases h)).no_op_sort
              exact h ▸ Judge₂.eq h_t_x h_t_x
            | .inr h =>
              -- Use more simps + completeness to destruct RedEta?? easier..
              have heq := h.complete
              rw [red_eta??] at heq
              simp [view_eta?, expr_to_eta, domain?] at heq
              simp_all
              split at heq
              case h_1 heq' =>
                simp [expr_to_eta] at heq'
                split at heq'
                case h_1 =>
                  simp_all
                  
                  sorry
                case h_2 =>
                  sorry-/
                /-rename_i heq_all _ _ _
                rw [← heq_all.left.right] at hr₄
                rw [← heq_all.right] at hr₃
                have hr₄ := (hr₄.push (.congrFun .quot)).pi (fun ⟨_, h⟩ => by cases h) (fun ⟨_, h⟩ => by cases h)-/
                
                --sorry
          --| .inr h =>
            --sorry

theorem preservation [DecidableEq τ_c] {e : GenericExpr τ_c} (ht : Judge₂ e τ) (hr : RedAff e e') : Judge₂ e' τ := by
  induction ht generalizing e' with
  | app h_t_f h_r_α h_t_x h_deq h_r_α₂ h_r_τ ih₁ ih₂ =>
    cases hr with
    | eql =>
      cases h_t_x with
      | box h_t_x =>
        cases h_t_f with
        | app h_t_f_eql =>
          cases h_t_f_eql with
          | eql =>
            rename_i h_r_τ_eql
            simp [eql.type] at h_r_τ_eql
            sorry
  | eq h_t_x h_t_y ih₁ ih₂ =>
     cases hr with
     | eql' hr => exact .eq (ih₁ hr) h_t_y
     | eqr' hr => exact .eq h_t_x (ih₂ hr)
  | coup h_t_β hr_t_x hr_τ ih =>
     cases hr with
     | coup hr => exact .coup (ih hr) hr_t_x hr_τ
  | mk h_t_x h_t_β harr hr_t_x h_t_y h_r_τ ih₁ ih₂ ih₃ =>
     cases hr with
     | sigl hr => exact .mk (ih₁ hr) h_t_β harr (hr_t_x.push (.congrArg hr)) h_t_y h_r_τ
     | sigr hr => exact .mk h_t_x h_t_β harr hr_t_x (ih₃ hr) h_r_τ
  | pair h_t_f hr_β h_t_g h_r_γ₁ h_r_pi_snd hr_γ h_r_snd_arg_τ h_r_γ h_r_τ_fst ih₁ ih₂ =>
     cases hr with
     | pairl hr => apply Judge₂.pair (ih₁ hr) <;> assumption
     | pairr hr => apply Judge₂.pair (by assumption) (by assumption) (ih₂ hr) <;> assumption
  | pi h_t_f_α h_arr h_t_f_β h_r_f_α h_shape_f_β h_r_τ ih₁ ih₂ =>
     cases hr with
     | pil hr =>
       have h_r_f_α' := h_r_f_α.push hr
       apply Judge₂.pi (ih₁ hr) <;> assumption
     | pir hr =>
       apply Judge₂.pi h_t_f_α h_arr (ih₂ hr) <;> assumption
  | bang ht ih =>
    cases hr with
    | bang hr =>
      exact .bang (ih hr)
  | refl | eql | id | sort | comp | comp₂ | comp' | fstc | sndc
  | sigma | curr | curr' | map | fmap | unmap | eval | quot | top | bot
  | tintro | box | unbox => cases hr

end Judge₂

end GenericExpr
