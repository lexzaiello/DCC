import Dcc.Ast
import Dcc.Aff.Red
import Dcc.Tactic.Reduce
import Dcc.Judge
import Dcc.Complete
import Dcc.Preservation

/-
Pseudo-reducibility-candidate-like requirements
which expressions must satisfy to be possible
reducts of =.
-/

/-
f_β in Π(f_α, f_β).
This takes an environment and a term, yielding an x = y.
-/

namespace Expr

@[dcc_judge]
abbrev fn_env_arrow (x δ : Expr) (o : Level) :=
  (DCC (δ : Sort o) → ((((x = x) : Sort 0) → Sort 0)))

@[dcc_judge]
abbrev fn_env_forall (f_α env : Expr) (o : Level) :=
  DCC (Π(Id(Sort o), `(Sort o, Π(Id(Sort 0), `(Coup(Id(Sort 0)), Sort 0)) ∘ (Eql(f_α) env))))

inductive EqEnvFn : Expr → Expr → Prop
  | eql    : Judge f_α (DCC (δ : Sort o) → Sort m)
    → Reduces (eql.type f_α δ m o) τ
    → EqEnvFn (DCC (Eql(f_α))) τ
  | quot   : EqEnvFn x (DCC ((γ : Sort o) → Sort 0))
    → Reduces (DCC ((β : Sort n) → ((γ : Sort o) → Sort 0))) τ
    → EqEnvFn (DCC `(β, x)) τ
  | comp'  : Judge g (DCC ((α : Sort m) → β))
    → Judge β (DCC Sort n)
    → EqEnvFn f (DCC ((β : Sort n) → ((γ : Sort o) → Sort 0)))
    → Reduces (DCC ((α : Sort m) → ((γ : Sort o) → Sort 0))) τ
    → EqEnvFn (DCC (f ∘' g)) τ
  -- may need to handle fully dependent
  | comp   : Judge g (comp.g.type α f_β m)
    → Judge f (DCC (Π(Id(Sort n), f_γ) Coup(f_β)))
    → EqEnvFn f (DCC ((Coup(f_β) : Sort n) → ((γ : Sort o) → Sort 0)))
    → Reduces (DCC ((α : Sort m) → ((γ : Sort o) → Sort 0))) τ
    → EqEnvFn (DCC (f ∘ g)) τ
  | id     : Reduces (DCC ((#(fn_env_arrow x δ o) : Sort 0)
    → #(fn_env_arrow x δ o))) τ
    → EqEnvFn (DCC Id(#(fn_env_arrow x δ o))) τ
  | id'    : Reduces (DCC ((#(fn_env_forall f_α env o) : Sort 0)
    → #(fn_env_forall f_α env o))) τ →
    EqEnvFn (DCC Id(#(fn_env_forall f_α env o))) τ
  | curr   : Judge α (DCC Sort m)
    → Judge f_β (DCC ((α : Sort m) → Sort n))
    → EqEnvFn x (DCC ((Coup(f_β) : Sort (max m n)) → Sort 0))
    → Reduces (curr.type α β (DCC `(Coup(f_β), Sort 0)) m) τ
    → EqEnvFn (DCC Λ(α, β, x)) τ

namespace EqEnvFn

open Congruent RedAff RedEta in
theorem reduces_eq (h : EqEnvFn e τ)
  (h_r_x : RedAffReflTrans x x') (h_n_x : IsNorm RedAff x')
  (h_t   : Judge (DCC (e env x)) τ) : Reduces (DCC (e env x)) (DCC (x' = x')) := by
  induction h with
  | id =>
    have ⟨f_α, f_β, env₁, α, h_t_f, h_r_α, h_t_x, h_r_τ⟩        := h_t.invert rfl
    have ⟨f_α₁, f_β₁, env₂, α₁, h_t_f₁, h_r_α₁, h_t_x₁, h_r_τ₁⟩ := h_t_f.invert rfl
    cases h_t_f₁ with
    | id h_t_arr h_r_id =>
      dcc reduce+ eta from h_r_id
      
      sorry
  | eql =>
    constructor
    · exact .trans (congrFun' (congrArg' (reduce_sound rfl))) (congrArg' h_r_x)
    · intro ⟨_, h⟩
      have hn₁ : IsNorm RedAff (reduce RedAff env).fst := reduce_norm rfl
      cases h with
      | congrFun h =>
        cases h with
        | congrFun h =>
          cases h
        | congrArg h => exact hn₁ ⟨_, h⟩
      | congrArg h => exact h_n_x ⟨_, h⟩
    · exact .single .eql
    · intro ⟨_, h⟩; cases h
  

--theorem mk_app (h_t_f : EqEnvFn f (DCC (Π(f_α, f_β) env)))

theorem well_typed (h : EqEnvFn e τ) : Judge e τ := by
  /-induction h with
  | eql h_t_f h_r_τ => exact .eql (by assumption) h_r_τ
  | id hr =>
    have hr₁' := hr.complete
    exact .id (by sorry) (reduce_reduces (by
      unfold id.type
      
      sorry))
  | comp' h_t_g h_t_β h_t_f h_red =>
    
    sorry
  | comp h_t_g h_t_f h_r ih =>
    
    sorry-/
  sorry

/-
Π(f_α, f_β) env

f_β env x
-/

theorem elim_env_arrow (h_t_f : Judge f (DCC (Π(f_α, f_β) env)))
  (h_r_α   : Reduces (DCC (f_α env)) α)
  (h_t_α   : Judge α (DCC Sort m))
  (h_eq_fn : EqEnvFn f_β (DCC ((Sort m : Sort m + 1) → ((α : Sort m) → Sort 0))))
  (h_t_x   : Judge x α)
  (h_t     : Judge (DCC (f x)) (DCC (a = b))) : a = b := by
  cases h_eq_fn with
  | quot h =>
    have h_t₀ := h.well_typed
    cases h_t with
    | app =>
      dcc_simp_all
      
      sorry


end EqEnvFn

end Expr
