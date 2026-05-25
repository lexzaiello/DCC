import Dcc.Ast
import Dcc.Judge
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

inductive EqEnvFn : Expr → Expr → Prop
  | eql    : Judge f_α (DCC (δ : Sort o) → Sort m)
    → EqEnvFn (DCC (Eql(f_α))) (eql.type f_α δ m o)
  | quot   : EqEnvFn x (DCC ((γ : Sort o) → Sort 0))
    → EqEnvFn (DCC `(β, x)) (DCC ((β : Sort n) → ((γ : Sort o) → Sort 0)))
  | comp'  : Judge g (DCC ((α : Sort m) → β))
    → Judge β (DCC Sort n)
    → EqEnvFn f (DCC ((β : Sort n) → ((γ : Sort o) → Sort 0)))
    → EqEnvFn (DCC (f ∘' g)) (DCC ((α : Sort m) → ((γ : Sort o) → Sort 0)))
  -- may need to handle fully dependent
  | comp   : Judge g (comp.g.type α f_β m)
    → Judge f (DCC (Π(Id(Sort n), f_γ) Coup(f_β)))
    → EqEnvFn f (DCC ((Coup(f_β) : Sort n) → ((γ : Sort o) → Sort 0)))
    → EqEnvFn (DCC (f ∘ g)) (DCC ((α : Sort m) → ((γ : Sort o) → Sort 0)))
  | id     : Reduces α (DCC ((β : Sort n) → Sort 0))
    → EqEnvFn (DCC Id(α)) (DCC (((x = y) : Sort 0) → ((β : Sort n) → Sort 0)))
  | curr   : Judge α (DCC Sort m)
    → Judge f_β (DCC ((α : Sort m) → Sort n))
    → EqEnvFn x (DCC ((Coup(f_β) : Sort (max m n)) → Sort 0))
    → EqEnvFn (DCC Λ(α, β, x)) (curr.type α β (DCC `(Coup(f_β), Sort 0)) m)

namespace EqFnEnv

theorem elim_env_arrow (h_t_f : Judge f (DCC (Π(f_α, f_β) env)))
  (h_r_α   : Reduces (DCC (f_α env)) α)
  (h_t_α   : Judge α (DCC Sort m))
  (h_eq_fn : EqEnvFn f_β (DCC ((Sort m : Sort m + 1) → ((α : Sort m) → Sort 0))))
  (h_t_x   : Judge x α)
  (h_r_x'  : Reduces x x')
  (h_t     : Judge (DCC (f x)) (DCC (a = b))) : a = x' ∧ b = x' := by
  cases h_eq_fn with
  | quot h =>
    induction f generalizing x with
    | app _ _ ih₁ ih₂ =>
      have ⟨_, _, _, _, h_t_a₁, hr_w, h_t_x', h_r_τ'⟩ := h_t_f.invert rfl
      have h  := ih₁ 
      sorry


end EqFnEnv

end Expr
