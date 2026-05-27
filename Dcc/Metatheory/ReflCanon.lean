import Dcc.Ast
import Dcc.Judge
import Dcc.Tactic.Reduce

/-
Want to automate IsNorm, but sounds hard.
-/

namespace Expr

abbrev Arity := ℕ

-- Combinators that can make a step with their well-typed arguments
inductive IsRedComb : Expr → Arity → Type
  -- Eql(f_α) env x -> (x = x)
  | eql   : IsRedComb (DCC Eql(f_α)) 2
  -- Id(α) x
  | id    : IsRedComb (DCC Id(α)) 1
  -- (f ∘ g) x
  | comp  : IsRedComb (DCC (f ∘ g)) 1
  | comp' : IsRedComb (DCC (f ∘' g)) 1
  -- Fstc(..) (x, y) -> x
  | fstc  : IsRedComb (DCC Fstc(β)) 1
  | sndc  : IsRedComb (DCC Sndc(β)) 1
  -- Σ(f_α, f_β) env -> Coup(...)
  | sigma : IsRedComb (DCC Σ(f_α, f_β)) 1
  -- `(β, x) y
  | quot  : IsRedComb (DCC `(β, x)) 1
  -- ⟨f, g⟩ x
  | pair  : IsRedComb (DCC ⟨f, g⟩) 1
  -- Λ(α, β, x) y z
  | curr  : IsRedComb (DCC Λ(α, β, x)) 2

inductive IsRedCombApp : Expr → Arity → Type
  -- Eql(f_α) env x -> (x = x)
  | eql   : IsRedCombApp (DCC Eql(f_α)) 2
  -- Id(α) x
  | id    : IsRedCombApp (DCC Id(α)) 1
  -- (f ∘ g) x
  | comp  : IsRedCombApp (DCC (f ∘ g)) 1
  | comp' : IsRedCombApp (DCC (f ∘' g)) 1
  -- Fstc(..) (x, y) -> x
  | fstc  : IsRedCombApp (DCC Fstc(β)) 1
  | sndc  : IsRedCombApp (DCC Sndc(β)) 1
  -- Σ(f_α, f_β) env -> Coup(...)
  | sigma : IsRedCombApp (DCC Σ(f_α, f_β)) 1
  -- `(β, x) y
  | quot  : IsRedCombApp (DCC `(β, x)) 1
  -- ⟨f, g⟩ x
  | pair  : IsRedCombApp (DCC ⟨f, g⟩) 1
  -- Λ(α, β, x) y z
  | curr  : IsRedCombApp (DCC Λ(α, β, x)) 2
  | app   : IsRedCombApp f (m + 1) → IsRedCombApp (DCC (f x)) m

/-
A normal form is either:
- a combinator with fewer than its arity arguments applied
  - and all arguments are values

- Π(f_α, f_β)
  - if f_β is a value
- Π(f_α, f_β) env
  - if f_β and env are values
- refl(f_α) env
  - if env is a value
- refl(f_α) env x
  - if env and x are values
- Coup(f_β)
- x = y

- a Sort m
- ⊤
- ⊥
- ∗
-/

inductive Value : Expr → Prop
  | pi₁    : Value f_β → Value (DCC Π(f_α, f_β))
  | pi₂    : Value f_β → Value env → Value (DCC (Π(f_α, f_β) env))
  | refl₁  : Value env → Value (DCC (refl(f_α) env))
  | refl₂  : Value env → Value x → Value (DCC (refl(f_α) env x))
  | coup   : Value (DCC Coup(f_β))
  | eq     : Value (DCC x = y)
  | comb   : IsRedComb c m → Value c
  | app    : IsRedCombApp (DCC (f x)) (m + 1) → Value f → Value x → Value (DCC (f x))
  | top    : Value (DCC ⊤)
  | bot    : Value (DCC ⊥)
  | tintro : Value (DCC ∗)
  | sort   : Value (DCC Sort m)

theorem Value.is_norm_aff (h : Value e) : IsNorm RedAff e := by
  sorry

theorem Value.is_norm_eta (h : Value e) : IsNorm RedEta e := by
  sorry

/-inductive IsComb : Expr → Arity → Type
  -- env x
  | refl  : IsComb (DCC refl(f_α)) 2
  -- Eql(f_α) env x
  | eql   : IsComb (DCC Eql(f_α)) 2
  -- Id(α) x
  | id    : IsComb (DCC Id(α)) 1
  -- (f ∘ g) x
  | comp  : IsComb (DCC (f ∘ g)) 1
  | comp' : IsComb (DCC (f ∘' g)) 1
  -- Fstc(..) (x, y)
  | fstc  : IsComb (DCC Fstc(β)) 1
  | sndc  : IsComb (DCC Sndc(β)) 1
  -- Σ(f_α, f_β) env
  | sigma : IsComb (DCC Σ(f_α, f_β)) 1
  -- `(β, x) y
  | quot  : IsComb (DCC `(β, x)) 1
  -- ⟨f, g⟩ x
  | pair  : IsComb (DCC ⟨f, g⟩) 1
  -- Λ(α, β, x) y z
  | curr  : IsComb (DCC Λ(α, β, x)) 2
  -- Π(f_α, f_β) env x
  | pi    : IsComb (DCC (Π(f_α, f_β)))-/

namespace Judge

-- Probably somewhat easy to prove
theorem eq_val_is_refl (ht : Judge e (DCC (x = y)))
  (hv : Value e) : ∃ f_α env, e = (DCC (refl(f_α) env x)) ∧ env.Value ∧ x.Value := by
  sorry

/-
Progress might be important for this too since we can establish what normal forms are.
If e : (x = y), then either e is a normal form (e.g., refl), or it reduces to (what?)
-/

theorem preservation (ht : Judge A t) (hr : RedAff A B) : Judge B t := by
  sorry

-- for refl canon
-- move to preservation.lean later
-- Hard one. Important, though. absolutely required for the proof.
theorem preservation' (ht : Judge A t) (hr : Reduces A B) : Judge B t := by
  sorry

theorem progress (ht : Judge e τ) : Value e ∨ (∃ e', RedAff e e') := by
  sorry

theorem refl_inhabits_id
  (h_t_f_α : Judge f_α (DCC (δ : Sort o) → Sort m))
  (h_t_env : Judge env δ)
  (h_red_α : Reduced (DCC (f_α env)) α)
  (h_red_x : Reduces x x')
  (h_t_x   : Judge x α) : Judge (DCC (refl(f_α) env x)) (DCC x' = x') :=
  .app (.app (.refl h_t_f_α (by
    dcc red*  aff here
    
    sorry)) (by sorry) (by sorry) (by sorry)) (by sorry) (by sorry) (by sorry)

-- IMPORTANT
-- somewhat easy
theorem refl_ty_heq (h_t : Judge (DCC (refl(f_α) env x)) (DCC x = y)) : x = y := by
  sorry

theorem refl_ty (h_t : Judge (DCC (refl(f_α) env x)) τ)
  (hr : Reduces x x') : τ = (DCC x' = x') := by
  sorry

theorem refl_preservation (h_t : Judge (DCC (refl(f_α) env x)) τ)
  (h_red : Reduces A (DCC (refl(f_α) env x)))
  (hred' : Reduces x x') : Judge A (DCC x' = x') := by
  sorry

/-
induction using Expr.instWellFounded?

Due to progress
-/
theorem eq_is_refl (h_t : Judge e (DCC (x = y))) :
  ∃ f_α env, Reduces e (DCC (refl(f_α) env x)) := by
  induction e using RedAff.instRedRel.wellFounded.induction with
  | h e ih =>
    match h_t.progress with
    | .inl h_val =>
      have ⟨f_α, env, heq⟩ := h_t.eq_val_is_refl h_val
      simp_all
      exact ⟨f_α, env, ⟨.refl, h_val.is_norm_aff, .refl, h_val.is_norm_eta⟩⟩
    | .inr ⟨e', hr⟩ =>
      match ih _ hr (h_t.preservation hr) with
      | ⟨f_α, env, ⟨hr₁, hn₁, hr₂, hn₂⟩⟩ =>
        exact ⟨f_α, env, ⟨.trans (.single hr) hr₁, hn₁, hr₂, hn₂⟩⟩

theorem elim_eq (h : Judge e (DCC (x = y))) : x = y := by
  have ⟨f_α, env, h_r⟩ := eq_is_refl h
  have ht' := h.preservation' h_r
  exact refl_ty_heq ht'

end Judge

end Expr
