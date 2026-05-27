import Dcc.Ast
import Dcc.Judge
import Dcc.Tactic.Reduce
import Dcc.Metatheory.Congr
import Dcc.Metatheory.Preservation

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

/-
Substitution lemma...

adding a 
-/

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

/-theorem refl_ty_heq (h_t : Judge (DCC (refl(f_α) env x)) (DCC x = y)) : x = y := by
  induction env using RedAff.instRedRel.wellFounded.induction with
  | h env ih =>
    have ⟨a, b, c, d, h_t_refl_env, f, g, h⟩ := h_t.invert rfl
    have ⟨i, j, k, l, m, o, p, q⟩ := h_t_refl_env.invert rfl
    cases m with
    | refl r s =>
      match q with
      | ⟨hr₁, hn₁, hr₂, hr₄⟩ =>
        cases hr₁ using Relation.TransGen.head_induction_on with
        | single h =>
          cases h with
          | congrFun h =>
            
            sorry
          | congrArg h =>
            sorry
          | curr =>
            sorry
        | head h ih =>
          sorry-/

theorem refl_ty_heq (h_t : Judge (DCC (refl(f_α) env x)) (DCC x = y)) : x = y := by
  have ⟨a, b, c, d, h_t_refl_env, f, g, h⟩ := h_t.invert rfl
  have ⟨i, j, k, l, m, o, p, q⟩ := h_t_refl_env.invert rfl
  cases m with
  | refl r s =>
    --dcc_simp_all (! !)
    match s with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      cases hr₁.cases_head with
      | inl h =>
        cases h
        cases hr₂.cases_head with
        | inl h =>
          cases h
          match q with
          | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
            cases hr₁ using Relation.TransGen.head_induction_on with
            | single h =>
              cases h with
              | congrFun h =>
                cases h with
                | quot =>
                  cases hr₂.cases_head with
                  | inl h =>
                    dcc_simp_all
                    have ⟨⟨h₁, h₂⟩, h₃⟩ := h
                    simp_all
                    cases h.symm
                    rename_i hreql _ _ _
                    match hreql with
                    | ⟨h₁, h₂, h₃, h₄⟩ =>
                      cases h₃ with
                      | refl =>
                        cases h₁ using Relation.TransGen.head_induction_on with
                        | single h =>
                          sorry
                        | head h ih =>
                          
                          sorry
                      | tail ih h => cases h; rfl
                  | inr h =>
                    sorry
                | congrArg h =>
                  sorry
                | congrFun h =>
                  sorry
              | congrArg h =>
                sorry
            | head h ih =>
              cases h with
              | congrFun h =>
                cases h with
                | quot =>
                  sorry
                | congrArg h =>
                  sorry
                | congrFun h =>
                  sorry
              | congrArg h =>
                rename_i x' _
                have h_dec := RedAff.instRedRel.decreasing h
                let h_t' := h_t.preservation (.congrFun (.congrArg h))
                exact refl_ty_heq (env := x') h_t'
        | inr h =>
          have ⟨C, h₁, h₂⟩ := h
          cases h₁ with
          | pi h =>
            cases h with
            | pi' h =>
              cases h with
              | quot h =>
                cases h with
                | pi' h =>
                  cases h
      | inr h =>
        sorry
termination_by env.size

/-
refl(f_α) env x
-/
theorem refl_ty_heq (h_t : Judge (DCC (refl(f_α) env x)) (DCC x = y)) : x = y := by
  match h_t with
  | .app (.app (.refl h_t_f_α h_r_refl_ty) h_r_α h_t_env h_r') h_r'' h_t_x ⟨h_r_xy₁, hn₁, h_r_xy₂, hn₂⟩ =>
    --dcc_simp_all (! !)
    match h_r_refl_ty with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      cases hr₁.cases_head with
      | inl h =>
        cases h
        dcc red !  aff
        dcc_aesop!
        dcc red !  eta
        
        sorry
      | inr h =>
        sorry
    /-cases h_r_xy₂ with
    | tail ih h => cases h; rfl
    | refl =>
      dcc red ! aff
      dcc_aesop!
      cases a
      
      sorry-/

/-theorem refl_ty_heq (h_t : Judge (DCC (refl(f_α) env x)) (DCC x = y)) : x = y := by
  cases h_t with
  | app h_t_f h_r_α h_t_x h_r_τ =>
    cases h_t_f with
    | app h_t_f' h_r_α' h_t_x' h_r_τ' =>
      cases h_t_f' with
      | refl a b =>
        match h_r_τ' with
        | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
          cases hr₁ with
          | single h =>
            sorry
          | tail h ih =>
            
            sorry-/
          /-cases hr₁ using Relation.TransGen.head_induction_on with
          | single h =>
            cases h
            sorry
          | head h hr₂ =>
            cases h with
            | congrFun h =>
              cases h with
              | quot =>
                cases hr₂ using Relation.TransGen.head_induction_on with
                | single h =>
                  sorry
                | head h hr₂ =>
                  cases h with
                  | congrFun h => cases h
                  | congrArg h =>
                    simp_all
                    cases hr₂ using Relation.TransGen.head_induction_on with
                    | single h =>
                      sorry
                    | head ha hb =>
                      cases ha with
                      | congrFun h => cases h-/
                      

-- IMPORTANT
-- somewhat easy
/-theorem refl_ty_heq (h_t : Judge (DCC (refl(f_α) env x)) (DCC x = y)) : x = y := by
  match h_t with
  | .app h_t_f h_r_α h_t_x h_r_τ =>
    match h_t_f with
    | .app h_t_f' h_r_α' h_t_x' h_r_τ' =>
      match h_t_f' with
      | .refl h_t_f_α h_r_refl =>
        dcc red ! aff
        dcc_aesop!
        cases a_30 with
        | refl =>
          cases a_28 with
          | single h => cases h
          | tail ih h =>
            cases a with
            | app h_t_refl _ _ _ =>
              cases h_t_refl with
              | refl =>
                cases h with
                | quot =>
                  
                  sorry
          /-
          cases a with
          | app h_t_refl b c d  =>
            dcc_aesop!
            cases h_t_refl with
            | refl =>
              
              sorry-/
        | tail ih h =>
          have ⟨f_α, env, heq⟩ := h.eq'
          cases heq
          cases h
          rfl-/

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
