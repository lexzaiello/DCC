import Dcc.Ast
import Dcc.Relation
import Dcc.Reduces
import Dcc.Metatheory.Congr

namespace Expr

abbrev Arity := ℕ

-- Combinators that can make a step with their well-typed arguments
-- with a list of their points
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
  | pair  : IsRedComb (DCC ⟦β⟧⟨f, g⟩) 1
  -- Λ(α, β, x) y z
  | curr  : IsRedComb (DCC Λ(α, β, x)) 2

theorem IsRedComb.is_norm_aff (h : IsRedComb e m) : IsNorm RedAff e := fun ⟨_, hr⟩ => by
  cases h <;> cases hr

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
  | pair  : IsRedCombApp (DCC ⟦β⟧⟨f, g⟩) 1
  -- Λ(α, β, x) y z
  | curr  : IsRedCombApp (DCC Λ(α, β, x)) 2
  | app   : IsRedCombApp f (m + 1) → IsRedCombApp (DCC (f x)) m

namespace Reduced

theorem head (hr : Reduced A D) : ∃ B C, RedEtaReflTrans C D ∧ RedAff A B ∧ (B = C ∨ RedAffTrans B C) ∧ IsNorm RedAff C ∧ IsNorm RedEta D := by
  match hr with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
    cases hr₁ using Relation.TransGen.head_induction_on with
    | single h => exact ⟨_, _, hr₂, h, .inl rfl, hn₁, hn₂⟩
    | head h ih => exact ⟨_, _, hr₂, h, .inr ih, hn₁, hn₂⟩

/-theorem Reduced.step_comb₁ (h_f : IsRedComb f 1) (h_r : Reduced (DCC (f x))) : ∃ e' e'',
  RedAff (DCC (f x)) e' ∧ RedAffReflTrans -/

end Reduced

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
  | coup   : Value f_β → Value (DCC Coup(f_β))
  | eq     : Value (DCC x = y)
  | comb   : IsRedComb c m → Value c
  | c_app  : IsRedComb f 2 → Value f → Value x → Value (DCC (f x))
  | top    : Value (DCC ⊤)
  | bot    : Value (DCC ⊥)
  | tintro : Value (DCC ∗)
  | sort   : Value (DCC Sort m)

inductive TyValue : Expr → Prop
  -- potentially sus IsNorm
  | pi     : IsNorm RedEta f_β → Value env
    → TyValue (DCC (Π(f_α, f_β) env))
  | eq     : TyValue (DCC x = y)
  | top    : TyValue (DCC ⊤)
  | bot    : TyValue (DCC ⊥)
  | tintro : TyValue (DCC ∗)
  | sort   : TyValue (DCC Sort m)

theorem Value.is_norm_aff (h : Value e) : IsNorm RedAff e := by
  induction h with
  | pi₁ h_val_f_β =>
    exact fun ⟨_, h⟩ => by cases h
  | pi₂ h_val_f_β h_val_env ih₁ ih₂  =>
    exact fun ⟨_, h⟩ => by
      cases h with
      | congrFun h => cases h
      | congrArg h =>
        exact (ih₂ ⟨_, h⟩).elim
  | refl₁ _ ih =>
    exact fun ⟨_, h⟩ => by
      cases h with
      | congrFun h => cases h
      | congrArg h =>
        exact (ih ⟨_, h⟩).elim
  | refl₂ h_val_f_β h_val_env ih₁ ih₂  =>
    exact fun ⟨_, h⟩ => by
      cases h with
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h =>
          exact (ih₁ ⟨_, h⟩).elim
      | congrArg h =>
        exact (ih₂ ⟨_, h⟩).elim
  | top | bot | tintro | sort => exact fun ⟨_, h⟩ => by cases h
  | coup _ ih =>
    exact fun ⟨_, h⟩ => by
      cases h with
    | coup h =>
      exact (ih ⟨_, h⟩).elim
  | eq => exact fun ⟨_, h⟩ => by cases h
  | comb h => exact h.is_norm_aff
  | c_app h_c_f h_val_f h_val_x ih₁ ih₂ =>
    cases h_c_f with
    | eql =>
      exact fun ⟨_, h⟩ => by
        cases h with
        | congrFun h => cases h
        | congrArg h => exact (ih₂ ⟨_, h⟩).elim
    | curr =>
      exact fun ⟨_, h⟩ => by
        cases h with
        | congrFun h => cases h
        | congrArg h => exact (ih₂ ⟨_, h⟩).elim

theorem TyValue.is_norm_aff (h : TyValue τ) : IsNorm RedAff τ := by
  induction h
  any_goals (
    focus
    intro ⟨_, h⟩
    cases h
    done)
  · intro ⟨_, h⟩
    cases h with
    | congrFun h => cases h
    | congrArg h =>
      rename_i h_v_env _
      exact h_v_env.is_norm_aff ⟨_, h⟩

theorem TyValue.is_norm_eta (h : TyValue τ) : IsNorm RedEta τ := by
  induction h
  any_goals (
    focus
    intro ⟨_, h⟩
    cases h
    done)
  · intro ⟨_, h⟩
    cases h with
    | pi hr hn_env hrt =>
      cases hrt with
      | pi' h =>
        rename_i h_norm_f_β _ _ _
        exact h_norm_f_β ⟨_, h⟩

theorem TyValue.red_eta (h : TyValue τ) (hr : RedEta τ τ') : False :=
  h.is_norm_eta ⟨_, hr⟩

theorem TyValue.red_aff (h : TyValue τ) (hr : RedAff τ τ') : False :=
  h.is_norm_aff ⟨_, hr⟩

theorem TyValue.reduces (h : TyValue τ) (hr : Reduces τ τ') : τ' = τ := by
  induction h with
  | pi =>
    have ⟨_, _, hr₁, hn₁, hr₂, hn₂, heq⟩ := hr.pi
    cases heq
    match hr₁.cases_head with
    | .inl h =>
      cases h
      match hr₂.cases_head with
      | .inl h =>
        cases h
        rfl
      | .inr ⟨_, h₁, h₂⟩ =>
        rename_i h_env_value _ _
        cases h_env_value.is_norm_aff.unique_refl (by assumption)
        rfl
    | .inr ⟨_, h₁, h₂⟩ =>
      rename_i h_n_β _ _ _ _
      exact (h_n_β ⟨_, h₁⟩).elim
  | tintro | sort | bot | top | eq =>
    match hr with
    | ⟨hr₁, hn₁, hr₂, hn₂⟩ =>
      match hr₁.cases_head with
      | .inl h =>
        cases h
        match hr₂.cases_head with
        | .inl h =>
          cases h; rfl
        | .inr ⟨_, h₁, h₂⟩ =>
          cases h₁
      | .inr ⟨_, h₁, h₂⟩ =>
        cases h₁

end Expr
