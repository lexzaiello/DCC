import Dcc.Attrs
import Dcc.Ast
import Dcc.Aff.Size
import Dcc.Relation

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

/-
Sorts, ⊤, ⊥, ∗, and "combinators" that are no-op.
-/
inductive Atom : Expr → Prop
  | refl₀  : Atom (DCC refl(f_α))
  | refl₁  : Atom (DCC (refl(f_α) env))
  | refl₂  : Atom (DCC (refl(f_α) env x))
  | coup   : Atom (DCC Coup(f_β))
  | eq     : Atom (DCC (x = y))
  | top    : Atom (DCC ⊤)
  | tintro : Atom (DCC ∗)
  | bot    : Atom (DCC ⊥)
  | sort   : Atom (DCC Sort m)

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

inductive TyValue (P_pi : Expr → Prop) : Expr → Prop
  -- potentially sus IsNorm
  | pi     : P_pi f_β → Value env
    → TyValue P_pi (DCC (Π(f_α, f_β) env))
  | eq     : TyValue P_pi (DCC x = y)
  | top    : TyValue P_pi (DCC ⊤)
  | bot    : TyValue P_pi (DCC ⊥)
  | tintro : TyValue P_pi (DCC ∗)
  | sort   : TyValue P_pi (DCC Sort m)

end Expr

/-
For normalization by evaluation for η

Example:

α -> a
-------------------------------
Id(α) -> Lam (fun (x : α) => x)

Id(α) -> 

Use variables?

apps have an environment. This is either a couple or a neutral value.
-/



/-theorem Val.head_arity_lt_exp_size (h : Eval env e e') : Val.head_arity e' ≤ Val.size e' := by
  cases h
  any_goals grind
  case app f f' x x' h₁ h₂ h₃ =>
    
    sorry
  cases x
  case neut =>
    grind
  case lam arity bdy =>
    dcc_simp
    -/

/-@[aesop safe forward (rule_sets := [DccSize])]
theorem EvalCompound.size_eq (h : EvalCompound env x x') : Val.composite_size x' = (Expr.composite_size x) + x.head_arity := by
  cases h
  case boxed h =>
    dcc_simp_all
    have h := h.size_eq
    
    
    sorry-/

/-@[aesop safe forward (rule_sets := [DccSize])]
theorem Eval.size_eq (h : Eval _env x x') : Val.composite_size x' = (Expr.composite_size x) + x.head_arity := by
  cases h with
  | compound =>
    sorry
  | simple h =>
    exact h.composite_size_eq-/

/-@[aesop safe forward (rule_sets := [DccSize])]
theorem Eval.size_eq (h : Eval _env e v) : v.composite_size ≤ e.composite_size := by
  induction e generalizing v
  case sigma ih₁ ih₂ | pair ih₁ ih₂ ih₃ | comp₂ ih₁ ih₂ | comp ih₁ ih₂ | comp' ih₁ ih₂ | fstc ih
    | sndc ih | eql ih | eq ih₁ ih₂ | refl _ _ _
    | eval _ _ _ | unbox ih | box ih | bang ih
    | coup ih₁ | mkc ih₁ ih₂ ih₃ | pi ih₁ ih₂
    | curr ih₁ ih₂ ih₃ | map ih₁ | fmap ih₁
    | curr' ih₁ ih₂ ih₃ | quot ih₁ ih₂ | id ih₁
    | top | bot | tintro | sort =>
      focus
      cases h
      · first
        | grind
        | (rename_i h
           first
           | have h := ih h
             grind
           | grind
           | (have ha := ih₁ (by assumption)
              grind)
           | (have ha := ih₁ (by assumption)
              have hb := ih₂ (by assumption)
              grind)
           | (have ha := ih₁ (by assumption)
              have hb := ih₂ (by assumption)
              have hc := ih₃ (by assumption)
              grind))
  case app ih₁ ih₂ =>
    cases h with
    | app hf hx happ =>
      have ha := ih₁ (by assumption)
      have hb := ih₂ (by assumption)
      have hc := happ.decreasing
      grind-/

/-theorem ApplyCompound.decreasing (h : ApplyCompound f x e') : e'.size < f.size + x.size + 1 := by
  cases h
  case map h₁ h₂ =>
    have ha := h₂.decreasing
    dcc_simp
    
    sorry-/

mutual

/-theorem Apply.decreasing (h : Apply f x e') : e'.size + e'.head_arity < f.size + x.size + f.head_arity := by
  cases h
  case fmap env h₁ h₂ =>
    dsimp [Val.head_arity, Val.size, Neutral.size, Expr.size]
    have h := h₁.size_eq
    have h₂ := h₂.decreasing
    
    simp_all
    
    grind
  case map env h₁ h₂ =>
    sorry
  case unbox =>
    grind
  case pair h₁ h₂ h₃ h₄ h₅ =>
    have ha := h₁.size_eq
    have hb := h₂.size_eq
    have hc := h₃.decreasing
    have hd := h₄.decreasing
    have he := h₅.decreasing
    dsimp [Val.size, Neutral.size, Expr.size]
    grind
  case eval h₁ h₂ h₃ =>
    have ha := h₁.size_eq
    have hb := h₂.decreasing
    have hc := h₃.decreasing
    dsimp [Val.size, Neutral.size, Expr.size]
    grind
  case quot h =>
    have ha := h.size_eq
    dsimp [Val.size]
    grind
  case sndc | fstc | id => grind
  case comp h₁ h₂ h₃ h₄ | comp₂ h₁ h₂ h₃ h₄ | comp' h₁ h₂ h₃ h₄ =>
    have ha := h₁.size_eq
    have hb := h₂.size_eq
    have hc := h₃.decreasing
    have hd := h₄.decreasing
    dsimp [Val.size, Expr.size]
    grind
  case curr₁ =>
    dsimp [Val.size, Expr.size]
    -/

/-theorem Eval.size_eq (h : Eval _env e v) : e.size = v.size := by
  cases h
  any_goals (grind)
  case bang x x' h | boxed x x' h =>
    have h := h.size_eq
    simp [Val.size, Neutral.size, Expr.size]
    grind
  case coup h₁ h₂ h₃ =>
    
    sorry-/

end

/-@[aesop safe forward (rule_sets := [DccSize])]
theorem Eval.neut_size_leq (h : Eval _env e Val(neutral(v))) : v.size ≤ e.size := by
  cases h
  any_goals (grind)
  case t_coup h =>
    have h := h.size_eq
    grind
  case bang h =>
    have h := h.size_eq
    dsimp [Neutral.size, Expr.size]
    grind
  case boxed h =>
    have h := h.size_eq
    dsimp [Neutral.size, Expr.size]
    
    sorry
  case eq h₁ h₂ =>
    have ha := h₁.size_eq
    have hb := h₂.size_eq
    grind
  case coup h₁ h₂ =>
    have ha := h₁.size_eq
    have hb := h₂.size_eq
    grind
  case app h₁ h₂ h₃ =>
    have ha := h₁.size_eq
    have hb := h₂.size_eq
    have hc := h₃.decreasing
    simp [Val.size] at hc
    grind-/

/-def quote (v : Val) : Expr :=
  match v with
  | -/

end Val

end Semantic

namespace Expr

open Semantic

def eval (e : Expr) : Val :=


end Expr

/-
NbE η-reduction:

Check if 
-/
