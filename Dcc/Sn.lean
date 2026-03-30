import Dcc.Ast2
import Dcc.Eval2
import Dcc.EvalTm
import Dcc.Judge2
import Dcc.Tactic

/-
Notes:
- Can use lexicographic ordering to allow ⟨a, b⟩ x = (a x, b x) copying.
- Unification algorithm to convert untyped into typed. Massive plus for readability, and we can in our SN proof say "Unif τ₁ τ'₁" before Judge.
- 
-/

theorem Expr.Reduces.IsNorm (h : Expr.Reduces a b) : b.IsNorm :=
  match h with
  | ⟨_, h⟩ => h

theorem Expr.Reduces.unique (h₁ : Expr.Reduces a b) (h : a.IsNorm) : a = b := by
  cases h₁
  rename_i h_red h_norm
  exact (h_red.unique h).symm

theorem Expr.Reduces.unique' (h₁ : Expr.Reduces a b) (h₂ : Expr.Reduces a c) : b = c := by
  cases h₁
  cases h₂
  rename_i ha _ _ _
  exact ha.unique' (by assumption) (by assumption) (by assumption)

--theorem IsNorm.decreasing (h : IsNorm e) :

theorem Expr.Reduced.unique (h : Expr.Reduced a b) (h_norm : a.IsNorm) : a = b := by
  cases h
  rename_i h _
  change Relation.ReflTransGen Expr.RedTy _ _ at h
  rw [← Relation.reflGen_transGen] at h
  induction h
  · rfl
  · rename_i h _
    change Expr.RedTyTrans _ _ at h
    exact (h.unique (by assumption)).symm

theorem Expr.Reduced.unique' (h₁ : Expr.Reduced a b) (h : Expr.Reduced a c) : b = c := by
  cases h₁
  cases h
  rename_i ha _ hb _
  exact ha.unique (by assumption) (by assumption) (by assumption)

theorem Expr.Reduceds.unique' (h₁ : Expr.Reduces a b) (h : Expr.Reduces a c) : b = c := by
  cases h₁
  cases h
  rename_i ha _ hb _
  exact ha.unique' (by assumption) (by assumption) (by assumption)

theorem Expr.Reduced.decreasing (h : Expr.Reduced a b) : b.ty_size < a.ty_size ∨ a = b := by
  cases h
  rename_i h_refl h_norm
  change Relation.ReflTransGen Expr.RedTy _ _ at h_refl
  rw [← Relation.reflGen_transGen] at h_refl
  induction h_refl
  exact .inr rfl
  · rename_i b' h_red
    change Expr.RedTyTrans _ _ at h_red
    exact .inl h_red.decreasing'

theorem Expr.Projects.unique (h₁ : Expr.Projects π a b) (h₂ : Expr.Projects π a c) : b = c := by
  induction h₁
  repeat {
    cases h₂
    rename_i hreda _ hred' _ _ hredb hred''
    have h := hreda.unique' (by assumption)
    simp_all
    exact hred'.unique' (by assumption)
  }

theorem Judge.unique (h₁ : Judge t₁ e) (h₂ : Judge t₂ e) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | s | k' | k => cases h₂; rfl
  | srt => cases h₂; rfl
  | lense | coupe | paire =>
    cases h₂
    · rename_i h _
      cases h
      rename_i h _ _
      cases h
    rfl
  | app h_t_f h_red_α h_j_x h_deq =>
    rename_i ih₁ ih₂
    cases h₂ with
    | lense | coupe | paire =>
      cases h_t_f
      rename_i h _
      cases h
    | app h_t_f' h_red' h_x' =>
      have ha := ih₁ (by assumption)
      have hb := ih₂ (by assumption)
      simp_all only

theorem RedTm.ty_decreasing (h_red : Expr.RedTm e e') (h_t : Judge t e) (h_t' : Judge t' e') : t'.ty_size < t.ty_size := by
  induction h_red generalizing t t' with
  | k =>
    repeat judge_cases_spine
    rename_i h _ _ _
    cases h
    rename_i h _
    cases h
    rename_i h
    cases h
    rename_i h _
    cases h
    rename_i h _
    cases h
    rename_i h _
    cases h
    
  | _ => sorry
