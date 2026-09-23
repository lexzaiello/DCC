import Dcc.Attrs
import Dcc.Ast
import Dcc.Ast.Points
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

open Dsl

/-
A measure of term size which decreases under the affine and eta reduction rules counted like such:

- AST terms which are combinators count themselves as an operation + 1
- Boxed terms are counted thrice, since pairs duplicate
  - ⟦β⟧⟨M, N⟩ &(x) = (M x, N x (M x))
- Computationally irrelevant points (e.g., type arguments) are also counted when
  they have relevance to eta reduction
- No terms have a size of zero, except injected constants (e.g., holes in eta reduction)
-/

namespace GenericExpr

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def size.{u} {τ : Type u} (e : GenericExpr τ) : ℕ :=
  match e with
  | DCC[.] (Dom x) => x.size
  | DCC[.] (Dom₂ x) => x.size * 2
  | DCC[.] (Unbang x) => x.size
  | DCC[.] (Uncoup x) => x.size
  | DCC[.] ∗ => 1
  | DCC[.] ⊤ => 2
  | DCC[.] ⊥ => 2
  | DCC[.] x = y => (x.size + y.size) + 1
  | DCC[.] A ≃ B => (A.size + B.size) + 1
  | DCC[.] (Unify τ_A τ_B X Y) => 5 * ((10 * (τ_A.size + 1)) + (10 * (τ_B.size + 1)) + (10 * (X.size + 1)) + (10 * (Y.size + 1)))
  | DCC? (? _m) => 1
  | DCC? True => 1
  | DCC? False => 1
  | DCC? Bool => 1
  | DCC? (≃.mk a b c d) => a.size + b.size + c.size + d.size + 1
  | DCC? (Bool.Ind motive x y) => motive.size + x.size + y.size + 1
  | DCC? (≃.Ind motive x) => motive.size + x.size + 1
  | DCC? (≃.1 x y) => x.size + y.size + 1
  | DCC? (≃.2 x y) => x.size + y.size + 1
  | DCC? (≃.3 x y) => x.size + y.size + 1
  | DCC? (≃.4 x y) => x.size + y.size + 1
  | DCC? (⊥.Ind motive) => motive.size + 1
  | DCC[.] (Eql α)  => α.size * 2 + 5
  | DCC[.] (refl α) => α.size * 2 + 5
  | DCC[.] Sort m => 3
  | DCC[.] (Σ α β) => α.size + (β.size + 1) * 6 + 5
  | DCC[.] (`β x) => β.size + x.size + 1
  | DCC[.] (,β x y) => β.size + x.size + y.size + 1
  | DCC[.] (Σ β) => β.size + 1
  | DCC[.] (Id α)      => α.size + 1
  | DCC[.] (Fst α)    => α.size + 2
  | DCC[.] (Snd α)    => α.size + 2
  | DCC[.] (Swap B C)    => (B.size + 1) + (C.size + 1) * 5
  | DCC[.] (Π α β) => α.size + β.size + 2
  | DCC[.] (∘ f g)  => f.size + f.size + g.size + 3
  | DCC[.] (⟨,⟩β a b)   => 3 * (β.size + a.size + a.size + b.size + 3)
  | DCC[.] (Λ α β x) => α.size + β.size * 2 + x.size + 3
  | DCC[.] (!Λ α β x) => α.size + (6 * (β.size + 1)) + x.size + 5
  | DCC[.] (Eval α β x) => α.size + β.size + x.size + 4
  | DCC[.] (!x)   => x.size + 1
  | DCC[.] (*x)   => 10 * x.size + 4
  | DCC[.] (&x)   => (5 * x.size) + 1
  | DCC[.] (!<> x)   => x.size + x.size + x.size + 4
  | DCC[.] ($<> x)   => 5 * x.size + 4
  | DCC[.] (f x) => f.size + x.size
  | .const _ => 0
  | .hole _ => 0

@[grind .]
theorem point_size_lt : size ((GenericExpr.points e).get n) < size e := by
  induction e
  any_goals (
    fin_cases n <;>(simp [points, Vector.get, size]; grind))
  any_goals (simp [points, Vector.get, size])

@[grind .]
theorem point_size_lt' : size ((GenericExpr.points e).get ⟨n, h⟩) < size e := point_size_lt (n := ⟨n, h⟩)

theorem set_point_size_lt (h : n < point_arity e) (heq : Fin.mk n h = n₀) (hlt : p'.size < (e.points.get (Fin.mk n h)).size) : size (set_points e ((GenericExpr.points e).set n p' h)) < e.size := by
  induction e
  any_goals (
    simp [point_arity] at h
    fin_cases n₀ <;> (
      cases heq
      simp [points, set_points, size]
      simp [points, Vector.get] at hlt
      grind))
  any_goals (
    cases heq
    simp [point_arity] at h)

end GenericExpr
