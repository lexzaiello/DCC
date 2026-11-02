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

namespace Expr

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def size (e : Expr) : ℕ :=
  match e with
  | DCC ∗ => 1
  | DCC 𝟙 => 1
  | DCC 𝟘 => 1
  | DCC (= A x y) => (A.size + x.size + y.size) + 1
  | DCC (? m) => m.size.succ
  | DCC 𝟙₂ => 1
  | DCC 𝟘₂ => 1
  | DCC 𝟚 => 1
  | DCC (𝟚.Rec motive x y) => motive.size + x.size + y.size + 1
  | DCC (𝟘.Rec motive) => motive.size + 1
  | DCC (Eql α)  => α.size + 2
  | DCC (=' α)  => α.size + 2
  | DCC (refl α) => α.size + 1
  | DCC Sort _m => 1
  | DCC (Σ α β) => α.size + β.size + 1
  | DCC (Σ' α β) => α.size + β.size + 1
  | DCC (`β x) => β.size + x.size + 1
  | DCC (,β x y) => β.size + x.size + y.size + 1
  | DCC (Id α)      => α.size + 1
  | DCC (Fst β)    => β.size + 1
  | DCC (Snd β)    => β.size + 1
  | DCC (Swap B C)    => B.size + C.size + 2
  | DCC (Π α β) => α.size + β.size + 1
  | DCC (∘ f g)  => f.size + g.size + 1
  | DCC (⟨,⟩β a b)   => 3 * (β.size + a.size + a.size + b.size + 3)
  | DCC (!Λ α β x) => (α.size * 2) + (6 * (β.size + 1)) + (x.size * 2) + 5
  | DCC (Λ α β x) => α.size + β.size + x.size + 2
  | DCC (Eval α β x) => α.size + β.size + x.size + 1
  | DCC (!x)   => x.size + 1
  | DCC (*x)   => x.size + 1
  | DCC (&x)   => (x.size * 5) + 1
  | DCC (!<> x)   => x.size + 2
  | DCC ($<> x)   => (x.size * 5) + 1
  | DCC (f x) => f.size + x.size
  | .hole _ => 1

@[grind .]
theorem size_pos : 0 < size e := by
  induction e <;> grind

@[grind .]
theorem point_size_lt : size ((Expr.points e).get n) < size e := by
  induction e
  any_goals (
    fin_cases n <;>(simp [points, Vector.get, size]; grind))
  any_goals (simp [points, Vector.get, size])

@[grind .]
theorem point_size_lt' : size ((Expr.points e).get ⟨n, h⟩) < size e := point_size_lt (n := ⟨n, h⟩)

theorem set_point_size_lt (h : n < point_arity e) (heq : Fin.mk n h = n₀) (hlt : p'.size < (e.points.get (Fin.mk n h)).size) : size (set_points e ((Expr.points e).set n p' h)) < e.size := by
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

/-
@[grind .]
theorem point_size_lt : size ((Expr.points e).get n) < size e := by
  induction e
  any_goals (
    fin_cases n <;>(simp [points, Vector.get, size]; grind))
  any_goals (simp [points, Vector.get, size])

@[grind .]
theorem point_size_lt' : size ((Expr.points e).get ⟨n, h⟩) < size e := point_size_lt (n := ⟨n, h⟩)

theorem set_point_size_lt (h : n < point_arity e) (heq : Fin.mk n h = n₀) (hlt : p'.size < (e.points.get (Fin.mk n h)).size) : size (set_points e ((Expr.points e).set n p' h)) < e.size := by
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
-/

end Expr
