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
  | DCC[.] (Dup B x) => ((B.size + 1) * 3) + x.size + 1
  | DCC[.] (Map A B x y) => A.size + B.size + x.size + y.size + 3
  | DCC[.] (Assoc A B C) => 2 * (2 * (A.size + 1) + 2 * (B.size + 1)+ 2 * (C.size + 1) + 7)
  | DCC[.] ∗ => 1
  | DCC[.] ⊤ => 2
  | DCC[.] ⊥ => 2
  | DCC[.] (= A x y) => (A.size + x.size + y.size) + 1
  | DCC? (? m) => m.size.succ
  | DCC? True => 1
  | DCC? False => 1
  | DCC? Bool => 1
  | DCC? (Bool.Rec motive x y) => motive.size + x.size + y.size + 1
  | DCC? (⊥.Rec motive) => motive.size + 1
  | DCC[.] (Eql α)  => α.size * 80 + 17
  | DCC[.] (refl α) => α.size * 2 + 5
  | DCC[.] Sort _m => 3
  | DCC[.] (Σ α β) => α.size + β.size + 1
  | DCC[.] (`β x) => β.size + x.size + 1
  | DCC[.] (,β x y) => β.size + x.size + y.size + 1
  | DCC[.] (Id α)      => α.size + 1
  | DCC[.] (Fst β)    => β.size + 2
  | DCC[.] (Snd β)    => β.size + 2
  | DCC[.] (Swap B C)    => (B.size + 1) + (C.size + 1) * 5
  | DCC[.] (Π α β) => 10 * ((100 * (α.size + 5)) + (100 * (β.size + 5)))
  | DCC[.] (∘ f g)  => f.size + f.size + g.size + 3
  | DCC[.] (⟨,⟩β a b)   => 3 * (β.size + a.size + a.size + b.size + 3)
  | DCC[.] (Λ α β x) => (α.size * 2) + β.size * 2 + (x.size * 2) + 3
  | DCC[.] (!Λ α β x) => (α.size * 2) + (6 * (β.size + 1)) + (x.size * 2) + 5
  | DCC[.] (Eval α β x) => α.size + β.size + x.size + 4
  | DCC[.] (!x)   => x.size + 1
  | DCC[.] (*x)   => 10 * x.size + 4
  | DCC[.] (&x)   => (5 * x.size) + 1
  | DCC[.] (!<> x)   => x.size + x.size + x.size + 4
  | DCC[.] ($<> x)   => 5 * x.size + 4
  | DCC[.] (f x) => f.size + x.size
  | .const _ => 0
  | .hole _ => 0

theorem point_size_lt (h : Points e l) : (l.get n).size < e.size := by
  cases h <;> grind

/-
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
-/

end GenericExpr
