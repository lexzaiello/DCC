import Mathlib
import VersoSlides
import Verso.Doc.Concrete
import Dcc.Ast
import Dcc.Judge

open VersoSlides

#doc (Slides) "Dependently-Typed Categorical Combinators" =>

# The Dependently-Typed Combinator Calculus

# Contribution

## Result ⟺ Practical Formalization Techniques

Formalizing a dependent type theory is challenging because *computations can appear in types*.


$$`\frac{\Gamma \vdash M : A \quad A =_{\beta} B \quad \Gamma \vdash B : K}{\Gamma \vdash M : B}`

In the _Calculus of Constructions_, if $`A` has type $`B` and $`C` is def-eq. ($`=_{\beta}`) $`B`, then $`A : C`.

# Example: Types Can Contain Computations

```lean
def ex : (if 1 == 1 then ℕ else ℝ) :=
--                              ^ !click
  .zero

#check ex
-- !fragment fadeUp
#check (fun (x : ℕ) => x) ex
-- !fragment fadeUp
```

# Problem: Type-checking runs programs (might not terminate)

Classic example: Omega combinator

```lean
#check_failure (fun x => x x) (fun x => x x)
-- !fragment fadeUp
```

# Strong-Normalization

Strong normalization is defined in Mathlib:

```lean
/--
`Acc` is the accessibility predicate. Given some relation `r` (e.g. `<`) and a value `x`,
`Acc r x` means that `x` is accessible through `r`:

`x` is accessible if there exists no infinite sequence `... < y₂ < y₁ < y₀ < x`.
-/
inductive Acc' {α : Sort u} (r : α → α → Prop) : α → Prop where
  /--
  A value is accessible if for all `y` such that `r y x`, `y` is also accessible.
  Note that if there exists no `y` such that `r y x`, then `x` is accessible. Such an `x` is called a
  _base case_.
  -/
  | intro (x : α) (h : (y : α) → r y x → Acc' r y) : Acc' r x
```

# Strong-Normalization

Strong normalization says that there is *no infinite series of reductions* on some object with respect to a relation.

Lean knows a program will terminate if it follows the typing rules.

```lean
variable (MyExpr : Type) (MyJudge : MyExpr → MyExpr → Prop) (StepsTo : MyExpr → MyExpr → Prop)
-- If an expression is well typed at t, then there is no infinite sequence of reductions.
-- Reduction will terminate
theorem sn_typed {e t : MyExpr} (ht : MyJudge e t) : Acc (fun a b => StepsTo b a) e := by
  sorry
```

# Problem: The Meta-Theoretical Ouroboros

To prove strong-normalization, you usually need to prove theorems about type-checking:

# Definitional Equality is Complicated: Lean4Lean

Lean4Lean is a formalization of Lean's metatheory in Lean. It defines definitional equality in a 67-line inductive.

# Def-eq / conversion: Lean4Lean

```leanLibCode Lean4Lean.Theory.Typing.Strong (startLine := 16) (endLine := 32)
inductive IsDefEqStrong : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → u.WF uvars → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    Γ ⊢ .sort l ≡ .sort l' : .sort (.succ l)
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    u.WF uvars →
    [] ⊢ ci.type.instL ls ≡ ci.type.instL ls' : .sort u →
    Γ ⊢ ci.type.instL ls ≡ ci.type.instL ls' : .sort u →
    Γ ⊢ .const c ls ≡ .const c ls' : ci.type.instL ls
```
