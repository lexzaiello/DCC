import Mathlib.Data.Nat.Notation

/-
Refactor notes:
- substitution I have been doing with ⊢ is cut elimination.

⊢ feels less ergonomic than I want it to be, and potentially dangerous.
(: T x) : Prop is quite nice and easy to traverse.

left of ⊢ are : Prop,
right of ⊢ is a function of the Props.

⊢ takes the consequent first.

⊢ α β : (α → β) → α → Prop

⊢ : (Prop → Prop → Prop) → Prop → Prop → Prop

⊢ fn_conclude hyp₁ hyp₂

minimal AST.

⊢, ∶, Prop, Ty, not sure if Pi is even necessary.

Pi is probably not necessary, Pi is just a ⊢ that judges a function
to have some codomain whatever with (∶ t_fn_app fn_app)

We won't actually have id, but this is what it would look like:

don't actually need fn_conclude.

⊢ : Prop → Prop → Prop.

just a sequence of judgments.
However, we need to be able to do things like β x.

⊢ should allow us to do function application.

⊢ α Type (∶ (α → Type) β) (∶ α x)

Summary: making ⊢ more well-typed.

⊢ allows application of judgements.

id : ⊢ Ty (⊢ ) judge_id (∶ Ty α)
^ we can make ⊢ dom accept prop instead of Ty for the domain.


⊢ : Prop → (Prop → Prop) judge_f judge_x

application β x:

⊢ α (const' Prop Prop (∶ (Type u.succ) Type u)) (∶ (α → Type u) β) (∶ α x)

id : 
-/

abbrev Universe := ℕ

inductive Expr where
  | judge : Universe → Expr
  | vdash : Universe → Universe → Expr
  -- S combinator
  | both  : Universe  → Universe → Universe → Expr
