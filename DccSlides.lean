import VersoSlides
import Verso.Doc.Concrete
import Dcc.Types
import Dcc.Compile

open VersoSlides

#doc (Slides) "Dependent Categorical Combinators" =>

# The Dependent Categorical Combinators (DCC)

Lexi Aiello

# DCC is the Rust of dependent type theory

# DCC is the Rust of dependent type theory:

- Based on categorical combinators
  - No variables, no contexts - all combinators
- No duplication allowed
  - Duplication is explicit via reference counting (a la Rust, linear logic)
- Strongly-normalizing
  - Wicked fast type-checker
  - Types are canonical
  - *Extensional* - $`x = y \iff x \equiv y`

# DCC is the Rust of dependent type theory:

:::fragment
Type-checking is decidable
:::

# Type-checking is decidable

In DCC, a judgment is valid iff the type-checker can infer it (usually impossible for DTT):

```leanLibCode Dcc.Metatheory.Decidability (startLine := 32) (endLine := 33)
theorem Judge.complete (h : Judge e t) : infer e = .some ⟨t, ⟨h⟩⟩ := by
  induction h <;> (dsimp only [infer]; (try (dcc_simp_all; dcc_aesop!)); try grind)
```

# Type-checking is decidable

```leanLibCode Dcc.Metatheory.Decidability (startLine := 39) (endLine := 46)
instance : Decidable (Judge e t) :=
  if h : (infer e).isSome then
    if heq : ((infer e).get h).fst = t then
      .isTrue (heq ▸ ((infer e).get h).snd.down)
    else
      isFalse (fun h => by simp [h.complete] at *)
  else
    isFalse (fun h => by simp [h.complete] at *)
```

# DCC is the Rust of dependent type theory:

- Avoid reasoning about duplication
:::fragment
- Dead-simple def. eq.: just reduce both types
  - Type-checking is *fast* (21 ms. to compile + type-check a small Lean program to DCC deep embedding)
:::

# DCC is the Rust of dependent type theory:
:::fragment
- Avoid reasoning about duplication
  - Just run the rewrite rules *literally* on the AST
    - Sound + complete beta-reducer
- End-to-end verified type-checker and Lean → DCC compiler
:::

# Example: Writing DCC Programs in Lean

```lean
#time #eval dcc_infer (fun (α : Sort 0)
  (x : α) => x) True True.intro
```

- ~20ms to compile (compiler itself type-checks parts of expr) + infer in deep embedding
- Users write normal Lean code
- Compiles to variable-free, combinatory program

# Example: Writing DCC Programs in Lean

```lean -panel
#eval dcc_compile (fun (α : Sort 0)
  (x : α) => x) True True.intro
```

- Users write normal Lean code
- Compiles to variable-free, combinatory program

# Example: Reference Counting

```lean -panel
#time #eval dcc_infer (((fun (x : *(Sort 1)) =>
  (fun (x : Sort 1) => x) ↑(x))) &(Sort 0))
```

- User indicates a cloneable resource with `&(x)`
- Compiled program has application under a $`\lambda`
  - Requires cloning the context
  - Constrained and tracked via reference counting

# Example : Reference Counting

```lean -panel
#eval dcc_compile (((fun (x : *(Sort 1)) =>
  (fun (x : Sort 1) => x) ↑(x))) &(Sort 0))
```

# Example: Reference Counting

- Pair rule (as in cat. combinators) requires argument is boxed as clonable
  - Pair downgrades cloneable box to non-clonable term
  - Boxes count their contents three times in size measure
- Not all operations require cloning (e.g., previous slide)

# Example: Reference Counting

- Strong normalization *for free* (simple syntactic size measure)
  - Eager normalization - types are canonical
  - Extensional reflection rule for propositional equality
- Rust-like resource management
  - No reasoning about duplication - wicked fast type-checker

# Inference rule: reference counting

$$`
\begin{gathered}
\frac{x : A}{\&(x) : !(A)} \\
\llbracket \beta \rrbracket \langle M, N \rangle \&(x) \rightarrow \llbracket \beta \rrbracket ((M x), (N x (M x)))
\end{gathered}
`

- The $`!(A)` modality is taken from linear / affine logic
- Argument must be cloneable → downgraded to non-cloneable by pair dup.

# Size measure: pair

$$`
\begin{gathered}
\frac{}{size(\&(x)) = 3 \cdot size(x) + 1}\\
\frac{}{size(f x) = size(f) + size(x)}\\
\frac{}{size(\llbracket \beta \rrbracket \langle M, N \rangle) = 2 \cdot size(M) + size(N) + 2} \\
\frac{}{size(\llbracket \beta \rrbracket (x, y)) = size(x) + size(y)}
\end{gathered}
`

# Size measure: pair

$$`
\begin{align*}
size & (\llbracket \beta \rrbracket \langle M, N\rangle \&(x)) =\\
  & (2 \cdot size(M) + size(N) + 2) \\
  & + (3 \cdot size(x) + 1) \\
size & (\llbracket \beta \rrbracket ((M x), (N x (M x)))) = \\
  & (size(M) + size(x)) \\
  & + (size(N) + size(x) + (size(M) + size(x))) \\
size & (\llbracket \beta \rrbracket \langle M, N \rangle \&(x))
  & > size(\llbracket \beta \rrbracket ((M x), (N x (M x))))
\end{align*}
`

# Inference rule: pair

$$`
\frac{f : \Pi(x : A), B x \quad g : \Pi(x : A) (y : B x), C x y}{
\llbracket C \rrbracket \langle f, g \rangle : \Pi (x : !(A)), \Sigma (a : B (*(x))), C (*(x)) a}
`

# DCC is *Extensional* and *Decidable*

# The Payoff: Decidable Extensional Type-Checking

$$`\frac{\Gamma \vdash M : A \quad A =_{\beta} B \quad \Gamma \vdash B : K}{\Gamma \vdash M : B}`

_Figure: the usual judgmental conversion constructor._

DCC has no conversion constructor. There is exactly one (literally, not definitionally) valid type for each term.

# The Payoff: Decidable Extensional Type-Checking

This is the inference rule for $`refl` in Martin-Lof Type Theory. $`refl` is the only constructor of propositional equality in MLTT.

$$`
\frac{}{refl : \Pi (a : A), a = a}
`

# The Payoff: Decidable Extensional Type-Checking

$$`
\frac{}{refl : \Pi (a : A), a = a}
`

Due to the conversion constructor, $`refl` could type-check as multiple types.
E.g., if $`x` and $`y` reduce to the same thing in $`x = y`.

# The Payoff: Decidable Extensional Type-Checking

$`refl` is the constructor for $`=` in DCC, but we have no general conversion constructor.
Refl's type is normalized *fully* before it becomes a valid judgment.

# The Payoff: Decidable Extensional Type-Checking

In DCC, $`x = y` iff $`x` and $`y` are literally, syntactically the same.

# The Payoff: Decidable Extensional Type-Checking

```leanLibCode Dcc.Metatheory.ReflCanon (startLine := 457) (endLine := 469) -panel
theorem elim_eq (h : Judge e (DCC (x = y))) : x = y := by
  induction e using RedAff.instRedRel.wellFounded.induction with
  | h e ih =>
    have h₀ := h
    cases h
    case app h_t_f h_r_α h_t_x h_r_x_α ih₂ =>
      match h₀.progress with
      | .inl v =>
        have ⟨f_α, env, x', env'', x'', heq, hr⟩ := h₀.eq_val_is_refl v
        exact (heq ▸ h₀).refl_ty_heq
      | .inr ⟨e', hr⟩ => exact ih _ hr (h₀.preservation (by assumption))
    case coup _ _ h => exact (Reduces.no_sort_eq (by assumption)).elim
    all_goals (exact (Reduces.no_pi_eq (by assumption)).elim)
```

# Contribution

## Affine Types: Normalization for Free in DTT

Formalizing a dependent type theory is challenging because *computations can appear in types*.

$$`\frac{\Gamma \vdash M : A \quad A =_{\beta} B \quad \Gamma \vdash B : K}{\Gamma \vdash M : B}`

In the _Calculus of Constructions_, if $`A` has type $`B` and $`C` is def-eq. ($`=_{\beta}`) $`B`, then $`A : C`.

# Example: Types Can Contain Computations

```lean -panel
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

```lean -panel
#check_failure (λ x => x x) (λ x => x x)
```

# Strong-Normalization

Strong normalization says that there is *no infinite series of reductions* on some object with respect to a relation. It is defined in Mathlib:

```lean -panel
/--
`Acc r x` means that `x` is accessible through `r`:

`x` is accessible if there exists no infinite sequence
  `... < y₂ < y₁ < y₀ < x`.
-/
inductive Acc' {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : (y : α) → r y x → Acc' r y) : Acc' r x
```

# Strong-Normalization

Lean knows a program will terminate if it follows the typing rules.

```lean -panel
variable (MyExpr : Type) (MyJudge : MyExpr → MyExpr → Prop)
  (StepsTo : MyExpr → MyExpr → Prop)
-- If an expression is well typed at t, then there is
-- no infinite sequence of reductions.
theorem sn_typed {e t : MyExpr} (ht : MyJudge e t) :
  Acc (fun a b => StepsTo b a) e := by
  sorry
```

# Problem: The Meta-Theoretical Ouroboros

To prove strong-normalization, you usually need to prove theorems about type-checking:

- Preservation: if $`M : A` and $`M \rightarrow N`, then $`N : A`
- Progress: if $`M : A`, then $`\exists N, M \rightarrow N`

Among others...

# Problem: The Meta-Theoretical Ouroboros

- Types can contain computations, so proofs need to handle *conversion* (def. eq)
  - Requires very complex machinery
- Automating conversion requires an algorithm to reduce expressions
  - Requires *strong-normalization* ⟺ requires meta-theory proofs (*cycle*)

# Definitional Equality is Complicated: Lean4Lean

Lean4Lean is a formalization of Lean's metatheory in Lean. It defines definitional equality in a 67-line inductive.

# Def-eq / conversion: Lean4Lean

```
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

I side-step these issues altogether by restricting my types affinely
===================================================================

Similar to how Rust's type-system works. Objects in the type context₁ can never be duplicated.
They can be _moved_, like in Rust, but never duplicated.

- ₁Combinators have no contexts

I side-step these issues altogether by restricting my types affinely
===================================================================

Notes on notational shorthand when discussing DCC inference rules:
- $`\forall (x : A)` is notational shorthand (using variables) for an actual $`\Pi` DCC expression (without variables) that couldn't fit on the screen
- $`A \rightarrow B` is also shorthand for a macro defined to be a `\Pi` expression in DCC
- $`\rightarrow_{\beta}` indicates affine-eta reduction to a normal form

I side-step these issues altogether by restricting my types affinely
===================================================================

To illustrate, here are my inference rules for $`\Pi` and application:

:::hstack
$$`
\frac{f_{\alpha} : \delta \rightarrow \text{Sort}\ m \quad f_{\beta} : \forall (s : \delta) (x : f_\alpha s), \text{Sort}\ n}
{\Pi(f_\alpha, f_\beta) : \delta \rightarrow \text{Sort}\ max(m, n)}
`

$$`
\frac{f : \Pi (f_\alpha, f_\beta) x_\alpha, f_{\alpha} x_{\alpha} \rightarrow_{\beta} \alpha, \quad x : \alpha, \quad f_\beta x_\alpha \rightarrow_{\tau}}
{f x : \tau}
`
:::

I side-step these issues altogether by restricting my types affinely
--------------------------------------------------------------------

App rule in Lean:

```lean
/- !hide -/
open Expr
-- !end hide
inductive Judge'' : Expr → Expr → Prop
  | app    : Judge'' f (DCC (Π(f_α, f_β) x_α))
    → Reduces (DCC (f_α x_α)) α
    → Judge'' x α
    → Reduced (DCC (f_β x_α x)) τ
    → Judge'' (DCC (f x)) τ
```

I side-step these issues altogether by restricting my types affinely
--------------------------------------------------------------------

$`\Pi` rule in Lean:


```lean
/- !hide -/
open Expr
-- !end hide
inductive Judge' : Expr → Expr → Prop
  | pi     : Judge' f_α (DCC ((α : Sort m) → Sort n))
    → Judge' f_β (DCC (Π(Id(Sort m),
      `(Sort m,
        Π(f_α, Λ(α, f_α,
          `(Coup(f_α), Sort o))))) α))
    → Reduces (DCC (α : Sort m) → Sort o) τ
    → Judge' (DCC Π(f_α, f_β)) τ
```

# Existing Solution: Normalization by Evaluation (NbE)

:::table
*
  * *Deep embedding* (AST in Lean)
  * *Semantic model* (e.g., actual Lean functions)
:::

# Existing Solution: Normalization by Evaluation (NbE)

:::table
*
  * *Deep embedding* (AST in Lean)
  * *Semantic model* (e.g., actual Lean functions)
*
  * Reification ➡️
  * ⬅️ Reflection
:::

# Existing Solution: Normalization by Evaluation (NbE)

:::table
*
  * *Deep embedding* (AST in Lean)
  * *Semantic model* (e.g., actual Lean functions)
*
  * Reification ➡️
  * ⬅️ Reflection
*
  * `MyExpr.Lam` becomes `fun abc => xyz`
  * Reduce term, convert back to `MyExpr`
:::

# Contribution

Affine restriction: a new(?) technique to *automate conversion*

- Restrict term reduction in types to the "affine fragment" (terms that decrease in size)
  - Get strong normalization in types for free
  - Decidable type-checking
- This technique is practically applicable (specifically in categorical combinators)
  - Probably other combinatory logics, too

# Contribution 1

- Technique is quite obvious and requires far less boilerplate than NbE
  - Works with the deep embedding directly, not appealing to denotational semantics

# Contribution 1

- I show that all the types you need can be expressed using rules that are *guaranteed to decrease in size*.
  - Strong normalization proof is dead-simple:
    - Just do `termination_by e.ty_size` and recurse in `Acc` proof.
  - Further proofs (e.g., preservation, progress) can automate conversion with a function `reduce`
    - Avoid hundreds of lines of induction

# Practically applicable

Since I have an *algorithm to reduce expressions*:

- Type-checking is deterministic
- Type-checking is decidable
  - A judgment $`e : t` is valid iff it is inferred by the type-checker
- All formalized in Lean

# Practically applicable

My work builds off an existing theory: the simply-typed categorical combinators.

- I extend them with dependent types
- Cat. combinators have theoretical performance advantages as a $`λ`-calculus compilation target
- Compiler from Lean (minus inductive types) to my dependently-typed combinators in < 100 lines of Lean

# Practically applicable

A formalization of this scale in Lean requires very carefully constructed abstraction and boilerplate:
- Of practical interest to others doing metatheory in proof assistants
- Extensive use of tactic and typeclass automation
  - Proof of completeness is *1 line of Lean*

# The Categorical Combinators

$$`
\begin{array}{l l l}
&(ass) & (x \circ y) z = x(y z) \\
&(fst) & Fst(a, b) = a \\
&(snd) & Snd(a, b) = b \\
&(dpair) & \langle x, y\rangle z = (x z, y z) \\
&(curr) & \Lambda(x)yz = x(y, z) \\
&(app) & App(f, x) = f x \\
&(quote) & '(x) y = x
\end{array}
`

# The Categorical Combinators

- Model cartesian closed categories (categorical semantics of simply-typed $`\lambda`-calculus) literally
- Theoretical performance advantages: original compilation target of OCaml
- Have been extended to simply-typed before (Curien, "Categorical combinators")

# The Categorical Combinators

- Variables are modeled as nested tuples:
$$`
\Lambda(Fst) x y = x \approx (\lambda x. \lambda y. x) x = x
`

# The Dependent Categorical Combinators

- Instead of modeling untyped variables, I model *contexts*:

$$`
x_0 : A_0, x_1 : A_1(x_0), x_2 : A_2 (x_0, x_1) \approx \\
  \llbracket \Sigma(A_1), A_2 \rrbracket (\llbracket A_1 \rrbracket (x_0, x_1), x_2)
`

# The Dependent Categorical Combinators

- Instead of modeling untyped variables, I model *contexts*:

$$`
\frac{x : \Pi (x : \Sigma (x : A), B x), C x
}{\Lambda(A, B, x) : \Pi (x : A) (y : B x), C (\llbracket B \rrbracket (x, y))}
`

# The Dependent Categorical Combinators

- $`\Pi`'s domain and codomain depend on an environment (the context)

$$`
\frac{f_{\alpha} : \delta \rightarrow \text{Sort}\ m \quad f_{\beta} : \Pi (s : \delta) (x : f_\alpha s), \text{Sort}\ n}
{\Pi(f_\alpha, f_\beta) : \delta \rightarrow \text{Sort}\ max(m, n)}
`

# Demo: Lean Compiler

```lean -panel
#eval dcc_compile (fun (α : Sort 0) (x : α) => x) True True.intro
-- !fragment fadeUp
   #eval dcc_infer   (fun (α : Sort 0) (x : α) => x) True True.intro
-- !fragment fadeUp
```

# Demo: Lean Compiler

- Compiles raw Lean terms (`Lean.Expr`) into my combinators
- The entire compiler is 100 lines of code
- No book-keeping for contexts:
  - Since contexts can include terms (dependent), complex data structures are usually required just to compile
  - Context book-keeping is just a combinator `Expr`

# Demo: Lean Compiler

- Context book-keeping is just a combinator `Expr`

```leanLibCode Dcc.Compile (startLine := 30) (endLine := 51)
def Ctx := Expr
def Ctx.empty := DCC !(⊤)

def Expr.deref : Expr → Expr
  | DCC !(Γ) => Γ
  | Γ => Γ

def cc_var (ctx : Ctx) (idx : ℕ) : Option Expr :=
  match ctx, idx with
  | DCC Coup(β), .zero => pure <| DCC Sndc(β)
  | DCC !(Coup(β)), .zero => pure <| DCC Sndc(β) ∘' *(Coup(β))
  | DCC !(Coup(β)), .succ n => do
    match (← β.infer).fst with
    | DCC (Π(a, _b) x_α) =>
      (·.comp' (DCC (Fstc(β)) ∘' !(Coup(β)))) <$> cc_var (DCC (a x_α)).reduce_all n
    | _ => .none
  | DCC Coup(β), .succ n => do
    match (← β.infer).fst with
    | DCC (Π(a, _b) x_α) =>
      (·.comp' (DCC (Fstc(β)))) <$> cc_var (DCC (a x_α)).reduce_all n
    | _ => .none
  | _, _ => .none
```

# Demo: Type-Checker Performance

```lean
#time #eval Sigma.fst <$> (Expr.infer (DCC (Π(Id(Sort 1),
   `(Sort 1,
     Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))) ∘
         Fstc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))) ∘
       Fstc(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))), Sort 0))))
   Coup(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))), Sort 0)))))
```

# Demo / Theorem: Judgmental Completeness

In DCC, a judgment is valid iff the type-checker can infer it:

```leanLibCode Dcc.Metatheory.Decidability (startLine := 32) (endLine := 33)
theorem Judge.complete (h : Judge e t) : infer e = .some ⟨t, ⟨h⟩⟩ := by
  induction h <;> (dsimp only [infer]; (try (dcc_simp_all; dcc_aesop!)); try grind)
```

There is only one valid type.

# Demo / Theorem: Judgmental Completeness

```leanLibCode Dcc.Metatheory.Decidability (startLine := 32) (endLine := 33)
theorem Judge.complete (h : Judge e t) : infer e = .some ⟨t, ⟨h⟩⟩ := by
  induction h <;> (dsimp only [infer]; (try (dcc_simp_all; dcc_aesop!)); try grind)
```

This theorem is usually impossible for a dependent type theory. Since two types might be valid for the same expression (type conversion), inference is deterministic, but judgments are not. In the DCC, types are *canonical*, since I prove strong normalization *before* meta-theory.

# Theorem: Type-Checking is Decidable



# Principal Result: The Dependent Categorical Combinators have Affine Types

# Principal Result

$$`
\begin{array}{l l l}
&(ass) & (x \circ y) z = x(y z) \\
&(fst) & Fst(a, b) = a \\
&(snd) & Snd(a, b) = b \\
&(curr) & \Lambda(x)yz = x(y, z) \\
&(app) & App(f, x) = f x \\
&(quote) & '(x) y = x \\
&(dpair) & \langle x, y\rangle z = (x z, y z)
\end{array}
`

$`dpair` is the only rule that increases the size of the program.

# Principal Result

The types of the dependent categorical combinators, including $`dpair`, can be encoded *without invoking the $`dpair` rule*. DCC's types are *affine*. Each term in the type context is used *at most once* for each argument being checked.

# Principal Result

Since none of our primitive types invoke $`dpair`, our types are strongly-normalizing *by default*. The size of our types strictly decrease. I leverage this fact to prove decidability of type-checking.

# Principal Result

1. I define a very simple notion of "size" for an expression
2. I show the size decreases when the affine combinators reduce
3. I use my size measure as `termination_by` to prove SN and define a terminating reduction function
4. I show the reduction function produces normal forms

# Principal Result

5. Since the reduction function produces normal forms, I have determinism (Church-Rosser proven, but not necessary)
6. I use the reducer in my inference function
7. I avoid conversion *altogether* by reducing types to normal form eagerly in each judgment constructor
8. I use completeness + soundness of the reducer to show soundness + completeness of `infer`
9. *I show type-checking is decidable*

# Decidability is only possible due to the affine restriction

- Otherwise, conversion would require normalization by evaluation (NbE)
  - Unclear if decidability can be proven (would need completeness / soundness for reflection and reification)
- Affine restriction feels "elegant" (remove just 1 combinator, and you get decidability)

-- TODO: more inference rules to explain
-- TODO: inference rules are kind of the least important part
-- Size measure first
-- Go over inference rules quickly
-- Go over how we avoid conversion in judgment rule
-- Compare with parallel reduction or another with a general conversion constructor
