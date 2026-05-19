import Mathlib
import VersoSlides
import Verso.Doc.Concrete
import Dcc.Compile

open VersoSlides

#doc (Slides) "Dependent Categorical Combinators" =>

# The Dependent Categorical Combinators

Lexi Aiello

# Contribution

## Affine Restriction: A New(?) Technique for Normalization in DTT

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

```leanLibCode Lean4Lean.Theory.Typing.Strong (startLine := 16) (endLine := 32) -panel
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

```leanLibCode Dcc.Compile (startLine := 9) (endLine := 21)
def Ctx := Expr
def Ctx.empty := DCC ⊤
def cc_var (ctx : Ctx) (idx : ℕ) : Option Expr :=
  match ctx, idx with
  | DCC Coup(β), .zero => pure <| DCC Sndc(β)
  | DCC Coup(β), .succ n => do
    match (← β.infer).fst with
    | DCC (Π(a, _b) x_α) =>
      (·.comp' (DCC (Fstc(β)))) <$> cc_var (DCC (a x_α)).reduce_all n
    | _ => .none
  | _, _ => .none
```

# Demo: Type-Checker Performance

```lean
#time dcc_trace (Π(Id(Sort 1),
   `(Sort 1,
     Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))) ∘
         Fstc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))) ∘
       Fstc(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))), Sort 0))))
   Coup(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))), Sort 0)))
```

My type-checker inferred the types of *each* sub-expression in this tree in *52ms*. Somewhat impressive for a tree this size.

# Demo / Theorem: Judgmental Completeness

In DCC, a judgment is valid iff the type-checker can infer it:

```leanLibCode Dcc.Complete (startLine := 31) (endLine := 32)
theorem Judge.complete (h : Judge e t) : infer e = .some ⟨t, ⟨h⟩⟩ := by
  induction h <;> (dsimp only [infer]; try (simp_all [dcc_judge, dcc_reduce]; aesop (rule_sets := [DccReduce])))
```

# Demo / Theorem: Judgmental Completeness

```leanLibCode Dcc.Complete (startLine := 31) (endLine := 32)
theorem Judge.complete (h : Judge e t) : infer e = .some ⟨t, ⟨h⟩⟩ := by
  induction h <;> (dsimp only [infer]; try (simp_all [dcc_judge, dcc_reduce]; aesop (rule_sets := [DccReduce])))
```

This theorem is usually impossible for a dependent type theory. Since two types might be valid for the same expression, judgments are not deterministic. In the DCC, types are *canonical*, since I prove strong normalization *before* meta-theory.

# Theorem: Type-Checking is Decidable

```leanLibCode Dcc.Complete (startLine := 36) (endLine := 43)
instance : Decidable (Judge e t) :=
  if h : (infer e).isSome then
    if heq : ((infer e).get h).fst = t then
      .isTrue (heq ▸ ((infer e).get h).snd.down)
    else
      isFalse (fun h => by simp [h.complete] at *)
  else
    isFalse (fun h => by simp [h.complete] at *)
```

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
