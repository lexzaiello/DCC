# DCC - The Dependent Combinator Calculus

## Overview

The DCC is a dependently-typed calculus based on [SK combinators](https://en.wikipedia.org/wiki/SKI_combinator_calculus). My goal is to formalize a proof of strong normalization of the dependently-typed calculus.

## Background / Definitions

### SK Combinators

The [SK combinator calculus](https://en.wikipedia.org/wiki/SKI_combinator_calculus) is a turing complete model of computation equivalent to the lambda calculus. It has to equational / algebraic rewrite rules:

```
S x y z = (x z) (y z)
```

```
K x y = x
```

`S` is the driver of computation, since it duplicates the variable `z`, allowing infinite recursion.
Herein, we specifically refer to the *dependently typed* variant of SK. As such, we attach "type arguments:"

```
S α β γ x y z = (x z) (y z)
```

```
K α β x y = x
```

Rewrite rules are left unchaged. α and β are strictly information for the kernel.

### Dependent Types

Herein, when we refer to dependent types, we are specifically referring to [*pure* lambda calculi](https://en.wikipedia.org/wiki/Pure_type_system). We have an infinite hierarchy of sorts, and Π binders are the only mechanism of forming types (→ is created with Π and the `K` combinator).

Inductive types are out of the scope of this project. As such, an explicit notion of propositional equality is out of scope. Our ideal calculus is essentially the raw [Calculus of Constructions](https://en.wikipedia.org/wiki/Calculus_of_constructions), but without contexts or variables.

#### Type of S

We are using the standard definition of the `S` combinator's dependent type:

```lean
S : ∀ (α : Type) (β : α → Type) (γ : ∀ (x : α), β x → Type) (x : ∀ (x : α) (y : β x), γ x y) (y : ∀ (x : α), β x) (z : α), γ z (y z)
```

#### Type of K and K'

We also use the standard type of the `K` combinator, and have a special case of `K` called `K'` to close the "loop" of type dependency:

```lean
K : ∀ (α : Type) (β : α → Type) (x : α) (y : β x), α
```

```lean
K' : ∀ (α : Type) (β : Type) (x : α) (y : β), α
```

### All Objects in the Calculus

`S`, `K`, and `K'` are our only computationally relevant objects. All other objects are for forming types, though they can appear as terms, but have no rewrite rules accessible to the user:

| Object   | Purpose                                        | Rewrite Rule                    | Type                                                                                                     | Computationally Relevant?                   |
|----------|------------------------------------------------|---------------------------------|----------------------------------------------------------------------------------------------------------|---------------------------------------------|
| `S`      | Duplication and composition in computation     | `S x y z = (x z) (y z)`         | See above. Requires explicit type arguments `α`, `β`, `γ`.                                               | Yes                                         |
| `K`      | Weakening, dependent type                      | `K x y = x`                     | See above. Requires explicit type arguments `α`, `β`.                                                    | Yes                                         |
| `K'`     | Weakening, nondependent type                   | `K' x y = x`                    | See above. Requires explicit type arguments `α`, `β`.                                                    | Yes                                         |
| `Sort m` | Prevent self-type paradox                      | n/a                             | `⊢ Sort m : Sort m.succ`, `Prop` is shorthand for `Sort 0`                                               | No, cannot pattern match.                   |
| `Π`      | Form dependent types.                          | `((Π α, β) x) = Π (α x), (β x)` | `Γ x : α, β x : Sort m ⊢ Π α, β : Sort m`                                                                | No. Only kernel has access to rewrite rule. |
| `B`      | Type combinator, composition.                  | `B f g x = f (g x)`             | No explicit type arguments. Inferred from `Π`.<br>`Γ g : Π α, K* β, f : Π β, γ ⊢ (Π α, B f g) : γ (g x)` | No. Only kernel has access to rewrite rule. |
| `C`      | Type combinator, flip arguments to a function. | `C f x y = f y x`               | Inferred from `Π`. Omitted for brevity. No explicit type arguments.                                      | No. Only kernel has access to rewrite rule. |
| `K*`     | Type combinator, discard argument.             | `K* x y = x`                    | Inferred from `Π`. Omitted for brevity. No explicit type arguments.                                      | No. Only kernel has access to rewrite rule. |
| `I`      | Type combinator, identity.                     | `I x = x`                       | Inferred from `Π`. Omitted for brevity. No explicit type arguments.                                      | No. Only kernel has access to rewrite rule. |

#### Decreasing Measure: Why BCKI Combinators?

BCKI combinators are the preferred mechanism for forming types inside `Π` binders. This is because none of the arguments of the types of `K`, `K'`, or `S` duplicate any argument in context:

```lean
K : ∀ (α : Type) (β : α → Type) (x : α) (y : β x), α
K' : ∀ (α : Type) (β : Type) (x : α) (y : β), α
S : ∀ (α : Type) (β : α → Type) (γ : ∀ (x : α), β x → Type) (x : ∀ (x : α) (y : β x), γ x y) (y : ∀ (x : α), β x) (z : α), γ z (y z)
```

Each argument uses each element in the context at most once. By argument, I refer to each nested `(_ : _)` under a `Π` binder. The only duplication under a `Π` binder has the codomain of `S`.
This enables strong normalization of type formation in SK, since each argument type merely rearranges or discards elements in context, but never duplicates them. As such, **whenever an argument is applied to a function, the number of "type combinators" in its type strictly decreases**.

# Main Theorems

*Note: See [eval.lean](https://github.com/lexzaiello/DCC/blob/868e86ccb34a3cabcb71cdfaa05d48bb16d43397/Dcc/Eval.lean) for the full list of my results as of March 19, 2026.*

Our main goal is to prove strong normalization of well-typed dependent SK programs. We intend to do so by using our *decreasing measure* for types as a proxy. If a program is well-typed, then its type will strictly decrease upon applying an argument.

## BCKI Evaluation Rules

Here are the rewrite rules for our type combinators. Note that no duplication is possible, and we use call-by-name reduction to allow deterministic reduction:

```lean
inductive Expr.RedTy : Expr → Expr → Prop
  | next      : RedTy (SK (K* A b)) A
  | comp      : RedTy (SK (B f g x)) (SK (f (g x)))
  | flip      : RedTy (SK (C x y z)) (SK (x z y))
  | read      : RedTy (SK (I x)) x
  | congrFun  : Expr.RedTy f f'
    → Expr.RedTy (SK (f x)) (SK (f' x))
```

## Decreasing Measure in Types:

This is our definition of the "size" of an argument type under a `Π` binder:

```lean
inductive Expr.TySize : Expr → ℕ → Prop
  | next : Expr.TySize (SK K*) 1
  | comp : Expr.TySize (SK B) 1
  | flip : Expr.TySize (SK C) 1
  | read : Expr.TySize (SK I) 1
  | pi   : Expr.TySize (SK Π α, β) 0
  | comb : Expr.TySize (.comb c) 0
  | hole : Expr.TySize (SK __ ∶ t) 0
  | srt  : Expr.TySize (SK Sort m) 0
  | app  : Expr.TySize f n
    → Expr.TySize x m
    → Expr.TySize (SK (f x)) (n + m)
```

```lean
def Expr.ty_size : Expr → ℕ
  | (SK K*) | (SK B) | (SK C) | (SK I) => 1
  | (SK Π _α, _β) | .comb _c | SK __ ∶ _t | SK Sort _m => 0
  | SK (f x) =>
    let n := f.ty_size
    let m := x.ty_size
    (n + m)
```

We have proven soundness and completeness of our `ty_size` function with respect to `TySize`.

Note that due to our notion of congruence, the left-most head of an application must always fire for reduction to occur. As a result, the size of the application will strictly decrease.

## Existence of a decreasing size:

```lean
theorem Expr.RedTy.decreasing (h_red : Expr.RedTy e e') (h_size : e.TySize n) : ∃ m, e'.TySize m ∧ m < n := by
  induction h_red generalizing n
  · cases h_size
    iterate 2 (rename_i h _; cases h)
    exact ⟨_, (by assumption), by grind only⟩
  · cases h_size
    iterate 3 (rename_i h _; cases h)
    exact ⟨_, .app (by assumption) (.app (by assumption) (by assumption)), by grind only⟩
  · cases h_size
    iterate 3 (rename_i h _; cases h)
    exact ⟨_, .app (.app (by assumption) (by assumption)) (by assumption), by grind only⟩
  · cases h_size
    rename_i h _; cases h
    exact ⟨_, by assumption, by grind only⟩
  case congrFun f f' x hrf ih =>
    cases h_size
    rename_i n_x _ _
    have h := ih (by assumption)
    have ⟨m, hf, h₁⟩ := h
    exact ⟨m + n_x, .app (by assumption) (by assumption), by grind⟩
```

Together with uniqueness of type sizes, this shows that the type size *strictly decreases*:

```lean
theorem Expr.TySize.unique (h₁ : Expr.TySize e n) (h₂ : e.TySize m) : m = n := by
  induction h₁ generalizing m
  repeat (cases h₂; rfl)
  case app f n x m _ _ ih₁ ih₂ =>
    cases h₂
    rename_i hnf hnx
    have ha := ih₁ hnf
    have hb := ih₂ hnx
    grind only
```

We have also shown that the size decreases with respect to the transitive closure of `RedTy` (single-step reduction):

```lean
theorem Expr.RedTyTrans.decreasing (h_red : Expr.RedTyTrans a b) (hn : a.TySize n) : ∃ m, b.TySize m ∧ m < n := by
  induction h_red
  · rename_i hr
    exact hr.decreasing hn
  · rename_i b c htrans hr ih
    have ⟨m, hbm₁, hbm₂⟩ := ih
    have ⟨mc, hcm₁, hcm₂⟩ := hr.decreasing hbm₁
    exact ⟨mc, hcm₁, by grind only⟩

theorem Expr.RedTy.decreasing' (h_red : Expr.RedTy e e') : e'.ty_size < e.ty_size := by
  let h_size := e.ty_size
  have ⟨m, h, hp⟩ := Expr.RedTy.decreasing h_red (Expr.TySize.sound (e := e) (n := h_size) rfl)
  have h := h.complete
  exact h.symm ▸ hp
```

## Strong Normalization Proof (single step and transitive closure)

We use a fairly standard definition of `SN` with Lean's `Acc` accessibility predicate. We have proven it using our decreasing measure for both the transitive closure and single-step reduction:

```lean
def Expr.RedTy.SN (e : Expr) : Acc (fun b a => Expr.RedTy a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing'
  exact Expr.RedTy.SN e')
termination_by e.ty_size

def Expr.RedTyTrans.SN (e : Expr) : Acc (fun b a => Expr.RedTyTrans a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing'
  exact Expr.RedTyTrans.SN e')
termination_by e.ty_size
```

Our decreasing measure is extremely powerful, and allows us to recurse in proofs where Lean would have easily hung otherwise.

## Other proofs:

Here is a list of other proofs we have omitted for brevity:

* Completeness of the full beta reducer `reduce : Expr → Expr` with respect to normal transitive forms:
  * `theorem Expr.RedTyTrans.complete' : Expr.RedTyTrans a b → IsNorm b → Expr.reduce a = b := ...`
    * This essentially proves uniqueness of normal forms due to soundness of the reducer.
* Completeness of the full beta reducer with respect to definitional equality:
  * `theorem Expr.RedTyTrans.complete : Expr.RedTyTrans a b → Expr.reduce a = Expr.reduce b := ...`
  * `theorem Expr.RedTyTrans.reduce_same : Expr.RedTyTrans a b → Expr.RedTyTrans a c → reduce b = reduce c := ...`
    * **Note that this is essentially Church-Rosser, as we have also shown soundness of the reducer:**
* Soundness of the full beta reducer:
  * `theorem reduce_sound : Expr.reduce e = e' → Expr.RedTyReflTrans e e' := ...`
* More of these proofs, but for single-step reduction and the `step?` function.
  * Deterministic single-step reduction: `theorem Expr.RedTy.unique : Expr.RedTy a b → Expr.RedTy a c → b = c := ...`

# References:

Much of this current iteration of the paper is original work, but I have absorbed a great deal of information. Here is my Bibtex file of various sources I consulted:

* Altenkirch, T., Kaposi, A., Šinkarovs, A., & Végh, T. (2023). The Münchhausen Method in Type Theory. In 28th International Conference on Types for Proofs and Programs (TYPES 2022) (pp. 10:1–10:20). Schloss Dagstuhl – Leibniz-Zentrum fur Informatik.

* Mazza, D. (2007). A denotational semantics for the symmetric interaction combinators. Mathematical Structures in Computer Science, 17(3), 527–562.

* Eli Ben-Sasson, Iddo Bentov, Yinon Horesh, & Michael Riabzev. (2018). Scalable, transparent, and post-quantum secure computational integrity. .

* Maribel Fernández, & Ian Mackie (2003). Operational equivalence for interaction nets. Theoretical Computer Science, 297(1), 157–181.

* Lévy, J.J. (1976). An algebraic interpretation of the λβ K-calculus; and an application of a labelled λ-calculus. Theoretical computer science, 2(1), 97-114.

* Yves Lafont (1997). Interaction Combinators. Information and Computation, 137(1), 69-101.

* Micali, S. (2000). Computationally Sound Proofs. SIAM J. Comput., 30(4), 1253–1298.

* Eli Ben-Sasson, Alessandro Chiesa, Eran Tromer, & Madars Virza. (2014). Scalable Zero Knowledge via Cycles of Elliptic Curves. .

* Arora, S., & Safra, S. (1998). Probabilistic checking of proofs: a new characterization of NP. J. ACM, 45(1), 70–122.

* Goldwasser, S., Micali, S., & Rackoff, C. (1985). The knowledge complexity of interactive proof-systems. In Proceedings of the Seventeenth Annual ACM Symposium on Theory of Computing (pp. 291–304). Association for Computing Machinery.

* Lior Goldberg, Shahar Papini, & Michael Riabzev. (2021). Cairo – a Turing-complete STARK-friendly CPU architecture. .

* Lafont, Y. (1989). Interaction nets. In Proceedings of the 17th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (pp. 95–108). Association for Computing Machinery.

* Y. Lafont (1988). The linear abstract machine. Theoretical Computer Science, 59(1), 157-180.

* Cousineau, M. (1985). The categorical abstract machine. In Functional Programming Languages and Computer Architecture (pp. 50–64). Springer Berlin Heidelberg.

* Peyton Jones, S. (1987). The Implementation of Functional Programming Languages (Prentice-Hall International Series in Computer Science). Prentice-Hall, Inc..

* Seely, R. (1984). Locally cartesian closed categories and type theory. Mathematical Proceedings of the Cambridge Philosophical Society, 95(1), 33–48.

* P.-L. Curien (1986). Categorical combinators. Information and Control, 69(1), 188-254.

* Andreas Abel, Klaus Aehlig, & Peter Dybjer (2007). Normalization by Evaluation for Martin-Löf Type Theory with One Universe. Electronic Notes in Theoretical Computer Science, 173, 17-39.

* David Turner (1979). A new implementation technique for applicative languages. Software: Practice and Experience, 9.

# Future Work

My next primary objective is to formalize a proof of strong normalization of well-typed term-level SK programs using my type-level decreasing measure as a proxy. This is my final objective. Then, I intend to type-set the paper.

## Lean Toolchain

I am using Lean4 with the toolchain `leanprover/lean4:v4.26.0`. Lean support with Nix is not well-maintained, so you will have to install it manually.

## Docs

To view the documentation, use:

```shell
nix run .#serve
```

If the docs are not up-to-date, please run `lake build`.

By *Lexi Aiello*.
