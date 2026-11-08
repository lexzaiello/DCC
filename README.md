# DCC - The Dependent Combinator Calculus

## Overview

The DCC is a dependently-typed calculus based on [categorical combinators](https://www.sciencedirect.com/science/article/pii/S001999588680047X). DCC is [extensional](https://ncatlab.org/nlab/show/extensional+type+theory), meaning the equality reflection theorem ([proof](https://github.com/lexzaiello/DCC/blob/4b0ea7f932ae69ac6d11658d69d3dcc0c261f4e7/Dcc/Metatheory/Extensional.lean#L122)) holds. DCC has decidable type-checking ([proof](https://github.com/lexzaiello/DCC/blob/fb7acf6d9644df7d13c809d12609b59eaca5c763/Dcc/Metatheory/Decidability.lean#L135)), is strongly-normalizing ([proof](https://github.com/lexzaiello/DCC/blob/fb7acf6d9644df7d13c809d12609b59eaca5c763/Dcc/Red/Rel.lean#L82)), and consistent ([proof](https://github.com/lexzaiello/DCC/blob/4b0ea7f932ae69ac6d11658d69d3dcc0c261f4e7/Dcc/Metatheory/Consistent.lean#L7)). A subset of Lean 4 can be compiled to DCC.

DCC is quite minimal, aiming to have sound metatheory. It is implemented entirely in Lean with a [type-checker](https://github.com/lexzaiello/DCC/blob/master/Dcc/Judge3.lean) with soundness and completeness. You can import the type-checker (`Expr.infer`) by importing `Dcc.Judge3`. The β-reduction engine can be imported with `import Dcc.Red`.

See the [paper](https://github.com/lexzaiello/DCC/blob/master/paper.pdf) for a formal presentation of DCC.

## Examples

DCC uses a Lisp-like S-expression syntax. A DCC program looks like this:

```lisp
(DCC ((Λ (Sort 0)
         (Id (Sort 0))
         (Id (Σ (Sort 0)
             (Id (Sort 0)))))
      𝟙
      ∗))
```

This is a program that applies a type `𝟙` (the top / unit type) and its inhabitant `∗` to a function which accepts a type and an inhabitant of its type `(Λ (Sort 1) (Id (Sort 0)) (Id (Σ (Sort 0) (Id (Sort 0)))))`. Its output is as such:

```lean
open Expr in
#eval reduce_all (DCC ((Λ (Sort 0) (Id (Sort 0)) (Id (Σ (Sort 0) (Id (Sort 0))))) 𝟙 ∗))
/-
Messages here:
16:0:
(DCC (,(Id (Sort 0)) 𝟙 ∗))
-/
```

It type-checks as such:

```lean
open Expr in
#eval (·.fst) <$> infer (DCC ((Λ (Sort 0) (Id (Sort 0)) (Id (Σ (Sort 0) (Id (Sort 0))))) 𝟙 ∗))
/-
Messages here:
16:0:
Except.ok (DCC (Σ (Sort 0) (Id (Sort 0))))
-/
```

### Boolean negation

This is a function that flips boolean:

```lisp
(DCC (𝟚.Rec (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟚))
            (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟘₂))
            (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟙₂))))
```

It type-checks as such:

```lean
open Dsl Expr in
#eval (·.fst) <$> infer (DCC (𝟚.Rec (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟚)) (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟘₂)) (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟙₂))))
/-
Messages here:
191:0:
Except.ok (DCC ((Π (`𝟙 𝟙) (`𝟙 (Π (`𝟙 𝟚) (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟚))))) ∗))
-/
```

It runs as such:

```lean
open Dsl Expr in
#eval reduce_all (DCC ((𝟚.Rec (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟚)) (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟘₂)) (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟙₂))) ∗ 𝟙₂))
/-
Messages here:
191:0:
(DCC 𝟘₂)
-/
```

And type-checks correctly:

```lean
open Dsl Expr in
#eval (·.fst) <$> infer (DCC ((𝟚.Rec (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟚)) (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟘₂)) (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟙₂))) ∗ 𝟙₂))
/-
Messages here:
191:0:
Except.ok (DCC 𝟚)
-/
```

### Bool-indexed identity

This is a DCC expression for the identity function indexed by a boolean. If it is applied 𝟙₂, its domain is `A`. If it applied 𝟘₂, its domain is `B`:

```lean
def example_curr_bool_select (A B : Expr) : Expr :=
  -- If true, 𝟙, if false 𝟘
  let motive     := DCC (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) (Sort 0)))
  let case_true  := DCC (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) A))
  let case_false := DCC (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) B))
  let selector   := (DCC ((𝟚.Rec motive case_true case_false) ∗))
  DCC (Λ 𝟚 selector (Snd selector))

open Dsl in
#eval (·.fst) <$> Expr.infer (example_curr_bool_select (DCC 𝟙) (DCC 𝟘))
/-
Messages here:
213:0:
Except.ok (DCC
 ((Π (`𝟙 𝟚)
     (`𝟙 (Π ((𝟚.Rec (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) (Sort 0))) (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟙)) (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟘)))
             ∗)
            (Λ 𝟚
               ((𝟚.Rec (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) (Sort 0))) (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟙))
                       (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟘)))
                ∗)
               (∘ ((𝟚.Rec (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) (Sort 0))) (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟙))
                          (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟘))) ∗)
                  (Fst ((𝟚.Rec (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) (Sort 0))) (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟙))
                               (Λ 𝟙 (`𝟙 𝟚) (`(Σ 𝟙 (`𝟙 𝟚)) 𝟘))) ∗)))))))
  ∗))
-/

open Dsl in
#eval (·.fst) <$> Expr.infer (DCC (#((example_curr_bool_select (DCC 𝟙) (DCC 𝟘))) 𝟙₂ ∗))
/-
Messages here:
215:0:
Except.ok (DCC 𝟙)
-/

open Dsl in
#eval Expr.reduce_all (DCC (#((example_curr_bool_select (DCC 𝟙) (DCC 𝟘))) 𝟙₂ ∗))
/-
Messages here:
218:0:
(DCC ∗)
-/
```

## Lean Compiler

The current version of DCC does not have η-reduction, so some examples of the Lean compiler do not work. However, here is the identity function on 𝟚:

```lean
#eval Std.format (dcc_compile (fun (x : Bool) => x))
/-
Messages here:
24:0:
((!Λ 𝟙 (`𝟙 𝟚) (∘ (Snd (`𝟙 𝟚)) (* (Σ 𝟙 (`𝟙 𝟚))))) (& ∗))
-/
```

It type-checks as such:

```lean
#eval (·.fst) <$> Expr.infer (dcc_compile (fun (x : Bool) => x))
Messages here:
25:0:
Except.ok (DCC ((Π (!<> (`𝟙 𝟚)) (!Λ 𝟙 (`𝟙 𝟚) (∘ (∘ (`𝟙 𝟚) (Fst (`𝟙 𝟚))) (* (Σ 𝟙 (`𝟙 𝟚)))))) (& ∗)))
```

Past versions of DCC had more powerful η-reduction. However, we have omitted it in this version so as to achieve these metatheoretic results:

- Subject-reduction: [proof](https://github.com/lexzaiello/DCC/blob/fb7acf6d9644df7d13c809d12609b59eaca5c763/Dcc/Metatheory/SubjectReduction.lean#L965)
- Progress: [proof](https://github.com/lexzaiello/DCC/blob/fb7acf6d9644df7d13c809d12609b59eaca5c763/Dcc/Metatheory/Progress.lean#L957)
- Consistency: [proof](https://github.com/lexzaiello/DCC/blob/4b0ea7f932ae69ac6d11658d69d3dcc0c261f4e7/Dcc/Metatheory/Consistent.lean#L7)
- Equality reflection: [proof](https://github.com/lexzaiello/DCC/blob/4b0ea7f932ae69ac6d11658d69d3dcc0c261f4e7/Dcc/Metatheory/Extensional.lean#L122)

We hope to add back η-reduction and more powerful type conversion in a later paper.

## Lean Toolchain

I am using Lean4 with the toolchain `leanprover/lean4:v4.30.0-rc2`. Lean support with Nix is not well-maintained, so you will have to install it manually.

By [*Lexi Aiello*](https://lexzaiello.com/).

# AI (Anti)-Disclosure

No LLM software was used in this paper and I am morally opposed to the existence of LLM-based intelligence. This paper is licensed under the GNU GPL-3.0 license. Attribution **must** be provided in any derivative works, including LLM-assisted ones, and the GNU GPL-3.0 license must be appropriately used.
