# DCC - The Dependent Combinator Calculus

## Overview

The DCC is a dependently-typed calculus based on [categorical combinators](https://www.sciencedirect.com/science/article/pii/S001999588680047X). DCC is [extensional](https://ncatlab.org/nlab/show/extensional+type+theory), meaning the equality reflection theorem holds. DCC has decidable type-checking, is strongly-normalizing, and consistent. A subset of Lean 4 can be compiled to DCC.

DCC is quite minimal, aiming to have sound metatheory. It is implemented entirely in Lean with a [type-checker](https://github.com/lexzaiello/DCC/blob/master/Dcc/Judge3.lean) with soundness and completeness. You can import the type-checker (`Expr.infer`) by importing `Dcc.Judge3`. The β-reduction engine can be imported with `import Dcc.Red`.

See the [paper](https://github.com/lexzaiello/DCC/blob/master/paper.pdf) for a formal presentation of DCC.

## Examples

DCC uses a Lisp-like S-expression syntax. A DCC program looks like this:

```lisp
(DCC ((Λ (Sort 0) (Id (Sort 0)) (Id (Σ (Sort 0) (Id (Sort 0))))) 𝟙 ∗))
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

## Lean Toolchain

I am using Lean4 with the toolchain `leanprover/lean4:v4.30.0-rc2`. Lean support with Nix is not well-maintained, so you will have to install it manually.

## Docs

To view the documentation, use:

```shell
nix run .#serve
```

If the docs are not up-to-date, please run `lake build`.

By *Lexi Aiello*.
