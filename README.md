# DCC - The Dependent Combinator Calculus

## Overview

The DCC is a dependently-typed calculus based on [SK combinators](https://en.wikipedia.org/wiki/SKI_combinator_calculus). The DCC does not use variables or mutable state. In this repository, I set out to:

- [x] Define syntax for a variable-free combinator calculus
- [x] Define single-step and type relations for the calculus
  - [x] Define types for every object in the syntax tree
- [ ] Proofs
  - [ ] Prove preservation of the typing judgment under single-step reduction
  - [ ] Prove preservation of the typing judgment under star-step reduction
  - [ ] Prove progress of well-typed terms (well-typed terms can step, or they are normal values)
  - [ ] Prove weak normalization of the calculus using [reducibility candidates](https://www.cs.cmu.edu/~rwh/courses/chtt/pdfs/girard.pdf) or a combinator-specific decreasing measure

## Lean Toolchain

I am using Lean4 with the toolchain `leanprover/lean4:v4.26.0`. Lean support with Nix is not well-maintained, so you will have to install it manually.

## Docs

To view the documentation, use:

```shell
nix run .#serve
```

If the docs are not up-to-date, please run `lake build`.
