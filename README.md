# DCC - The Dependent Combinator Calculus

## Overview

The DCC is a dependently-typed calculus based on [categorical combinators](https://www.sciencedirect.com/science/article/pii/S001999588680047X). DCC is [extensional](https://ncatlab.org/nlab/show/extensional+type+theory), meaning the equality reflection theorem holds. DCC has decidable type-checking, is strongly-normalizing, and consistent. A subset of Lean 4 can be compiled to DCC.

See the [paper](https://github.com/lexzaiello/DCC/blob/master/paper.pdf) for a formal presentation of DCC.

## Lean Toolchain

I am using Lean4 with the toolchain `leanprover/lean4:v4.30.0-rc2`. Lean support with Nix is not well-maintained, so you will have to install it manually.

## Docs

To view the documentation, use:

```shell
nix run .#serve
```

If the docs are not up-to-date, please run `lake build`.

By *Lexi Aiello*.
