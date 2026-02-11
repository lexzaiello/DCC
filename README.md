# DCC - The Dependent Combinator Calculus

The DCC is an extensional, dependently-typed combinator calculus. It is based on [SK combinators](https://en.wikipedia.org/wiki/SKI_combinator_calculus).

## Lean Toolchain

I am using Lean4 with the toolchain `leanprover/lean4:v4.26.0`. Lean support with Nix is not well-maintained, so you will have to install it manually.

## Docs

To view the documentation, use:

```shell
nix run .#serve
```

If the docs are not up-to-date, please run `lake build`.
