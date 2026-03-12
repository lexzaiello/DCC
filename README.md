# DCC - The Dependent Combinator Calculus

## Overview

The DCC is a dependently-typed calculus based on [SK combinators](https://en.wikipedia.org/wiki/SKI_combinator_calculus). The DCC does not use variables or mutable state. In this repository, I set out to:

## Dependent S Combinator Type-checks

```lean
example (h₁ : Judge (Srt m) α) (h₂ : Judge ((~> n.succ) α, (Srt n)) β)
  (h₃ : Judge ((Π' o.succ) α
      , (Π' o.succ) β
      , ⸨next ⸨assert (Srt o)⸩⸩) γ)
  (h₄ : Judge ((Π' o) α, (Π' o) β, γ) x)
  (h₅ : Judge ((Π' n) α, β) y)
  (h₆ : Judge α z) : Judge ⸨γ z ⸨y z⸩⸩ ⸨(S m n o) α β γ x y z⸩ := by
  decide_infer
```

## Lean Toolchain

I am using Lean4 with the toolchain `leanprover/lean4:v4.26.0`. Lean support with Nix is not well-maintained, so you will have to install it manually.

## Docs

To view the documentation, use:

```shell
nix run .#serve
```

If the docs are not up-to-date, please run `lake build`.

By *Lexi Aiello*.
