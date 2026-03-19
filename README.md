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

| Object   | Purpose                                    | Rewrite Rule                    | Type                                                       | Computationally Relevant?                   |
|----------|--------------------------------------------|---------------------------------|------------------------------------------------------------|---------------------------------------------|
| `S`      | Duplication and composition in computation | `S x y z = (x z) (y z)`         | See above                                                  | Yes                                         |
| `K`      | Weakening, dependent type                  | `K x y = x`                     | See above                                                  | Yes                                         |
| `K'`     | Weakening, nondependent type               | `K' x y = x`                    | See above                                                  | Yes                                         |
| `Sort m` | Prevent self-type paradox                  | n/a                             | `⊢ Sort m : Sort m.succ`, `Prop` is shorthand for `Sort 0` | No, cannot pattern match.                   |
| `Π`      | Form dependent types.                      | `((Π α, β) x) = Π (α x), (β x)` | `Γ x : α, β x : Sort m ⊢ Π α, β : Sort m`                  | No. Only kernel has access to rewrite rule. |
| `B`      | Type combinator                            |                                 |                                                            |                                             |
|          |                                            |                                 |                                                            |                                             |

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
