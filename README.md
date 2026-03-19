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

## Main Theorems

Our main goal is to prove strong normalization of well-typed dependent SK programs. We intend to do so by using our *decreasing measure* for types as a proxy. If a program is well-typed, then its type will strictly decrease upon applying an argument.

### BCKI Evaluation Rules

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

### Decreasing Measure in Types:

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

We have proven [soundness and completeness](https://github.com/lexzaiello/DCC/blob/5aa8889607fde66a7cf44ae06b477a3a7fe17926/Dcc/Eval2.lean#L73) of our `ty_size` function with respect to `TySize`.

Note that due to our notion of congruence, the left-most head of an application must always fire for reduction to occur. As a result, the size of the application will strictly decrease.

#### Existence of a decreasing size:

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

### Strong Normalization Proof (single step and transitive closure)

We use a fairly standard definition of `SN` with Lean's `Acc` accessibility predicate. We have proven it using our decreasing measure for [both the transitive closure and single-step reduction](https://github.com/lexzaiello/DCC/blob/5aa8889607fde66a7cf44ae06b477a3a7fe17926/Dcc/Eval2.lean#L361):

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

### Other proofs:

Here is a list of other proofs we have omitted for brevity:

* [Completeness](https://github.com/lexzaiello/DCC/blob/5aa8889607fde66a7cf44ae06b477a3a7fe17926/Dcc/Eval2.lean#L336) of the full beta reducer `reduce : Expr → Expr` with respect to normal transitive forms:
  * `theorem Expr.RedTyTrans.complete' : Expr.RedTyTrans a b → IsNorm b → Expr.reduce a = b := by ...`
* [Completeness](https://github.com/lexzaiello/DCC/blob/5aa8889607fde66a7cf44ae06b477a3a7fe17926/Dcc/Eval2.lean#L328) of the full beta reducer with respect to definitional equality:
  * `theorem Expr.RedTyTrans.complete : Expr.RedTyTrans a b → Expr.reduce a = Expr.reduce b := ...`


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
