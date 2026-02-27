/-
Meta combinators with some useful "shapes" abstracted. Specifically,
- β x

- forwardN would be cool too
- "forward". Inspired by this shape:
  | k'₁     : IsStepM ⟪(M K'.{[m, n]}) α⟫ ⟪Π.{[n.succ, m]} (Sort n) (M (K'.{[m, n]} α))⟫

A meta combinator takes a type argument α, then inserts it somewhere within the
type it represents to be carried on to the next binder.

subst is distinct from S, in that it can only produce a Π "binder" at the top level.

forward.{[m, n]} _ α = Π.{[m, n]}

- note that this approach means we can skip Π combinators and only have Π expressions,
since forward handles this for us.

Π : Syntax
app' : (Syntax → Syntax) → (Syntax → Syntax) → Syntax → Syntax
^ we can handle Π with this one too with a special ValidJudgment for Π.
^ can insert constants with forget. subst is special case for Π,
app' is composition equivalent kinda.
since we don't want a Π combinator.
quote = K' Syntax Syntax

- kernel implicitly converts from Syntax to type.

- judgmental definitional equality is hidden, except to the kernel

we don't need context lists?

subst.{[m, n]} πdom πcod x = Π.{[m, n]} (πdom x) (πcod x)

K'.{[m, n]} : Π.{[m.succ, m]} (Sort m)
  (subst.{[n.succ, m]} (quote (Sort n))
    (subst.{[m, m]} (I.{[1]} Syntax)

| k'₁     : IsStepM ⟪(M K'.{[m, n]}) α⟫ ⟪Π.{[n.succ, m]} (Sort n) (M (K'.{[m, n]} α))⟫
k'₁ =

THE most natural way to do this is with context lists. All arguments at all binders.
we can literally pass in the application itself. It receives itself.

idx f

0 f (app' a b) = (f a)
(n + 1) f (app' a b) = n f b

inductive Pos where
  | head : Pos
  | tail : Pos → Pos

0 = Pos.head
(n + 1) = Pos.tail n

Π receives the entire application as "Syntax".
dom and cod are mappings on Syntax. use app' for this.

app' is actually a ReaderT Syntax Syntax. It's a monad.
need to pass around the context as well.
Think it actually handles this by default.
-/
