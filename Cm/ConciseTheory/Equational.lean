/-
I want to make our "retroactive" / uncurried interpretation work.
That is, since all the combinators have a fixed nubmer of arguments, it doesn't really matter
if we can do partial application. But it does in some sense.
Altenkirch mentions the primary stumbling block is the U-set. You need a "placeholder" for the sort
that contains all the types, since you want to add more, even after referencing the base type sort.

We have achieved this without forward declarations or rewrite rules in the past. Munchhausen method
is entirely unnecessary for combinators.

It's also an extremely unergonomic approach and kind of boils down to our meta combinators.

The two approaches we've explored to this:
- Tall meta combinator hierarchy, never achieved fully dependent S, since its dependent type is notoriously complex.
- "Equational" meta combinators. This supports fully dependent S, but it does not support partial application.

Partial application is pretty necessary. Not being able to type-check partially applied combinators does not necessarily
lead to inconsistency, but it intuitively makes it less useful in some vague sense.

Altenkirch's paper isn't particularly helpful, but we can try modeling our theory similarly with simulated "rewrite rules".

Take an example:

K has 2 explicit type arguments, and 2 term / parameter arguments

K : ∀ (α : Type) (β : α → Type) (x : α) (y : β x), α
S : ∀
  (α : Type)
  (β : α → Type)
  (γ : ∀ (x : α), β x → Type)
  (f : ∀ (x : α) (y : β x), γ x y)
  (g : ∀ (x : α), β x)
  (x : α) : γ x (g x) := f x (g x)

Our "equational" approach to this involved computing the type only when all of the arguments were applied, but this
feel dumb, since then we can't produce a proof of α → α, for example, with only K and S.
We can only type-check terms that reduce to beta normal forms, essentially.

This is not ideal. We want to be able to derive I, for example, which we can't do if we don't have support for partial application.

The other approach was fine, but we had a massive hierarchy of meta combinators. At least a dozen of them.
S was the central culprit.

I'm curious if we can do some combination of the approaches though.
The main challenge with the approach supporting partial application was that getting the meta combinator types right was difficult.
And, there was exponential blowup, which Altenkirch mentions, since each of the meta combinators need their own types, and they need their own types, forever.

Not really sure what Altenkirch means by "internalizing" the U-set.

"The problem is that in Pi, Kd and Sd type parameters X, Y, and Z are quantified externally.
"Externally?"

"Quantify within U" - U is the "placeholder" type universe, I assume

Realization:
- Tm : Ty → Set denotes that each term has access to the entire universe of types. This seems like it's only something you need to worry about when you rely on Agda rewrite rules to encode the theory.

So, U is the placeholder universe of all types?
In our combinator definitions, we often need access to elements inside Ty

What is the actual point of U?

Ty : Set, so Ty is the set of all types?
Terms are indexed by a Ty, not the Ty, though, which is confusing.
I think this is only required to facilitate checking types via rewrite rules / pattern matching. We will need to do something similar if we choose to encode our meta-theory in a similar way in Lean, although we will probably find a better way.

This Fam postulate comment is quite confusing: "- Fam X ≈ (X => U)
Fam is any function indexed by a Type.

How was he able to condense the meta combinator hierarchy for S? Could we copy his? Is there anything intrinsic to it that would forbid a freestanding theory?

Altenkirch has only 4 meta combinators for his S types, so maybe we can copy his?

"Currently, the interplay between the rewrite rules and the type-checker is not always satisfying. For example, our first attempt ends in an "infinite rewrite" - not good, as all the rules have to fire before the type-checker.

Essential components:
- "we introduce the type of an object but only define it later while already using it in the types of other objects" - this is kind of what we did, but without intending so.
- inductive inductive constructors ("coinductives"), we don't use these, they're not necessary


-/

namespace Comb


end Comb
