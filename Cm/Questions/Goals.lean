/-
Project objectives:

- Dependent S combinator with the standard type
- Dependent K combinator, with the standard type
- Nondependent K combinator, with the standard type

- Minimize the number of "special cases" we have in our AST.
  - If we can make cons point-free, we should do it.
  - If we can make pairs point-free, we should do it.
  - Ideally, application is the only non-point-free inference rule
- Maximize the expressivity of the language. Ideally, we use S, K, and app as usual.
  - We should only tack extra things on top if absolutely necessary.

If we were to do pure dependent SK, what would we need? What would be extra?

  - Need some way to represent Pi. Choose:
    1. Context lists? If so, snd and fst feel 

Proofs:
- Preservation proof
- Progress proof
- Church rosser theorem
- Strong normalization, if possible / enough time

Retrospective:

What is the latest iteration of the project attempting to do?

- separate nondependent pairs from sigma pairs.
- not clear that these two things even need to be separated

The big question: how do we emulate substitution?

- We almost always end up with some notion of Pi, even if it's just a syntactic marker.
- (Pi x) : Type

Multiple designs struggled, as they were each missing critical components. Rank in order of importance:

1. Contexts /
2. Sigma pairs: pairs that can depend on other values - 
-/
