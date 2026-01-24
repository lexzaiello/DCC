/-
Specifics to hammer out with the sigma approach:

::[::[(Ty m), nil.{[m.succ]}], ::[nil.{[m]} ∘ Prod.fst, Prod.snd]]

apply ::[x, f] = Prod.snd

TODO:
- need to figure out if I need Prod.fst and Prod.snd
or if I can use π.

I kind of want to try Prod.fst and Prod.snd

apply ::[x, f] = ::[x, f].snd

Prod.fst (α : Type) (β : α → Type) : (l : (× α β)), α
Prod.snd (α : Type) (β : α → Type) : (l : (× α β)), β l.fst

Question:
- do we want explicit type arguments for Prod.fst and Prod.snd?
I think we can do it, but considering NOT.

TODO:
- we may be able to remove π now?


∘ = ?
substitution of the context after ::[α,

we have prod.fst, and prod.snd defined now. epic.
unresolved questions.

id.{[m]} : (::[::[(Ty m), nil.{[m.succ]}], ::[nil.{[m]} ∘ Prod.fst, Prod.snd]])

I want to remove this composition shit.

::[nil.{[m]} ∘ Prod.fst, Prod.snd]
receives
::[\alpha, ::[Ty m, nil.{{m.succ]}]] from the α app.

this might call for both, but I don't want to do that. ngl

::[x, ::[f, g, ∘]] = f$ f (f$ g x)

we're just changing the nesting slightly here.

::[x, ::[f, g, ∘]] = ::[::[x, f], g]
::[x, ::[f, g]].snd = ::[::[x, f], g]?????

id.{[m]} : (::[::[(Ty m), nil.{[m.succ]}], ::[::[nil.{[m]}, Prod.fst], Prod.snd]])

(app? snd ::[(symbol "x"), ::[symbol "f", symbol "g"]]) = f$ g (f$ f x)

nil feels mildly more annoying to use than I would like.
would like the type to be even simpler, ngl.
nil α x = x

maybe it's actually fst?
-/
