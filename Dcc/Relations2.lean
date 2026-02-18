import Mathlib.Data.Nat.Notation

/-
Porting over abstract.lean work:

(∷ f g)

Design questions:
- should we put g first, letting us omit the judgment for f?
- Can we make a macro for cons that derives the types from the head-most ∷?

f : P
Q : P → Sort n
g : Q f

∷ is untyped. it just takes two judgments. We only know to substitute

Q' = P f

(∷ (∶ P f) (∶ Q' g))

How does substitution work mechanically? We can choose:

- duplicate x, pass composition in:
  (∷ f(x), g(x, f(x)))
- only duplicate x:
  (∷ f(x), g(x))

For actually making types:
- it's useful to have an "output" value and a "stored" value. a context, and an output
  - or, we can substitute all the way down, which is that the duplication option does.
  This is also what we did our proof of.
- perhaps sigma is less complicated than I thought. we just duplicate x in. This is substitution.

- assume f : α → β, g : α → γ

- We could type (∷ f g) as selecting a selector which acts on both the elements.

(∷f x) : (α → β → γ) → γ
Interesting, this looks like the S type.

What is the challenge we are trying to solve?

- Cons is a structure in our shallow encoding. It has its own type. it is not derived, for example,
and it isn't prop.
- If we don't use function composition, we won't be able to derive its type easily.

- Function composition is the most promising approach.

(∷f(x), g(f(x)))

(∷ (∶ _ f) (∶ _ g))

How will we represent simple arrows?

(∷ (∶ JudgeArg Arg) (∶ JudgeApp App))

- substitute x all the way down
- compose types

(∷ (∶ P f) (∶ Q g)) x =
  (∷ (∶ (P x) f(x)) (∶ Q(x, f(x)) g(x)))

- I combinator is totally unnecessary.
- we want S and K. In their usual formulations. No special judgment shit.
- First thing to do is Cons type.
- Also check Judge type.

- What will be the hardest parts of this? Can we do the S type?
- we will have to have the tail list also typed. This is annoying and confusing.
We can potentially avoid this by making ValidJudgment work only with types, not judgments.

- for checking apps as well:
  - we should assume that the head component is already sustituted. so don't substitute head.
  Just check if f = α

S m n o : (∷ (∶ (Ty m.succ) (Ty m)) (∶ _ cod))

- cod will receive x, at least in the type, and ((∶ (Ty m.succ) (Ty m)) x)

Two potential interpretations:
- fst is the type of the type
- snd is the asserted type

The purist interpretation:
- P is the assertion that this is well-typed.
I like this one more, because it forms kind of a tree of applications.

S type:

S m n o :
^ cod receives x. that's good.

I mean another thought is whether we want to pass x and f(x) in as just separate argument or as a list.

A list would be ideal, since then we can traverse it with fst and snd.

Also, we can ignore elements with fst, which is nice.

This will change the type of cons slightly, but that's fine.

Q ::[x, f x]. this aligns perfectly with sigma, ngl.
-/

abbrev Level := ℕ

inductive Expr where
  | K     : Level → Level → Expr -- Dependent K
  | K'    : Level → Level → Expr -- Nondependent K
  | S     : Level → Level → Level → Expr -- Dependent S
  | cons  : Expr  → Expr  → Expr -- not a combinator. just a freestanding expr.
  | judge : Level → Expr
  | type  : Level → Expr
  | prop  : Expr
  | sort  : Level → Expr
  | fst   : Expr
  | snd   : Expr
  | app   : Expr → Expr → Expr

open Expr

syntax "⸨" term+ "⸩"                          : term
syntax "::[" term,+ "]"                       : term
syntax "(" term "∶" "(" term "∶" term ")" ")" : term
-- ^ for making judgments: (x : (α : Ty m))

notation "Π'" => Expr.Pi
notation "Ty" => Expr.type
notation "Srt" => Expr.sort
notation "Prp" => Expr.prop

macro_rules
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f $x)
  | `(⸨ $f $x:term $args:term*⸩) => `(⸨ (Expr.app $f $x) $args*⸩)
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.cons $x ::[$xs,*])
  | `(($x ∶ ($α ∶ Ty $m))) => `(⸨(judge $m) $α $x⸩)

/-
In cons substitution / currying,
(∷ (judge P f) (judge Q g))
((∷ (judge P f) (judge Q g)) x) = ...

x : (α : Sort m)
P : α → Type

def Cons.curry.{m, n, o} {α : Sort m} {P : α → Sort n} {Q : ∀ (x : α), P x → Sort o}
  (c : Cons (∀ (x : α), P x) (fun f => ∀ (x : α), Q x (f x)))
  (x : α) : Cons (P x) (Q x) := ⟨c.f x, c.g x⟩ -- (:: f(x) g(x))

In cons substitution / currying:
P = ∀ (x : α), P(x) = ∷[(∶ 
∷[(∶

Another idea, potentially sus:

α → β = ::[(∶ α), β]

Another thing:
since cons is so primitive, we may want to special case it.
It's just incredibly frustrating having to put judgments for everything.

Or, we can add explicit type arguments to cons.

:: Tα Tβ [(∶ α), β]

This is not very different. it reads mildly cleaner.
Special case is preferred, to be honest.

We can make cons not a combinator. That's pretty clean, tbh.

Then, we don't have to give explicit types to the elements.
We can just hide it all in the judgment rule.

So, now, f : α → β:

::[(∶ α), (∶ 

A function application is a sequence of judgments.

So, the function application rule:
- substitute x in:
- check if fst is its type. this is the same as always.

Another idea:
- head element of the list is not just asserting the type of the argument, it's asserting
the type of the entire app so far.

Then, we always have the entire context floating around.
Then, again, it becomes composition, not duplication.

::[f, g] x = ::[f(x), g(f(x))]

f : α → β:
::[(: m) α, ::[snd ::[fst, (∶ m)

- we should make fst and snd also do substitution. fst l x. snd l x

Given that ::[] is untyped, we can almost certainly abuse this composition.

- Head position is not just a judgment of the argument,
but a judgment of the entire function.

Another thing I want to be able to do is both.
both in head position just duplicates the x.

::[both, g] x = ::[::[x, x], g]

However, there are different kinds of substitution and projection.

fst and snd should not assume that we want to substitute.

f : α → β = ::[(∶ m) α, ::[

How do we know when we want to normalize and when we don't?
When ::[] is composition and when it's not?

fst / snd are nice, but it would be even nicer if we could replace them.

Remember ::[a, b] x substitutes.

We can assume almost always that the second-most component is the final β-normal value.

so, fst and snd are not necessary for lists.

::[a, b] ::[f, g] = ::[::[f, g] a, b(::[f, g] a)]
                  = ::[::[f a, g a], b ::[f a, g a]]

we can re-derive the S combinator?

::[::[f a, g a], ::[b, c] ::[f a, g a]]
=

::[] is the list of steps in a reduction. literally. it literally is.
It's the inverse of application.

α → β, if ::[] is describing steps of a computation:

Judgments may actually be secondary to everything we're doing.
What advantage does the judgment have?
-/

inductive IsStep : Expr → Expr → Prop
  | subst  : IsStep ⸨::[f, g] x⸩ ::[⸨f x⸩, ⸨g ⸨f x⸩⸩]
  | k      : IsStep ⸨(K m n) α β x y⸩ x
  | k'     : IsStep ⸨(K' m n) α β x y⸩ x
  | s      : IsStep ⸨(S m n o) α β γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | fst    : IsStep ⸨fst ::[f, g]⸩ f
  | snd    : IsStep ⸨snd ::[f, g]⸩ g
  | fstj   : IsStep ⸨fst (f ∶ (α ∶ Ty m))⸩ f
  | sndj   : IsStep ⸨snd (f ∶ (α ∶ Ty m))⸩ α
  | left   : IsStep f f' → IsStep ⸨f x⸩ ⸨f' x⸩
  | right  : IsStep x x' → IsStep ⸨f x⸩ ⸨f x'⸩

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | symm    : DefEq e e'  → DefEq e' e
  | step    : IsStep e e' → DefEq e e'
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ⸨f x⸩ ⸨f' x⸩
  | right   : DefEq x x'  → DefEq ⸨f x⸩ ⸨f x'⸩

/-
S m n o : ∀ (α : Type m) (β : α → Type n) (γ : ∀ (x : α), β x → Type o)
  (f : ∀ (x : α) (y : β x), γ x y)
  (g : ∀ (x : α), β x)
  (z : α), γ x (g x)
-/
def S.type (m n o : Level) : Expr :=
  -- assert (α : Ty m)
  let α := ⸨(∶ 0) ⸨(∶ m.succ) (Ty m)⸩ (S m n o)⸩

  -- with α and (∶ Ty m α) in scope
  let β := ⸨(∶ sorry

  -- type of (S m n o α). ∀ (β : α → Type) ...
  let tSα := (∷ β sorry)

  ⸨∷ α ⸨(∶ o) tSα (S m n o)⸩⸩


inductive ValidJudgment : Expr → Expr → Prop
  | ty    : ValidJudgment (Ty m.succ) (Ty m)
  | prp   : ValidJudgment (Ty 0) Prp
  | app   : ValidJudgment t f
    → ValidJudgment ⸨fst ⸨fst ⸨t x⸩⸩⸩ x
     -- ^ (∷ (∶ P f) (∶ Q g)), P is a predicate. the predicate that x is typed at...
      -- Q is similar predicate for the codomain
    → ValidJudgment ⸨fst ⸨snd ⸨t x⸩⸩⸩ ⸨f x⸩
  | defeq : ValidJudgment α x
    → DefEq α β
    → ValidJudgment β x

syntax "defeq" ident,*        : tactic
syntax "step" ident,*         : tactic
syntax "judge" ident,*        : tactic

macro_rules
  | `(tactic| defeq $fn:ident,*) => do
    let nms : Array (Lean.TSyntax `tactic) ← (Array.mk <$> (fn.getElems.toList.mapM (fun name =>
      let nm := Lean.mkIdent (Lean.Name.mkStr `DefEq name.getId.toString)
      `(tactic| apply $nm))))

    `(tactic| $[$nms];*)
  | `(tactic| step $fn:ident,*) => do
    let nms : Array (Lean.TSyntax `tactic) ← (Array.mk <$> (fn.getElems.toList.mapM (fun name =>
      let nm := Lean.mkIdent (Lean.Name.mkStr `IsStep name.getId.toString)
      `(tactic| apply $nm))))

    `(tactic| $[$nms];*)
  | `(tactic| judge $fn:ident,*) => do
    let nms : Array (Lean.TSyntax `tactic) ← (Array.mk <$> (fn.getElems.toList.mapM (fun name =>
      let nm := Lean.mkIdent (Lean.Name.mkStr `ValidJudgment name.getId.toString)
      `(tactic| apply $nm))))

    `(tactic| $[$nms];*)
