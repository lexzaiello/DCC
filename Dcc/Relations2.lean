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
-/

abbrev Level := ℕ

inductive Expr where
  | K     : Level → Level → Expr -- Dependent K
  | K'    : Level → Level → Expr -- Nondependent K
  | S     : Level → Level → Level → Expr -- Dependent S
  | judge : Level → Expr
  | type  : Level → Expr
  | prop  : Expr
  | cons  : Expr
  | fst   : Expr
  | snd   : Expr
  | app   : Expr → Expr → Expr

open Expr

syntax "⸨" term+ "⸩"                  : term
syntax "::[" term,+ "]"               : term
syntax term "∶" "(" term "∶" term ")" : term
-- ^ for making judgments: (x : (α : Ty m))

notation "Π'" => Expr.Pi
notation "Ty" => Expr.type
notation "Prp" => Expr.prop
notation "∶" => Expr.judge
notation "∷" => Expr.cons

macro_rules
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f $x)
  | `(⸨ $f $x:term $args:term*⸩) => `(⸨ (Expr.app $f $x) $args*⸩)
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.app (Expr.app Expr.cons $x) ::[$xs,*])
  | `(x ∶ (α ∶ Ty m)) => `(⸨(∶ m) α x⸩)

inductive IsStep : Expr → Expr → Prop
  | subst  : IsStep ⸨⸨∷ ⸨(∶ m) P f⸩ ⸨(∶ n) Q g⸩⸩ x⸩
    ⸨∷ ⸨(∶ m) ⸨P x⸩ ⸨f x⸩⸩ ⸨(∶ n) ⸨Q x ⸨f x⸩⸩ ⸨g x⸩⸩⸩
  | k      : IsStep ⸨(K m n) α β x y⸩ x
  | k'     : IsStep ⸨(K' m n) α β x y⸩ x
  | s      : IsStep ⸨(S m n o) α β γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | fst    : IsStep ⸨fst ⸨∷ f g⸩⸩ f
  | snd    : IsStep ⸨snd ⸨∷ f g⸩⸩ g
  | fstj   : IsStep ⸨fst ⸨(∶ m) f g⸩⸩ f
  | sndj   : IsStep ⸨snd ⸨(∶ m) f g⸩⸩ g
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
