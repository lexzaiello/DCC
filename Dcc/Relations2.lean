import Mathlib.Data.Nat.Notation

/-
Summary of improvements:

- use sigmas instead of Pi

(:: f g) x = (:: f(x), g(f(x)))
snd (:: f(x), g(f(x))) = g(f(x))
fst (:: f(x), g(f(x))) = f(x)

f(x) is domain, g(f(x)) is codomain.

f(x) are a list of hypotheses kind of.

we can use judgments to make (:: f g) : Prop.

f is a judgment. then derive g type from the type contained in (∶ Tf f).

This is nice because :: doesn't need to be special-cased.

It's also nice because we only ever need to type the head element.

Is there a way to unify : T x with ::? Probably not.
We don't need :: to be Prop. We can use judgments to supply it nicely.

f in :: f g is a list of hypotheses. g is the conclusion.

(I ((∶ n.succ) (Ty n) α) x) : α

I : (∷ (I Prp)

unclear whether fst / snd should also be for (∶ T x).

Also unclear whether (∶ T x) is necessary. but it feels like it.

Reduction rules for (∷ f g) will become slightly messy if we use
judgment arguments.

We will have to though if we don't want to special-case cons.

I think we can also derive g from f.

(∷ (∶ Tf f) g) x = (∷ (∶ (Tf x) f) (g (f x)))

Do we even need S/K/I? Can we derive these from sigma / fst / snd?

fst projection is like K.

snd projection or something is like S.

wait. snd is S.

What about I?

I is intrinsic.

We can derive K. Absolutely.

I think we can actually assume that f is curried.

We can simplify the rule, I think.

The operational semantics shouldn't care about the type.

def Cons.elim_right {α : Type} {P : α → Prop} {Q : ∀ {x : α}, P x → Prop}
  (f : ∀ (x : α), P x) (g : ∀ {x : α}, Q (f x)) (x : α) : Q (f x) := by
  apply g

^ P x in f is (∶ Ty) in app infer rule.
-/

abbrev Level := ℕ

inductive Expr where
  | I     : Level → Expr
  | judge : Level → Expr
  | type  : Level → Expr
  | prop  : Expr
  | cons  : Expr
  | fst   : Expr
  | snd   : Expr
  | app   : Expr → Expr → Expr

open Expr

syntax "⸨" term+ "⸩"       : term

notation "Π'" => Expr.Pi
notation "Ty" => Expr.type
notation "Prp" => Expr.prop
notation "∶" => Expr.judge
notation "∷" => Expr.cons

macro_rules
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f $x)
  | `(⸨ $f $x:term $args:term*⸩) => `(⸨ (Expr.app $f $x) $args*⸩)

inductive IsStep : Expr → Expr → Prop
  | i      : IsStep ⸨(I m) α x⸩ x
  | subst  : IsStep ⸨⸨∷ f g⸩ x⸩ ⸨∷ ⸨f x⸩ ⸨g ⸨f x⸩⸩⸩
  | fst    : IsStep ⸨fst ⸨∷ f g⸩⸩ f
  | snd    : IsStep ⸨snd ⸨∷ f g⸩⸩ g
  | fstj   : IsStep ⸨fst ⸨(∶ m) f g⸩⸩ f
  | sndj   : IsStep ⸨snd ⸨(∶ m.succ) f g⸩⸩ ⸨(∶ m) g⸩
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
I type:

I.{[m]} : ∀ (α : Ty m), α → α
-/
def I.type (m : Level) : Expr :=
  ⸨∷ ⸨(∶ m) (Ty m)⸩ ⸨∷ snd fst⸩⸩

inductive ValidJudgment : Expr → Expr → Prop
  | ty    : ValidJudgment ⸨(∶ m.succ.succ) (Ty m.succ) (Ty m)⸩ (Ty m)
  | prp   : ValidJudgment ⸨(∶ 1) (Ty 0) Prp⸩ Prp
  | app   : ValidJudgment ⸨(∶ m) ⸨∷ α β⸩ f⸩ f
    → ValidJudgment ⸨α x⸩ x
    → ValidJudgment ⸨(∶ m) ⸨snd ⸨⸨∷ α β⸩ x⸩⸩ ⸨f x⸩⸩ ⸨f x⸩
  | defeq : ValidJudgment ⸨(∶ m) α x⸩ x
    → DefEq α β
    → ValidJudgment ⸨(∶ m) β x⸩ x
  | i     : ValidJudgment ⸨(∶ m) (I.type m) (I m)⸩ (I m)
