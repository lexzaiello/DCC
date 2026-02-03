import Mathlib.Data.Nat.Notation

/-
- Need some kind of mechanism to apply judgments.

We could use Σ for this.

(Σ t_app) : Prop → Prop → Prop

We need some mechanism to traverse the context that is well-typed.
This suggests that Σ is different from :.

This feels like reaching the end of a list. Maybe instead of snd and fst,
we want pattern mathcing.

fst + (snd exists_case nil_case)

So, our context now becomes:

(⊢ t_app judge_f judge_x) : Prop
We represent function types now as:

Pi t_in t_out

And, t_in : Prop → Prop

So we can only build the asserted type from the known ok types.

We should be able to make certain known ok types dynamically.

For example, id:

(∶ (u.succ) (Ty u)) : (Ty u) → Prop

Unclear how we continue passing the context in.

The obvious way is to do substitution.

I don't like having "state."

The idea is that the assertion for (f x y) sees (Σ t_app

- The input register should produce as an input a type in universe u matching the
level of Pi.

id.{[m]} : (Pi (const' (Type m.succ) Prop (Type m)) _)

fst and snd always produce as final outputs types, since they are mainly used
in the t_in position.

Terms get inserted via judgments by the Kernel.
fst and snd do not have universe level arguments, since these can be inferred.

TODO: we will probably need some mechanism to split a stream / context.
Duplicate it that only lives in Prop.

We could derive this as shorthand from both.

What about output types?
It feels like they should receive the context as well?
There is no circumstance in which they won't.
However, (Pi.{{m, n]} (t_in : Prop → Type m) (t_out : Prop → Type n)) : Type n

Another potential interpretation of ⊢.

The thing I'm wondering is if Pi is even necessary.

fst on a judgment just returns the type.
However, snd is not legal.

snd and fst should ONLY return Prop.

So how do we type (x : α)?

I feel like we ought to return Prop from our t_in
where the object being judged is the type.

(∶ type_of_type type)

I feel like high-key, with nested Pi,
we could do it instead with a partially applied Judge.
Idk.

Or, we could it by asserting that the output Pi expression has some type.
-/

abbrev Level := ℕ

inductive Expr where
  | app   : Expr  → Expr → Expr
  | ty    : Level → Expr
  | Pi    : Expr -- Pi : (Prop → Prop) → (Prop → Prop) → (Type 0)
  | judge : Level → Expr -- (: T x) : Prop - this is asserting that (x : T)
  | sigma : Level → Expr -- (Σ t_app (: T_f f) (: T_x x)) - this is asserting ((f x) : t_app)
  | prop  : Expr -- as usual
  | fst   : Expr
  /-
    snd has a x_case for when the snd value exists,
    and a nil case for when it does not exist. The nil_case receives niothing.
    ⸨snd x_case nil_case⸩
  -/
  | snd   : Expr
  | comp  : Expr -- for composing context traversal functions.
  /-
    ^ To traverse contexts. snd (Σ t_app (: t_f f) (: t_x x)) = (: t_x x)
  -/
  /-
    The standard combinators.
  -/
  | const' : Level → Level → Expr -- α → β → α

open Expr

def sort_to_expr : Level → Expr
  | 0 => prop
  | .succ n => ty n

syntax "⟪" term,+ "⟫"      : term
syntax "⸨" term+ "⸩"       : term

notation "Ty" => Expr.ty
notation "Prp" => Expr.prop
notation "∶" => Expr.judge
notation "⊢" => Expr.sigma

macro_rules
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f $x)
  | `(⸨ $f $x:term $args:term*⸩) => `(⸨ (Expr.app $f $x) $args*⸩)

infixr:90 " ∘ " => (fun f g => ⸨Expr.comp f g⸩)

/-
None of the terms we introduced above have step rules except for composition, app
and sapp.
-/
inductive IsStep : Expr → Expr → Prop
  | const' : IsStep ⸨(const' m n) _α _β x y⸩ x
  | comp   : IsStep ⸨(f ∘ g) x⸩ ⸨f ⸨g x⸩⸩
  | fst    : IsStep ⸨fst ⸨(⊢ m) t_app judge_f judge_x⸩⸩ judge_f
  | snd    : IsStep ⸨snd ⸨(⊢ n) t_app judge_f judge_x⸩⸩ judge_x
  -- snd can only return new Props, so we can't project on a judge.
  -- we need a default value, then.
  | snd_no : IsStep ⸨snd ⸨(∶ n) _a _b⸩⸩ ⸨(∶ n) _a _b⸩
  | left   : IsStep f f'
    → IsStep ⸨f x⸩ ⸨f' x⸩
  | right  : IsStep x x'
    → IsStep ⸨f x⸩ ⸨f x'⸩

/-
Assertions reject the context and just output
a type of type (Type m).
-/
def mk_assert (α : Expr) (m : Level) : Expr :=
  ⸨(const' 0 0) Prp Prp ⸨(∶ m.succ) (Ty m) α⸩⸩

/-
(α : Type u) → (β: Type v) corresponds to:

(Pi (const' (Type u) Prop α) (const' (Type v) Prop β))
(Pi.{{m, n]} (t_in : Prop → Type m) (t_out : Prop → Type n)) : Type n, due to this rule.
-/
def mk_arrow (α β : Expr) (m n : Level) : Expr :=
  let t_in := mk_assert α m
  let t_out := mk_assert β n

  ⸨Pi t_in t_out⸩

/-
const' : (α : Type m) → (β : Type n) → α → β → α

At (x : α) argument, we have (const' α β) in the judgment list. This is:
⊢ _ (⊢ _ (∶ t_const const') (∶ t_α α))

So, we output (∶ t_α α)
-/
def const'.type (m n : Level) : Expr :=
  let α := mk_assert (Ty m) m.succ
  let β := mk_assert (Ty n) n.succ
  -- with ⊢ _ (⊢ _ (∶ t_const const) (∶ (Ty m) α)) (∶ (Ty n) β)
  -- in scope. We select (∶ (Ty m) α)
  -- with (snd ∘ fst)
  let x := (snd ∘ fst)
  -- with ⊢ _ (⊢ _ (⊢ _ (∶ t_const const) (∶ (Ty m) α)) (∶ (Ty n) β)) (∶ α x) in scope
  let y := (fst ∘ fst)

  -- with ⊢ _ (⊢ _ (⊢ _ (⊢ _ (∶ t_const const) (∶ (Ty m) α)) (∶ (Ty n) β)) (∶ α x)) (∶ β y) in scope
  let out := (fst ∘ fst)

  ⸨Pi α ⸨Pi β ⸨Pi x ⸨Pi y out⸩⸩⸩⸩

/-
Pi : mk_arrow (Pair _ _) Ty
-/

inductive ValidJudgment : Expr → Expr → Prop
  | judge : ValidJudgment t (Ty m)
    → ValidJudgment x t
    → ValidJudgment ⸨(∶ m) t x⸩ Prp
  | sigma : ValidJudgment t_app (Ty o)
    → ValidJudgment ⸨(∶ m) t_f f⸩ Prp
    → ValidJudgment ⸨(∶ n) t_x x⸩ Prp
    → ValidJudgment ⸨f x⸩ t_app
    → ValidJudgment ⸨(⊢ o) t_app ⸨(∶ m) t_f f⸩ ⸨(∶ n) t_x x⸩⸩ Prp
  | fst   : ValidJudgment fst (mk_arrow Prp Prp 0 0)
  | snd   : ValidJudgment snd (mk_arrow Prp Prp 0 0)
  | prp   : ValidJudgment Prp (Ty 0)
  | ty    : ValidJudgment (Ty m) (Ty m.succ)
  | comp  : ValidJudgment comp (mk_arrow -- comp : (Prop → Prop) → (Prop → Prop) → Prop → Prop
    (mk_arrow Prp Prp 0 0) -- Prop → Prop
    (mk_arrow
      (mk_arrow Prp Prp 0 0) -- Prop → Prop
      (mk_arrow Prp Prp 0 0) 1 1) 1 1)
  | pi    : ValidJudgment (Pi m n) (mk_arrow 
