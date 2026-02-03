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
-/

abbrev Level := ℕ

inductive Expr where
  | app   : Expr  → Expr → Expr
  | ty    : Level → Expr
  | Pi    : Level → Expr -- Pi.{[m]} _ : _ → Sort m
  | judge : Level → Expr -- (: T x) : Prop - this is asserting that (x : T)
  | sigma : Expr -- (Σ t_app (: T_f f) (: T_x x)) - this is asserting ((f x) : t_app)
  | prop  : Expr -- as usual
  | fst   : Expr
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
  | fst    : IsStep ⸨fst ⸨⊢ t_app judge_f judge_x⸩⸩ judge_f
  | snd    : IsStep ⸨snd ⸨⊢ t_app judge_f judge_x⸩⸩ judge_x
  | left   : IsStep f f'
    → IsStep ⸨f x⸩ ⸨f' x⸩
  | right  : IsStep x x'
    → IsStep ⸨f x⸩ ⸨f x'⸩

/-
(α : Type u) → (β: Type v) corresponds to:

(Pi (const' (Type u) Prop α) (const' (Type v) Prop β))
-/
def mk_arrow (α β : Expr) (m n : Level := 0) : Expr :=
  let t_in := ⸨(const' u.succ 1) (Type u) Prop α⸩
  let t_out
  ⸨(Pi m) t_in 

/-
Pi : mk_arrow (Pair _ _) Ty
-/

inductive ValidJudgment : Expr → Expr → Prop
  | Pi    : ValidJudgment bdy (Prod α β)
    → ValidJudgment (Pi bdy) (Ty m)
  | prop  : ValidJudgment Prp (Ty 0)
  | ty    : ValidJudgment (Ty m) (Ty m.succ)
  | pair  : ValidJudgment x α
    → ValidJudgment xs β
    → ValidJudgment ⟪x, xs⟫ (Prod α β)
  | Prod  : ValidJudgment α (Ty m)
    → ValidJudgment β (Ty n)
    → ValidJudgment (Prod α β) (Ty (max m n).succ)
  | sigma : ValidJudgment t (Ty m)
    → ValidJudgment x t
    → ValidJudgment ⸨(sigma m) t x⸩ Prp
  | comp  : ValidJudgment g (mk_arrow α β)
    → ValidJudgment f (mk_arrow β γ)
    → ValidJudgment (f ∘ g) (mk_arrow α γ)
  | app   : ValidJudgment f (Pi ⟪⟪assert, rst⟫, Γ⟫)
    → ValidJudgment ⸨assert Γ⸩ (Ty m)
    → ValidJudgment arg ⸨assert Γ⸩
    → ValidJudgment ⸨f arg⸩ ⟪rst, ⟪⸨(sigma m) ⸨assert Γ⸩ arg⸩, Γ⟫⟫
  | sapp  : ValidJudgment ⸨(sigma m) t_f f⸩ Prop
    → ValidJudgment ⸨(sigma n) t_x x⸩ Prop
    → ValidJudgment ⸨f x⸩ t'
    -- (sapp a b) reduces to 
    → ValidJudgment (sapp ⸨(sigma m) t_f f⸩ ⸨(sigma n) t_x x⸩) Prop

