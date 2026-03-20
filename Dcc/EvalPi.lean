import Dcc.Ast
import Dcc.Eval

/-
All Π expressions are prefixed by a type combinator.

not sure if this is even necessary.

we need a really clever decreasing measure.
We can do this by just prefixing unsubstituted Π.

Another alternative around this is:
do we actually need to copy x into β?

if we want full substitution, yes.

we can just have our evaluation rule such that
Π only substitutes once.

(arg n) (Π

B (Π ...) I

evaluates, but Π does not.

This is ugly.

we always require α substitution to step.
can be clever with size, as such.
β we don't.

Π size is literally just the sum of all the Ty expressions, I think.
We just can't recurse if we get a new Π inserted in.

We don't recurse under Π, we recurse under the original expr.
The expression's sum of Π should decrease.

IDEA JUST DROPPED. Size of all nested Π binders * the argument size.
-/

inductive Expr.RedPi : Expr → Expr → Prop
  | congr_cod : Expr.RedPi β β'
    → Expr.RedPi (SK Π α, β) (SK Π α, β')
  | step_pi   : Expr.RedPi (SK (α x)) α'
    → Expr.RedPi (SK ((Π α, β) x)) (SK (Π α', (β x)))
  | step_ty   : Expr.RedTy e e'
    → Expr.RedPi e e'

inductive Expr.PiSize : Expr → ℕ → Prop
  | pi_app  : Expr.PiSize (SK (α x)) m
    → Expr.PiSize (SK (β x)) n
    → Expr.PiSize (SK ((Π α, β) x)) (m + n + 1)
  | ty_size : Expr.TySize e (n + 1) -- to exclude counting Π apps from ty_size
    → Expr.PiSize e (n + 1)

def Expr.pi_size : Expr → Option ℕ
  | SK ((Π α, β) x) =>
    match Expr.pi_size (SK (α x)), Expr.pi_size (SK (β x)) with
    | .some m, .some n =>
      .some (m + n + 1)
    | _, _ => .none
  | e =>
    let ty_size := Expr.ty_size e
    match ty_size with
    | .zero => .none
    | n => .some n

theorem Expr.PiSize.sound : Expr.pi_size e = .some n → Expr.PiSize e n := by
  intro h
  unfold Expr.pi_size at h
  split at h
  · rename_i x₁ α β x
    split at h
    · rename_i heq₁ heq₂
      have h := Expr.PiSize.pi_app (Expr.PiSize.sound heq₁) (Expr.PiSize.sound heq₂)
      simp_all only [Option.some.injEq]
    · contradiction
  · rename_i x₁ ih
    simp_all
    split at h
    · contradiction
    simp at h
    cases n
    · contradiction
    · exact .ty_size (Expr.TySize.sound h)

