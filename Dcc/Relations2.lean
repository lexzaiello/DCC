import Mathlib.Data.Nat.Notation

/-
See abstract.lean for more.
-/

/-
What about (∶ T x) judgments?

def Cons.elim_right {α : Type} {P : α → Prop} {Q : ∀ {x : α}, P x → Prop}
  (f : ∀ (x : α), P x) (g : ∀ {x : α}, Q (f x)) (x : α) : Q (f x) := by
  apply g
                            ^
We don't actually take f(x) as an argument in the term. Just x.
f x gets passed into the type, not the term.

I m : ⸨∷ ⸨(∶ 0) ⸨(∶ m.succ) (Ty m)⸩ ⸨(I m.succ) (Ty m)⸩⸩ ⸨(∶ 0) (∶ m) (I m)⸩

P(x) doesn't necessarily need to be a Prop,
it may be elucidating to think about the type of cons first.

Cut elimination doesn't need to be restricted to Prop.


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
  | subst  : IsStep ⸨⸨∷ ⸨(∶ m) P f⸩ ⸨(∶ n) Q g⸩⸩ x⸩
    ⸨∷ ⸨(∶ m) ⸨P x⸩ ⸨f x⸩⸩ ⸨(∶ n) ⸨Q ⸨f x⸩⸩ ⸨g x⸩⸩⸩
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
I type:

I.{[m]} : ∀ (α : Ty m), α → α

This suggests α is a proof of (∶ m.succ) (Ty m) α
-/
def I.type (m : Level) : Expr :=
  ⸨∷ ⸨(∶ 0) ⸨(∶ m.succ) (Ty m)⸩ ⸨(I m.succ) (Ty m)⸩⸩
    ⸨(∶ 0) ⸨∷ ⸨(∶ 0) (∶ m) (I m)⸩ ⸨(∶ m) (I (m.succ)) (I m)⸩⸩ (I m)⸩⸩

inductive ValidJudgment : Expr → Expr → Prop
  | ty    : ValidJudgment ⸨(∶ m.succ.succ) (Ty m.succ) (Ty m)⸩ (Ty m)
  | prp   : ValidJudgment ⸨(∶ 1) (Ty 0) Prp⸩ Prp
  | app   : ValidJudgment ⸨(∶ m) t f⸩ f
    → ValidJudgment ⸨fst ⸨fst ⸨t x⸩⸩⸩ x -- (∷ dom cod), dom produces a judgment (∶ α x),
      -- cod / snd produces a judgment (∶ (β (fst (t x))) (f x))
    → ValidJudgment ⸨snd ⸨t x⸩⸩ ⸨f x⸩
  | defeq : ValidJudgment α x
    → DefEq α β
    → ValidJudgment β x
  | i     : ValidJudgment ⸨(∶ m) (I.type m) (I m)⸩ (I m)

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

theorem I.well_typed : ValidJudgment ⸨(∶ m.succ) (Ty m) α⸩ α
  → ValidJudgment ⸨(∶ m) α x⸩ x
  → ValidJudgment ⸨(∶ m) α ⸨(I m) α x⸩⸩ ⸨(I m) α x⸩ := by
  intro h_t_α h_t_x
  judge defeq, app, defeq, app, i, defeq
  assumption
  defeq symm, trans, right, right, step
  step subst
  defeq trans, right, step
  step fst
  defeq step
  step fstj
  defeq trans, right, step
  step subst
  defeq step
  step snd
  judge defeq
  assumption
  defeq symm, trans, right, right, left, step
  step subst
  defeq trans, right, right, step
  step subst
  defeq trans, right, step
  step fst
  defeq trans, step
  step fstj
  defeq left, right, step
  step i
  defeq trans, right, left, step
  step subst
  defeq trans, right, step
  step subst
  defeq trans, step
  step snd
  defeq trans, left, right, left, right, right, step
  step i
  defeq trans, left, right, step
  step i
  defeq trans, left, right, step
  step i
  defeq trans, right, step
  step i
  defeq symm, trans, right, step
  step i
  
