import Mathlib.Data.Nat.Notation
import Mathlib.Tactic

/-
⊢ : Prop → Prop → Prop → Prop
Pi : (Prop → Prop) → (Prop → Prop) → Type 0

Universe levels are probably wrong in a few places.

We should allow t_out to decide if it wants to make another ⊢.

⊢ : Type → Prop → Prop → Prop

So, out_t in a Pi takes judge_f and judge_x.

Pi : (Prop → Prop) → (Prop → Prop → Prop) → (Type 1)

Pi t_in (⊢ inner_pi)
-/

abbrev Level := ℕ

inductive Expr where
  | app   : Expr  → Expr → Expr
  | ty    : Level → Expr
  | Pi    : Expr -- Pi : (Prop → Prop) → (Prop → Prop → Prop) → (Type 0). This is because t_out needs to know the judged input type.
  | judge : Level → Expr -- (: T x) : Prop - this is asserting that (x : T)
  | vdash : Level → Expr -- ⊢ (t_app : Type) (judge_f : Prop) (judge_x : Prop)
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

syntax "⸨" term+ "⸩"       : term

notation "Ty" => Expr.ty
notation "Prp" => Expr.prop
notation "∶" => Expr.judge
notation "⊢" => Expr.vdash

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
  | fst_j  : IsStep ⸨fst ⸨(∶ m) t x⸩⸩ ⸨(∶ m.succ) (Ty m) t⸩
  | fst    : IsStep ⸨fst ⸨(⊢ m) t_app judge_f judge_x⸩⸩ judge_f
  | snd    : IsStep ⸨snd ⸨(⊢ m) t_app judge_f judge_x⸩⸩ judge_x
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
def mk_assert_in (α : Expr) (m : Level) : Expr :=
  ⸨(const' 0 0) Prp Prp ⸨(∶ m.succ) (Ty m) α⸩⸩

def mk_assert_out (α : Expr) (m : Level) : Expr :=
  ⸨(⊢ m) α⸩

/-
(α : Type u) → (β: Type v) corresponds to:

Pi (const' Prp Prp α) (⊢ β)
-/
def mk_arrow (α β : Expr) (m n : Level) : Expr :=
  let t_in := mk_assert_in α m

  ⸨Pi t_in ⸨(⊢ n) β⸩⸩

def ret_pi (the_pi : Expr) : Expr :=
  ⸨(⊢ 1) the_pi⸩

/-
const' : (α : Type m) → (β : Type n) → α → β → α

At (x : α) argument, we have (const' α β) in the judgment list. This is:
⊢ _ (⊢ _ (∶ t_const const') (∶ t_α α))

So, we output (∶ t_α α)
-/
def const'.type (m n : Level) : Expr :=
  let α := mk_assert_in (Ty m) m.succ
  let β := mk_assert_in (Ty n) n.succ

  -- with ⊢ _ (⊢ _ (∶ t_const const) (∶ (Ty m) α)) (∶ (Ty n) β)
  -- in scope. We select (∶ (Ty m) α)
  -- with (snd ∘ fst)
  let x := (snd ∘ fst)
  -- with ⊢ _ (⊢ _ (⊢ _ (∶ t_const const) (∶ (Ty m) α)) (∶ (Ty n) β)) (∶ α x) in scope
  let y := (fst ∘ fst)

  -- with (⊢ (const' α β x)) and (: t_y y) in scope.
  let out := ⸨(const' 0 0) Prp Prp⸩

  ⸨Pi α (ret_pi ⸨Pi β (ret_pi ⸨Pi x (ret_pi ⸨Pi y out⸩)⸩)⸩)⸩

/-
(∶ m) : ∀ (α : Type m), α → Prop
-/
def judge.type (m : Level) : Expr :=
  let α := mk_assert_in (Ty m) m.succ

  -- with (⊢ _ (:t_judge (judge m)) (: (Ty m) α)) in scope
  let x := snd

  ⸨Pi α (ret_pi ⸨Pi x (mk_assert_out Prp 0)⸩)⸩

/-
⊢ m : (Type m) → (judge_f : Prop) → (judge_x : Prop) → Prop

Used to denote function application as a kind of tree.
-/
def vdash.type (m : Level) : Expr :=
  ⸨Pi (mk_assert_in (Ty m) m.succ) (ret_pi ⸨Pi (mk_assert_in Prp 0) (ret_pi ⸨Pi (mk_assert_in Prp 0) (mk_assert_out Prp 0)⸩)⸩)⸩

/-
comp : (Prop → Prop) → (Prop → Prop) → Prop → Prop
-/
def comp.type : Expr :=
  (mk_arrow
    (mk_arrow Prp Prp 0 0) -- Prop → Prop
    (mk_arrow
      (mk_arrow Prp Prp 0 0) -- Prop → Prop
      (mk_arrow Prp Prp 0 0) 1 1) 1 1)

/-
Pi : ((Prop → Prop) → (Prop → (Prop → Prop))) : (Type 0)
-/
def pi.type : Expr :=
  let t_in := (mk_arrow Prp Prp 0 0)
  let t_out := (mk_arrow Prp (mk_arrow Prp Prp 0 0) 0 1)
  (mk_arrow t_in
    (mk_arrow t_out (Ty 0) 1 1) 1 1)

/-
(ValidJudgment t x : Prop) = ((∶ t x) : Prop)

ValidJudgment ⸨Pi t_in t_out⸩ f -> (∶ ⸨Pi t_in t_out⸩ f)

How do we recover ⊢ from partial apps?

- ValidJudgment always gives the type of the type, not just the type

Prop : (Ty 0) in Lean,

ValidJudgment (∶ (Ty 0) Prp) in our language.

⊢ (f : t)
-/

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | step    : IsStep e e' → DefEq e e'
  | symm    : DefEq e₁ e₂ → DefEq e₂ e₁
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ⸨f x⸩ ⸨f' x⸩
  | right   : DefEq x x'  → DefEq ⸨f x⸩ ⸨f x'⸩
  | vdash   : DefEq ⸨(⊢ m) t_fx ⸨(∶ n) t_f f⸩ ⸨(∶ o) t_x x⸩⸩ ⸨(∶ m) t_fx ⸨f x⸩⸩
  --| vdash   : DefEq ⸨(∶ m) t_x x⸩ ⸨(⊢ n) ⸨(∶ m) t_x x⸩ _a _b⸩
  /-| subst   : DefEq ($ (Pi α₁ β₁ map_arg₁), x) ($ (Pi α₂ β₂ map_arg₂), x)
    → DefEq (Pi α₁ β₁ map_arg₁) (Pi α₂ β₂ map_arg₂)-/

inductive ValidJudgment : Expr → Prop
  | judge : ValidJudgment ⸨(∶ 1) (judge.type m) (∶ m)⸩
  | vdash : ValidJudgment ⸨(∶ 1) (vdash.type m) (⊢ m)⸩
  | fst   : ValidJudgment ⸨(∶ 1) (mk_arrow Prp Prp 0 0) fst⸩ -- fst : Prop → Prop
  | snd   : ValidJudgment ⸨(∶ 1) (mk_arrow Prp Prp 0 0) snd⸩ -- snd : Prop → Prop
  | prp   : ValidJudgment ⸨(∶ 1) (Ty 0) Prp⸩ -- Prop : Ty 0
  | ty    : ValidJudgment ⸨(∶ (m.succ.succ)) (Ty m.succ) (Ty m)⸩ -- Ty m : Ty m.succ
  | comp  : ValidJudgment ⸨(∶ 1) comp.type comp⸩
  /-
    Pi accepts a map on the context producing the input type,
    and a map on the context producing the output type.

    Note that the resulting (∶ t x) judgements for t_in and t_out
    represent the TYPE of the asserted type.

    Pi : (Prop → Prop) → (Prop → Prop) → (Ty 0)
  -/
  | pi    : ValidJudgment ⸨(∶ 1) pi.type Pi⸩
  /-
    In the normal application case, f has a normal judgment.
    A Pi expression.
  -/
  | app  : ValidJudgment ⸨(∶ 1) ⸨Pi t_in t_out⸩ f⸩
    → ValidJudgment ⸨(∶ n) t_x x⸩
    -- t_in will produce another judgment. ⸨: type_of_x_type x_type⸩
    -- t_x : (Type n)
    → ValidJudgment ⸨(∶ n.succ) (Ty n) t_x⸩
    → DefEq ⸨t_in ⸨(∶ 1) ⸨Pi t_in t_out⸩ f⸩⸩ ⸨(∶ n.succ) (Ty n) t_x⸩
    -- t_out decides what to to do with the context and make a new judgment
    → ValidJudgment ⸨t_out ⸨(∶ 1) ⸨Pi t_in t_out⸩ f⸩ ⸨(∶ n) t_x x⸩⸩
  /-
    Partial application produces a conjoined context. ⊢ judge_f judge_x.
    This is our "context:" ⸨⊢ judge_f judge_inner_f judge_inner_x⸩
    This is the result of the partially applied app (a nested Pi):
      ⸨(∶ m) ⸨Pi t_in t_out⸩⸩
  -/
  | parapp : ValidJudgment ⸨(⊢ 1) ⸨Pi t_in t_out⸩ judge_inner_f judge_inner_x⸩
    → ValidJudgment ⸨(∶ n) t_x x⸩
    → ValidJudgment ⸨(∶ n.succ) (Ty n) t_x⸩
    -- Feed our context into t_in. This should produce the same judgment
    -- as (t_x : t_t_x)
    → DefEq ⸨(∶ n.succ) (Ty n) t_x⸩ ⸨t_in ⸨(⊢ 1) ⸨Pi t_in t_out⸩ judge_inner_f judge_inner_x⸩⸩
    → ValidJudgment ⸨t_out ⸨(⊢ 1) ⸨Pi t_in t_out⸩ judge_inner_f judge_inner_x⸩ ⸨(∶ n) t_x x⸩⸩
  | defeq   : ValidJudgment j₁
    → DefEq j₁ j₂
    → ValidJudgment j₂
  /-
    Base combinator types:
  -/
  | const'  : ValidJudgment ⸨(∶ 1) (const'.type m n) (const' m n)⸩

/-
Helper macros for proofs about judgments.
-/

syntax "defeq" ident,*        : tactic
syntax "step" ident,*         : tactic
syntax "judge" ident,*         : tactic

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

/-
Some simp lemmas for proofs.

Step simp lemmas, defeq simp lemmas.

| const' : IsStep ⸨(const' m n) _α _β x y⸩ x
| comp   : IsStep ⸨(f ∘ g) x⸩ ⸨f ⸨g x⸩⸩
| fst_j  : IsStep ⸨fst ⸨(∶ m) t x⸩⸩ ⸨(∶ m.succ) (Ty m) t⸩
| fst    : IsStep ⸨fst ⸨⊢ t_app judge_f judge_x⸩⸩ judge_f
| snd    : IsStep ⸨snd ⸨⊢ t_app judge_f judge_x⸩⸩ judge_x
| snd_no : IsStep ⸨snd ⸨(∶ n) _a _b⸩⸩ ⸨(∶ n) _a _b⸩
| left   : IsStep f f' → IsStep ⸨f x⸩ ⸨f' x⸩
| right  : IsStep x x' → IsStep ⸨f x⸩ ⸨f x'⸩
-/

@[simp] theorem defeq_refl (e : Expr) : DefEq e e := DefEq.refl

@[simp] theorem step_const' : IsStep ⸨(const' m n) _α _β x y⸩ x := IsStep.const'

@[simp] theorem step_comp : IsStep ⸨(f ∘ g) x⸩ ⸨f ⸨g x⸩⸩ := IsStep.comp

@[simp] theorem step_fst_j : IsStep ⸨fst ⸨(∶ m) t x⸩⸩ ⸨(∶ m.succ) (Ty m) t⸩ := IsStep.fst_j

@[simp] theorem step_fst : IsStep ⸨fst ⸨(⊢ m) t_app judge_f judge_x⸩⸩ judge_f := IsStep.fst

@[simp] theorem step_snd : IsStep ⸨snd ⸨(⊢ m) t_app judge_f judge_x⸩⸩ judge_x := IsStep.snd

@[simp] theorem step_left : IsStep f f' → IsStep ⸨f x⸩ ⸨f' x⸩ := IsStep.left

@[simp] theorem step_right : IsStep x x' → IsStep ⸨f x⸩ ⸨f x'⸩ := IsStep.right

@[simp] theorem ty_well_typed : ValidJudgment ⸨(∶ m.succ.succ) (Ty m.succ) (Ty m)⸩ := ValidJudgment.ty

/-
judge / : : ∀ (α : Type), α → Prop
-/
theorem judge_well_typed : ValidJudgment ⸨(∶ m.succ) (Ty m) α⸩
  → ValidJudgment ⸨(∶ m) α x⸩
  → ValidJudgment ⸨(∶ 0) Prp ⸨(∶ m) α x⸩⸩ := by
  intro h_t_α h_t_x
  judge defeq, parapp, defeq, app, judge
  exact m
  exact h_t_α
  simp
  defeq trans, step
  step const'
  defeq refl, refl
  assumption
  assumption
  defeq symm, trans, step
  step snd
  defeq refl
  unfold mk_assert_out
  defeq trans, left, right, vdash, vdash


/-theorem const'_well_typed : ValidJudgment ⸨(∶ m.succ) (Ty m) α⸩
  → ValidJudgment ⸨(∶ m) α x⸩
  → ValidJudgment ⸨(∶ n.succ) (Ty n) β⸩
  → ValidJudgment ⸨(∶ n) β y⸩
  → ValidJudgment ⸨(∶ m) α ⸨(const' m n) α β x y⸩⸩ := by
    intro h_t_α h_t_β h_t_x h_t_y
    judge defeq, parapp, defeq, parapp, defeq, parapp, defeq, parapp, defeq, app, const'
    exact m
    exact n
    exact h_t_α
    judge ty
    defeq symm, trans, step
    step const'
    defeq refl, left, left, right, trans, step
    step const'
    simp
-/
