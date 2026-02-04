import Mathlib.Data.Nat.Notation
import Mathlib.Tactic

abbrev Level := ℕ

inductive Expr where
  | app   : Expr  → Expr → Expr
  | ty    : Level → Expr
  | Pi    : Expr -- Pi : (Prop → Prop) → (Prop → Prop → Prop) → (Type 0). This is because t_out needs to know the judged input type.
  | judge : Level → Expr -- (: T x) : Prop - this is asserting that (x : T)
  | vdash : Expr -- ⊢ (t_app : Prop) (judge_f : Prop) (judge_x : Prop)
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
    The standard SK, BCKW combinators.
  -/
  | const' : Level → Level → Expr -- α → β → α
  | const  : Level → Level → Expr -- dependent K
  /-
    Dependent C / flip.
    C x y z = x z y
    C : ∀ (x : α) (β : Type) (γ : α → β → Type) (f : ∀ (x : α)
      (y : β), γ x y) (y : β) (z : α), γ z y
  -/
  | flip   : Level → Level → Level → Expr-- dependent C / flip combinator
  /-
    both : ∀ (α : Type) (β : α → Type) (γ : ∀ (x : α), β x → Type)
      (f : ∀ (x : α) (y : β x), γ x y)
      (g : ∀ (x : α), β x)
      (x : α), γ x (g x)
  -/
  | both   : Level → Level → Level → Expr
  | id     : Level → Expr

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
  | id     : IsStep ⸨(Expr.id m) _α x⸩ x
  | both   : IsStep ⸨(both m n o) _α _β _γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | flip   : IsStep ⸨(Expr.flip m n o) _α _β _γ x y z⸩ ⸨x z y⸩
  | const' : IsStep ⸨(const' m n) _α _β x y⸩ x
  | comp   : IsStep ⸨(f ∘ g) x⸩ ⸨f ⸨g x⸩⸩
  | fst_j  : IsStep ⸨fst ⸨(∶ m) t x⸩⸩ ⸨(∶ m.succ) (Ty m) t⸩
  | fst    : IsStep ⸨fst ⸨⊢ t_app judge_f judge_x⸩⸩ judge_f
  | snd    : IsStep ⸨snd ⸨⊢ t_app judge_f judge_x⸩⸩ judge_x
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
  ⸨⊢ ⸨(∶ m.succ) (Ty m) α⸩⸩

/-
(α : Type u) → (β: Type v) corresponds to:

Pi (const' Prp Prp α) (⊢ β)
-/
def mk_arrow (α β : Expr) (m n : Level) : Expr :=
  let t_in := mk_assert_in α m

  ⸨Pi t_in (mk_assert_out β n)⸩

def ret_pi (the_pi : Expr) : Expr :=
  ⸨⊢ ⸨(∶ 1) (Ty 0) the_pi⸩⸩

def snd.type : Expr := (mk_arrow Prp Prp 0 0)
def fst.type : Expr := (mk_arrow Prp Prp 0 0)

/-
Turns Pi t_in t_out into Pi t_out t_in
-/
def flip_pi : Expr :=
  ⸨(flip 1 1 0) (mk_arrow Prp Prp 0 0) (mk_arrow Prp Prp 0 0)
    ⸨(const' 1 0) (mk_arrow Prp (Ty 0) 0 1) Prp ⸨(const' 1 0) (Ty 0) Prp Prp⸩⸩
    Pi⸩

def dup_vdash : Expr :=
  ⸨both 

/-
const' : (α : Type m) → (β : Type n) → α → β → α

At (x : α) argument, we have (const' α β) in the judgment list. This is:
⊢ _ (⊢ _ (∶ t_const const') (∶ t_α α))


-/
def const'.type (m n : Level) : Expr :=
  let α := mk_assert_in (Ty m) m.succ
  let β := mk_assert_in (Ty n) n.succ

  -- with ⊢ t_app_αβ (⊢ t_app_α judge_const' judge_α) judge_β
  -- in scope. We select (∶ (Ty m) α)
  -- with (snd ∘ fst)
  let x := (snd ∘ fst)
  -- with ⊢ _ (⊢ t_app_αβ (⊢ t_app_α judge_const' judge_α) judge_β) judge_x
  let y := (snd ∘ fst)

  /-
    The output type is:
    ⊢ (∶ (Ty m) α) .. ..
  -/
  let cpy := ⸨(both 0 0 0)
    Prp
    ⸨(const' 1 0) (Ty 0) Prp Prp⸩
    ⸨(const' 1 0) (mk_arrow Prp (Ty 0) 0 1) Prp
      ⸨(const' 1 0) (Ty 0) Prp
        (mk_arrow Prp (mk_arrow Prp Prp 0 0) 0 1)⸩⸩⸩
  let out := ⸨cpy (⊢ ∘ (snd ∘ fst ∘ fst)) ⸨(id 0) Prp⸩⸩

  ⸨Pi α (ret_pi ⸨Pi β (ret_pi ⸨Pi x (ret_pi ⸨Pi y out⸩)⸩)⸩)⸩

def const.type (m n : Level) : Expr :=
  let α := mk_assert_in (Ty m) m.succ
  -- takes α, makes a new (α → Type n)
  let β.α := Expr.snd
  let β.const := (⸨(const' 0 0) Prp Prp⸩ ∘ β.α)
  let β.const_out := (mk_assert_out (Ty n) n.succ)
  let β := (⸨(∶ 2) (Ty 1)⸩ ∘ (⸨flip_pi β.const_out⸩ ∘ β.const))

  let βx := ⸨(both 0 0 0)
      Prp
      ⸨(const' 0 1) (Ty 0) Prp Prp⸩
      ⸨(const' 0 1) (mk_arrow Prp Prp 0 0) Prp ⸨(const' 0 1) (Ty 0) Prp⸩⸩
      (⸨⊢ ⸨(∶ n.succ.succ) (Ty n.succ) (Ty n)⸩⸩ ∘ (snd ∘ fst))
      snd⸩

  /-
    to prepend a judgment and ourselves.
  -/
  let cpy := ⸨(both 0 0 0)
    Prp
    ⸨(const' 1 0) (Ty 0) Prp Prp⸩
    ⸨(const' 1 0) (mk_arrow Prp (Ty 0) 0 1) Prp
      ⸨(const' 1 0) (Ty 0) Prp
        (mk_arrow Prp (mk_arrow Prp Prp 0 0) 0 1)⸩⸩⸩
  let out := ⸨cpy (⊢ ∘ (snd ∘ fst ∘ fst)) ⸨(id 0) Prp⸩⸩

  let y_out := ⸨Pi
    βx
    out⸩ -- with ⊢ _ (⊢ _ (⊢ _ judge_α)judge x judge_y

  ⸨Pi α
    (ret_pi
      ⸨Pi β
        (ret_pi ⸨Pi (Expr.snd ∘ Expr.fst) (ret_pi y_out)⸩)⸩)⸩
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
  ⸨Pi (mk_assert_in (Ty m) m.succ)
    (ret_pi ⸨Pi (mk_assert_in Prp 0) (ret_pi ⸨Pi (mk_assert_in Prp 0) (mk_assert_out Prp 0)⸩)⸩)⸩

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
Pi : ((Prop → Prop) → (Prop → Prop)) : (Type 0)
-/
def pi.type : Expr :=
  let t_in := (mk_arrow Prp Prp 0 0)
  let t_out := (mk_arrow Prp (mk_arrow Prp Prp 0 0) 0 1)
  (mk_arrow t_in
    (mk_arrow t_out (Ty 0) 1 1) 1 1)

/-
id : ∀ (α : Type), α → α
-/
def id.type (m : Level) : Expr :=
  let α := mk_assert_in (Ty m) m.succ
  let x := snd

  let cpy := ⸨(both 0 0 0)
    Prp
    ⸨(const' 1 0) (Ty 0) Prp Prp⸩
    ⸨(const' 1 0) (mk_arrow Prp (Ty 0) 0 1) Prp
      ⸨(const' 1 0) (Ty 0) Prp
        (mk_arrow Prp (mk_arrow Prp Prp 0 0) 0 1)⸩⸩⸩
  let out := ⸨cpy (⊢ ∘ snd) ⸨(id 0) Prp⸩⸩

  ⸨Pi α (ret_pi ⸨Pi x out⸩)⸩

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
  | vdash   : DefEq judge_app ⸨(∶ m.succ) (Ty m) t_fx⸩
    → DefEq judge_f ⸨(∶ n) t_f f⸩
    → DefEq judge_x ⸨(∶ o) t_x x⸩
    → DefEq ⸨⊢ judge_app judge_f judge_x⸩ ⸨(∶ m) t_fx ⸨f x⸩⸩
  --| vdash   : DefEq ⸨(∶ m) t_x x⸩ ⸨(⊢ n) ⸨(∶ m) t_x x⸩ _a _b⸩
  /-| subst   : DefEq ($ (Pi α₁ β₁ map_arg₁), x) ($ (Pi α₂ β₂ map_arg₂), x)
    → DefEq (Pi α₁ β₁ map_arg₁) (Pi α₂ β₂ map_arg₂)-/

inductive ValidJudgment : Expr → Prop
  | const : ValidJudgment ⸨(∶ 1) (const.type m n) (const m n)⸩
  | id    : ValidJudgment ⸨(∶ 1) (id.type m) (id m)⸩
  | judge : ValidJudgment ⸨(∶ 1) (judge.type m) (∶ m)⸩
  | vdash : ValidJudgment ⸨(∶ 1) (vdash.type m) ⊢⸩
  | fst   : ValidJudgment ⸨(∶ 1) fst.type fst⸩ -- fst : Prop → Prop
  | snd   : ValidJudgment ⸨(∶ 1) snd.type snd⸩ -- snd : Prop → Prop
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
    → DefEq ⸨t_in ⸨(∶ 1) ⸨Pi t_in t_out⸩ f⸩⸩ ⸨(∶ n.succ) (Ty n) t_x⸩
    -- t_out decides what to to do with the context and make a new judgment
    → ValidJudgment ⸨t_out
                    ⸨(∶ 1) ⸨Pi t_in t_out⸩ f⸩
                    ⸨(∶ n) t_x x⸩⸩
  /-
    Partial application produces a conjoined context. ⊢ judge_f judge_x.
    This is our "context:" ⸨⊢ judge_f judge_inner_f judge_inner_x⸩
    This is the result of the partially applied app (a nested Pi):
      ⸨(∶ m) ⸨Pi t_in t_out⸩⸩
  -/
  | parapp : ValidJudgment ⸨⊢ ⸨(∶ 1) (Ty 0) ⸨Pi t_in t_out⸩⸩ judge_inner_f judge_inner_x⸩
    → ValidJudgment ⸨(∶ n) t_x x⸩
    → DefEq ⸨t_in ⸨⊢ ⸨(∶ 1) (Ty 0) ⸨Pi t_in t_out⸩⸩ judge_inner_f judge_inner_x⸩⸩ ⸨(∶ n.succ) (Ty n) t_x⸩
    → ValidJudgment ⸨t_out
      ⸨⊢ ⸨(∶ 1) (Ty 0) ⸨Pi t_in t_out⸩⸩ judge_inner_f judge_inner_x⸩
      ⸨(∶ n) t_x x⸩⸩
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

@[simp] theorem defeq_refl (e : Expr) : DefEq e e := DefEq.refl

@[simp] theorem step_const' : IsStep ⸨(const' m n) _α _β x y⸩ x := IsStep.const'

@[simp] theorem step_comp : IsStep ⸨(f ∘ g) x⸩ ⸨f ⸨g x⸩⸩ := IsStep.comp

@[simp] theorem step_both : IsStep ⸨(both m n o) _α _β _γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩ := IsStep.both

@[simp] theorem step_fst_j : IsStep ⸨fst ⸨(∶ m) t x⸩⸩ ⸨(∶ m.succ) (Ty m) t⸩ := IsStep.fst_j

@[simp] theorem step_fst : IsStep ⸨fst ⸨⊢ t_app judge_f judge_x⸩⸩ judge_f := IsStep.fst

@[simp] theorem step_snd : IsStep ⸨snd ⸨⊢ t_app judge_f judge_x⸩⸩ judge_x := IsStep.snd

@[simp] theorem step_left : IsStep f f' → IsStep ⸨f x⸩ ⸨f' x⸩ := IsStep.left

@[simp] theorem step_right : IsStep x x' → IsStep ⸨f x⸩ ⸨f x'⸩ := IsStep.right

@[simp] theorem ty_well_typed : ValidJudgment ⸨(∶ m.succ.succ) (Ty m.succ) (Ty m)⸩ := ValidJudgment.ty

theorem id_well_typed : ValidJudgment ⸨(∶ m.succ) (Ty m) α⸩
  → ValidJudgment ⸨(∶ m) α x⸩
  → ValidJudgment ⸨(∶ m) α ⸨(id m) α x⸩⸩ := by
  intro h_t_α h_t_x
  judge defeq, parapp, app, id
  exact m
  exact h_t_α
  defeq step
  step const'
  exact h_t_x
  defeq step
  step snd
  defeq trans, left, step
  step both
  defeq trans, left, left, step
  step comp
  defeq vdash, trans, step
  step snd
  defeq refl
  defeq trans, step
  step id
  defeq vdash
  repeat (defeq refl)

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
  defeq trans, step
  step snd
  defeq refl
  unfold mk_assert_out
  defeq vdash, refl, vdash
  repeat (defeq refl)

theorem const'_well_typed : ValidJudgment ⸨(∶ m.succ) (Ty m) α⸩
  → ValidJudgment ⸨(∶ n.succ) (Ty n) β⸩
  → ValidJudgment ⸨(∶ m) α x⸩
  → ValidJudgment ⸨(∶ n) β y⸩
  → ValidJudgment ⸨(∶ m) α ⸨(const' m n) α β x y⸩⸩ := by
    intro h_t_α h_t_β h_t_x h_t_y
    judge defeq, parapp, defeq, parapp, defeq, parapp, defeq, app, const'
    exact m
    exact n
    exact h_t_α
    defeq step
    step const'
    defeq refl
    exact h_t_β
    defeq step
    step const'
    defeq refl
    exact h_t_x
    defeq trans, step
    step comp
    defeq trans, right, step
    step fst
    defeq step
    step snd
    defeq refl
    exact h_t_y
    simp
    defeq trans, step
    step comp
    defeq trans, right, step
    step fst
    defeq step
    step snd
    defeq trans, left, step
    step both
    simp
    defeq trans, left, left, step
    step comp
    defeq trans, left, left, right, step
    step comp
    defeq trans, left, left, right, right, step
    step comp
    defeq trans, left, left, right, right, right, step
    step fst
    defeq trans, left, left, right, right, step
    step fst
    defeq trans, left, left, right, step
    step snd
    defeq vdash, refl, trans, step
    step id
    defeq vdash, refl, vdash, refl, vdash
    repeat (defeq refl)

/-
Dependent K is well-typed.

α : Type
β : α → Type
-/
theorem const_well_typed : ValidJudgment ⸨(∶ m.succ) (Ty m) α⸩
  → ValidJudgment ⸨(∶ 1) (mk_arrow α (Ty n) m n.succ) β⸩
  → ValidJudgment ⸨(∶ m) α x⸩
  → ValidJudgment ⸨(∶ n) ⸨β x⸩ y⸩
  → ValidJudgment ⸨(∶ m) α ⸨(const m n) α β x y⸩⸩ := by
  intro h_t_α h_t_β h_t_x h_t_y
  judge defeq, parapp, defeq, parapp, defeq, parapp, defeq, app, const
  exact m
  exact n
  exact h_t_α
  defeq step
  step const'
  defeq refl
  exact h_t_β
  unfold mk_arrow
  simp
  defeq trans, step
  step comp
  defeq trans, right, step
  step comp
  defeq right, trans, step
  step flip
  defeq left
  defeq trans, right, step
  step comp
  unfold mk_assert_in
  defeq trans, right, right, step
  step snd
  defeq refl
  defeq refl
  exact h_t_x
  defeq trans, step
  step comp
  defeq trans, right, step
  step fst
  defeq step
  step snd
  defeq left, refl
  exact h_t_y
  defeq trans, step
  step both
  defeq trans, left, step
  step comp
  defeq vdash, refl
  defeq trans, step
  step comp
  defeq trans, right, step
  step fst
  defeq step
  step snd
  defeq step
  step snd
  defeq trans, left, step
  step both
  defeq trans, left, left, step
  step comp
  defeq vdash, trans, step
  step comp
  defeq trans, right, step
  step comp
  defeq trans, right, right, step
  step fst
  defeq trans, right, step
  step fst
  defeq trans, step
  step snd
  defeq refl
  defeq trans, step
  step id
  defeq vdash, refl, vdash, refl
  defeq vdash, refl
  repeat defeq refl

