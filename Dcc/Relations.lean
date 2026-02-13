/-
Application is, in some sense, interpretation of our combinators.

K does not supply new proof information, so application is not required.
β x.

TODO:
- correct ValidJudgment proofs using new inference rules
- fix simp lemmas so as to be cleaner
- S type
 -  S induces application, so we will need to decide how that works
- What is a proof of ∶ T x?
  - The ValidJudgment constructor
  - We should be able to refer to these by names, though
  - This suggests we should be able to improve the judgment rule for app

(∶ interpretation term), term is the proof.

⊢ reduced interpretation₁ interpretation₂

⊢ goal fn x

- our current calculus reduction rules are quite unrestricted.
we want the typing judgments to be essentially elided after one layer
so that we can use normal SK.

Note:
⊢ goal f x should somehow carry its components down

⊢ goal f x can be replaced with just

(∶ (Pi

⊢ gets encoded in the rule for S itself.

S should encode its requirements in its reduction rule.

K should stya the same. It doesn't care.

⊢ (∶ Ttf Tf) (∶ Ttx Tx) (f : Tf) (x : Tx)

Ideas:
- only encode typing judgments at the highest level of application
- reduction rules carry these down
- this happens inside the rule for S
- also happens in the judgment rule for app
- we should assume in app rule that Pi has already been substituted.
- it would be cool to be able to explicit supply proofs of ∶ T x
  - although these should be inferrable by the type-checker

ValidJudgment f ⸨Pi cod dom⸩
ValidJudgment x cod
ValidJudgment ⸨f x⸩ ⸨∶ ⸨dom x⸩ ⸨f x⸩⸩ ⸨f x⸩

S (∶ Pi Tx cod) (∶ (Pi Tx cod)) (∶ Tx x)

Then, S.type becomes

Prop → Prop → Prop → Prop

⊢ becomes unnecessary. we can also encode the dependency in K's reduction rule, I think,
although this is also unnecessary.

We also ought to improve substitution for Pi

so that we don't need to invoke S in the type for K.

K : Prop → Prop → Prop.

fst / snd have no use now.

fst / snd are just Prop → Prop → Prop, respectively.

snd : (Prop → Prop) → Prop → Prop
fst : Prop → Prop

Then, Pi becomes substitution as we always thought.

Composition is pretty natural on snd / fst now.

Composition is not necessary, since π is an argument to snd.

K : Pi (: Ty Prop) (Pi (snd fst) K)

This suggests that fst and snd should work on types.

- we should have some clever reduction rule for judgments.
- we substitute just x in. term, not its type.

this removes need for fst / snd.

Pi substitution rule should not substitute dom.

we should make this on-demand with S.

position of judgments feels like it changes form in to out,
but this is fine, since it mirrors the substitution rule.

S isn't guaranteed to produce a not-stuck expression
even if we type-check it.

we need to make sure that f and g line up better.

S as out type still makes sense, but g and x
should be term arguments, not prop.

This suggests, again, that the sustitution rule should be upgraded.

fst and snd should be operations on judgments

if we can get fst on Pi, that would be nice, too.

It would be really nice for Pi to take Prop arguments.
we can do that.

fst (∶ α x) = (∶ Ty α)

fst should also work on Pi, probably.
-/

inductive Expr where
  | Pi    : Expr
  | S     : Expr
  | K     : Expr
  | I     : Expr
  | judge : Expr
  | type  : Expr
  | prop  : Expr
  | fst   : Expr
  | snd   : Expr
  | app   : Expr → Expr → Expr

open Expr

syntax "⸨" term+ "⸩"       : term

notation "Π'" => Expr.Pi
notation "Ty" => Expr.type
notation "Prp" => Expr.prop
notation "∶" => Expr.judge

macro_rules
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f $x)
  | `(⸨ $f $x:term $args:term*⸩) => `(⸨ (Expr.app $f $x) $args*⸩)

inductive IsStep : Expr → Expr → Prop
  | k      : IsStep ⸨K x y⸩ x
  | s      : IsStep ⸨S ⸨∶ ⸨Pi α cod⸩ f⸩ ⸨∶ ⸨Pi α cod⸩ g⸩ ⸨∶ α x⸩⸩
    ⸨∶
      ⸨cod ⸨∶ α x⸩ ⸨g ⸨∶ α x⸩⸩⸩
      ⸨f ⸨∶ α x⸩ ⸨g ⸨∶ α x⸩⸩⸩
    ⸩
  | i      : IsStep ⸨I x⸩ x
  | fst    : IsStep ⸨fst π ⸨∶ α x⸩⸩ ⸨π ⸨∶ Ty α⸩⸩
  | snd    : IsStep ⸨snd π ⸨∶ α x⸩⸩ ⸨π x⸩
  | fstπ   : IsStep ⸨fst π ⸨Π' dom cod⸩⸩ ⸨π dom⸩
  | sndπ   : IsStep ⸨snd π ⸨Π' dom cod⸩⸩ ⸨π cod⸩
  | pi     : IsStep ⸨⸨Pi dom cod⸩ x⸩ ⸨Pi ⸨dom x⸩ ⸨cod x⸩⸩
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
K type:
  K : Prop → Prop → Prop
  K x y = x
-/
def K'.type : Expr :=
  ⸨Π' ⸨∶ Ty Prp⸩ ⸨Π' ⸨K ⸨∶ Ty Prp⸩⸩ K⸩⸩

/-
S type:
  S : (x : Prop) → (fst x : Prp) → Prop → Prop
  fst x is a Pi type, Pi dom cod. fst fst x is α in (x : α)
  S (∶ (Pi α cod) f) (∶ (Pi α cod) g) (∶ α x) = (∶
    (cod (∶ α x) (g (∶ α x)))
    (f (∶ α x) (g (∶ α x))))
-/
def S.type : Expr :=
  ⸨Π' ⸨∶ Ty Prp⸩ ⸨Π' ⸨fst I⸩ ⸨Π' ⸨fst ⸨fst K⸩⸩ S⸩⸩⸩

/-
(: T x) : Prop

∶ : Pi (∶ Ty) (S (Pi ∘ (∶)) t_out)

t_out α = ((∶ Prp) ∘ (Pi α))

: Pi (∶ Ty) (S (Pi ∘ (∶)) (S (K (B (∶ Prp))) Pi))
-/
def judge.type : Expr :=
  ⸨Π' ⸨∶ Ty⸩ ⸨S (Π' ∘ (∶)) ⸨K ⸨K Prp⸩⸩⸩⸩

inductive ValidJudgment : Expr → Expr → Prop
  | app   : ValidJudgment ⸨∶ ⸨Π' dom cod⸩ f⸩ f
    → ValidJudgment ⸨∶ dom x⸩ x
    → ValidJudgment ⸨∶ ⸨cod x⸩ ⸨f x⸩⸩ ⸨f x⸩
  | ty    : ValidJudgment ⸨∶ Ty Ty⸩ Ty
  | prp   : ValidJudgment ⸨∶ Ty Prp⸩ Prp
  | judge : ValidJudgment ⸨∶ judge.type ∶⸩ ∶
  | k'    : ValidJudgment ⸨∶ K'.type K⸩ K
  | defeq : ValidJudgment t₁ x
    → DefEq t₁ t₂
    → ValidJudgment t₂ x

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

@[simp] theorem defeq.refl : DefEq x x := DefEq.refl

@[simp] theorem defeq.trans : DefEq a b → DefEq b c → DefEq a c := DefEq.trans

@[simp] theorem S.step :  DefEq ⸨S x y z⸩ s' = DefEq s' ⸨⸨x z⸩ ⸨y z⸩⸩ := by
  ext
  constructor
  intro h
  defeq symm, trans, symm, step
  step s
  exact h
  intro h
  defeq trans, step
  step s
  defeq symm
  assumption

@[simp] theorem K.step : DefEq ⸨K x y⸩ k' = DefEq k' x := by
  ext
  constructor
  intro h
  defeq trans, symm
  exact h
  defeq step
  step k
  intro h
  defeq trans, step
  step k
  defeq symm
  exact h

@[simp] theorem B.step : DefEq ⸨B f g x⸩ b' = DefEq b' ⸨f ⸨g x⸩⸩ := by
  ext
  constructor
  intro h
  defeq trans, symm
  exact h
  defeq trans, step
  unfold B
  step left, left
  step s
  defeq trans, step
  step left, left, left, k
  simp
  defeq symm, left
  simp
  intro h
  defeq symm, trans
  exact h
  defeq symm, trans, step
  step left, left, s
  defeq trans, left, left, left, step
  step k
  defeq trans, step
  step s
  defeq left, step
  step k

@[simp] theorem C.step : DefEq ⸨C x y z⸩ c' ↔ DefEq c' ⸨x z y⸩ := by
  constructor
  intro h
  defeq trans, symm
  exact h
  defeq trans, left, left
  simp
  defeq symm, trans, left
  simp
  defeq symm, trans, left
  simp
  defeq refl
  simp
  defeq symm, trans, left
  simp
  defeq refl, refl, refl
  defeq trans, left
  simp
  defeq symm, trans, left
  simp
  defeq refl, refl
  simp
  defeq right, symm, trans, left, left
  simp
  defeq refl
  simp
  intro h
  defeq symm, trans
  exact h
  defeq symm, trans, left, left
  simp
  defeq symm, trans, left
  simp
  defeq symm, trans, left
  simp
  defeq refl
  simp
  defeq symm, trans, left
  simp
  defeq refl, refl, refl
  defeq trans, left
  simp
  defeq symm, trans, left
  simp
  defeq refl
  defeq trans, right, left
  simp
  defeq refl, refl
  simp
  defeq symm, trans, right
  simp
  defeq refl, refl

theorem K.preservation : ValidJudgment ⸨∶ Ty α⸩ α
  → ValidJudgment ⸨∶ Ty β⸩ β
  → ValidJudgment ⸨∶ α x⸩ x
  → ValidJudgment ⸨∶ β y⸩ y
  → ValidJudgment ⸨∶ α ⸨K ⸨∶ α x⸩ ⸨∶ β y⸩⸩⸩ ⸨K ⸨∶ α x⸩ ⸨∶ β y⸩⸩ := by
  intro h_t_α h_t_β h_t_x h_t_y
  judge defeq, app, defeq, app, k', defeq, app, defeq, app, judge
  assumption
  simp
  defeq trans, left, right
  simp
  defeq symm, trans, left
  simp
  defeq refl
  defeq refl
  defeq refl
  assumption
  defeq trans, left, right, left
  simp
  defeq refl
  defeq trans, left, right
  simp
  defeq refl
  defeq refl
  simp
  defeq trans, left, right
  simp
  defeq symm, trans, right
  simp
  defeq refl, refl, refl
  judge defeq, app, defeq, app, judge
  assumption
  simp
  defeq trans, left, right
  simp
  defeq symm, trans, left
  simp
  defeq refl
  defeq trans, right
  simp
  defeq refl
  defeq refl
  defeq refl
  assumption
  defeq trans, left, right
  simp
  defeq refl
  defeq refl
  defeq trans, right
  simp
  defeq refl
  defeq trans, left, right
  simp
  defeq symm, step
  step fst
  defeq symm, trans, right
  simp
  defeq refl
  defeq refl
