/-
We might want to just keep current K and add other K.
Type becomes annoying, though.

K : Pi (∶ Ty Prp) (Pi (Pi I)

- snd should upgrade.
Then we don't need K'.

- fst should actually upgrade. we seem to need it in quite a few places.
but also we need it to access pi members.

TODO: will need type universes. She mad.
-/

inductive Expr where
  | Pi    : Expr
  | S     : Expr
  | K     : Expr
  | K'    : Expr
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
  | s      : IsStep ⸨S ⸨∶ Tf f⸩ g x⸩ ⸨f x ⸨g x⸩⸩
  | i      : IsStep ⸨I x⸩ x
  | fst    : IsStep ⸨fst π ⸨∶ α x⸩⸩ ⸨π α⸩
  | snd    : IsStep ⸨snd π ⸨∶ α x⸩⸩ ⸨π x⸩
  | fstπ   : IsStep ⸨fst π ⸨Π' dom cod⸩⸩ ⸨π dom⸩
  | sndπ   : IsStep ⸨snd π ⸨Π' dom cod⸩⸩ ⸨π cod⸩
  | pi     : IsStep ⸨⸨Π' dom cod⸩ x⸩ ⸨Π' ⸨dom x⸩ ⸨cod x⸩⸩
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
def K.type : Expr :=
  ⸨Π' ⸨∶ Ty Prp⸩ ⸨Π' ⸨K ⸨∶ Ty Prp⸩⸩ ⸨fst K⸩⸩⸩

/-
I type:
  I : Prop → Prop
-/
def I.type : Expr :=
  ⸨Π' ⸨∶ Ty Prp⸩ ⸨K ⸨∶ Ty Prp⸩⸩⸩

/-
Π : Prop → Ty → Ty
-/
def Pi.type : Expr :=
  ⸨Π' ⸨∶ Ty Prp⸩ ⸨Π' ⸨K ⸨∶ Ty Ty⸩⸩ ⸨fst K⸩⸩⸩

/-
S type:
  S : (f : Prp) → (g : (fst x : Prp)) → (x : ((K ∘ fst ∘ fst) f : Prp)) → (((S ∘ snd) x) x (g x) : Prp)
  fst x is a Pi type, Pi dom cod. fst fst x is α in (x : α)
  (S (∶ (Π' Prp (K ( Ty Ty)) ((fst Π') (snd (fst I))) t_f
  S (∶ (Pi α cod) f) (∶ (Pi α cod) g) (∶ α x) = (∶
    (cod (∶ α x) (g (∶ α x)))
    (f (∶ α x) (g (∶ α x))))
-/
def S.type : Expr :=
  ⸨Π' ⸨∶ Ty Prp⸩ ⸨Π'
    ⸨fst ⸨S ⸨∶ Ty ⸨K ⸨∶ Ty⸩⸩⸩ ⸨S ⸨∶ Ty ⸨fst Π'⸩⸩ ⸨snd ⸨fst I⸩⸩⸩⸩⸩ -- Form Π α β
    ⸨Π'
      ⸨fst ⸨fst K⸩⸩ -- select α from Π α (Π β γ), prepend K.
      ⸨snd ⸨snd S⸩⸩⸩⸩⸩ -- select γ from Π α (Π β γ), prepend S

inductive ValidJudgment : Expr → Expr → Prop
  | app   : ValidJudgment ⸨∶ ⸨Π' ⸨∶ Tα α⸩ cod⸩ f⸩ f
    → ValidJudgment ⸨∶ α x⸩ x
    → ValidJudgment ⸨∶ ⸨cod x⸩ ⸨f x⸩⸩ ⸨f x⸩
  | ty    : ValidJudgment ⸨∶ Ty Ty⸩ Ty
  | prp   : ValidJudgment ⸨∶ Ty Prp⸩ Prp
  | k     : ValidJudgment ⸨∶ K.type K⸩ K
  | s     : ValidJudgment ⸨∶ S.type S⸩ S
  | defeq : ValidJudgment t₁ x → DefEq t₁ t₂ → ValidJudgment t₂ x

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

@[simp] theorem S.step :  DefEq ⸨S ⸨∶ Tf f⸩ g x⸩ s' = DefEq s' ⸨f x ⸨g x⸩⸩ := by
  ext
  constructor
  intro h
  defeq symm, trans, symm, step
  step s
  exact Tf
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

theorem K.preservation : ValidJudgment ⸨∶ Prp ⸨∶ α x⸩⸩ ⸨∶ α x⸩
  → ValidJudgment ⸨∶ Prp ⸨∶ β y⸩⸩ ⸨∶ β y⸩
  → ValidJudgment ⸨∶ α ⸨K ⸨∶ α x⸩ ⸨∶ β y⸩⸩⸩ ⸨K ⸨∶ α x⸩ ⸨∶ β y⸩⸩ := by
  intro h_t_α h_t_β
  judge defeq, app, defeq, app, k
  assumption
  defeq left, right, trans, step
  step pi
  defeq trans, right, step
  step fst
  defeq trans, left, right, step
  step k
  defeq refl
  assumption
  defeq left, right, step
  step k

/-
As usual:
S : ∀ (f : ∀ (x : α) (y : β x), γ x y) (g : ∀ (x : α), β x) (z : α), γ z (y z)
-/
theorem S.preservation : ValidJudgment ⸨∶ Prp ⸨∶ ⸨Π' ⸨∶ Ty α⸩ ⸨Π' β γ⸩⸩ f⸩⸩ ⸨∶ ⸨Π' ⸨∶ Ty α⸩ ⸨Π' β γ⸩⸩ f⸩
  → ValidJudgment ⸨∶ ⸨Π' ⸨∶ Ty α⸩ cod⸩ g⸩ g
  → ValidJudgment ⸨∶ α x⸩ x
  → ValidJudgment ⸨∶ ⸨γ x ⸨y x⸩⸩ ⸨S ⸨∶ ⸨Π' ⸨∶ Ty α⸩ ⸨Π' β γ⸩⸩ f⸩ g x⸩⸩ ⸨S ⸨∶ ⸨Π' ⸨∶ Ty α⸩ ⸨Π' β γ⸩⸩ f⸩ g x⸩ := by
  intro h_t_f h_t_g h_t_x
  judge defeq, app, defeq, app, defeq, app, s
  assumption
  defeq trans, left, right, step
  step pi
  defeq trans, left, right, right, step
  step pi
  defeq trans, left, right, left, right, step
  step fst
  defeq left, right, left, right, step
  step fstπ
  
  sorry
