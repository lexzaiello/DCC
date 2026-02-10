/-

-/

inductive Expr where
  | Pi    : Expr
  | S     : Expr
  | K     : Expr
  | judge : Expr
  | type  : Expr
  | prop  : Expr
  | vdash : Expr
  | fst   : Expr
  | snd   : Expr
  | app   : Expr → Expr → Expr

open Expr

syntax "⸨" term+ "⸩"       : term

notation "Π'" => Expr.Pi
notation "Ty" => Expr.type
notation "Prp" => Expr.prop
notation "∶" => Expr.judge
notation "⊢" => Expr.vdash

macro_rules
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f $x)
  | `(⸨ $f $x:term $args:term*⸩) => `(⸨ (Expr.app $f $x) $args*⸩)

inductive IsStep : Expr → Expr → Prop
  | k      : IsStep ⸨K α β x y⸩ x
  | k'     : IsStep ⸨K x y⸩ x
  | s      : IsStep ⸨S x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | fst    : IsStep ⸨fst ⸨∶ T x⸩⸩ T
  | snd    : IsStep ⸨snd ⸨∶ T x⸩⸩ x
  | left   : IsStep f f' → IsStep ⸨f x⸩ ⸨f' x⸩
  | right  : IsStep x x' → IsStep ⸨f x⸩ ⸨f x'⸩

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | symm    : DefEq e e'
    → DefEq e' e
  | step    : IsStep e e' → DefEq e e'
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ⸨f x⸩ ⸨f' x⸩
  | right   : DefEq x x'  → DefEq ⸨f x⸩ ⸨f x'⸩

abbrev B := ⸨S ⸨K S⸩ K⸩
abbrev C := ⸨S ⸨S ⸨K ⸨S ⸨K S⸩ K⸩⸩ S⸩ ⸨K K⸩⸩
abbrev I := ⸨S K K⸩

infixr:90 " ∘ " => (fun f g => ⸨B f g⸩)

/-
Nondependent interpretation of K.

This is fine, since in dependent K:
K : ∀ (α : Type) (β : α → Type) (x : α) (y : β x), α,

The type of y is not determined by anything. Its type is not under a ∀ binder.
It should be inferrable given it is an argument of type Prop.

K : (∶ Prop) → (∶ Prop) → (∶ α (K x y))
⸨∶ α ⸨K ⸨∶ α x⸩ ⸨∶ β y⸩⸩⸩
-/
def K.type : Expr :=
  ⸨Π' ⸨∶ Prp⸩ (⸨Π' ⸨∶ Prp⸩⸩ ∘ (K ∘ fst))⸩

/-
x : ∀ (x : α) (y : β x), γ x y
x ≅ Pi α (S nu
S : (x = (∶ Prop)) → (∶ 
-/
def S.type : Expr :=
  sorry

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
    → ValidJudgment ⸨dom x⸩ x
    → ValidJudgment ⸨∶ ⸨cod x⸩ ⸨f x⸩⸩ ⸨f x⸩
  | ty    : ValidJudgment ⸨∶ Ty Ty⸩ Ty
  | prp   : ValidJudgment ⸨∶ Ty Prp⸩ Prp
  | judge : ValidJudgment ⸨∶ judge.type ∶⸩ ∶
  | k'    : ValidJudgment ⸨∶ K.type K⸩ K
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

@[simp] theorem S.step : DefEq ⸨S x y z⸩ s' ↔ DefEq s' ⸨⸨x z⸩ ⸨y z⸩⸩ := by
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

@[simp] theorem K.step : DefEq ⸨K x y⸩ k' ↔ DefEq k' x := by
  constructor
  intro h
  defeq trans, symm
  exact h
  defeq step
  step k'
  intro h
  defeq trans, step
  step k'
  defeq symm
  exact h

@[simp] theorem B.step : DefEq ⸨B f g x⸩ b' ↔ DefEq b' ⸨f ⸨g x⸩⸩ := by
  constructor
  intro h
  defeq trans, symm
  exact h
  defeq trans, step
  unfold B
  step left, left
  step s
  defeq trans, step
  step left, left, left, k'
  simp
  defeq symm, left
  simp
  defeq refl
  intro h
  defeq symm, trans
  exact h
  defeq symm, trans, step
  step left, left, s
  defeq trans, left, left, left, step
  step k'
  defeq trans, step
  step s
  defeq left, step
  step k'

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
  defeq refl
  defeq refl
  defeq refl
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
  defeq refl
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
  defeq refl
  defeq refl
  defeq refl
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
  defeq refl
  defeq refl

theorem defeq.refl : DefEq x x := DefEq.refl

theorem defeq.symm : DefEq x y ↔ DefEq y x := ⟨DefEq.symm, DefEq.symm⟩

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
