/-
Questions:

- can we avoid universe polymorphism for the base combinators?
  - offload to (∶ T x : Prop)?
  - offloading would be very very nice
- What is a proof of (∶ T x)?
  - x?
  - x is a proof of T
- (∶ T x) : Judgment
  - Judgment : Prop

K : ∀ (α : Judgment) (β : Judgment), α → β → α

This seems to imply that (K : (∶ Tk K)).

snd (∶ Tα α) = (∶ α),

so we can apply x, and receive a typing judgment.

(∶ α x), then we can compare against the judgment for x.

This also implies that (x : (∶ α x)).

Type universe hierarchy is just for type of type.

(∶ T x) : Prop. This is fine.

(∶ T x) ↔ (Id_{T}, x = x)

snd (∶ Tα α) = (∶ α),

apply x, get (∶ α x).

Then compare this against the judgment for x.

To make this, we still use ⊢. β x

⊢ π₁ π₂ hyp₁ hyp₂ = (∶ ((π₁ hyp₁ hyp₂) (π₂ hyp₁ hyp₂)))

Eval rules:
1. snd (∶ T x) = (∶ x)
2. fst (∶ T x) = (∶ TT T)
3. fst ((f : Pi t_in t_out) (x : α)) = (t_in x)
4. snd ((f : Pi t_in t_out) (x : α)) = (t_out (t_in x))
5. ⊢ π₁ π₂ hyp₁ hyp₂ = (∶ ((π₁ hyp₁ hyp₂) (π₂ hyp₁ hyp₂))
6. S x y z = (x z) (y z)
   ^ the typing judgments themselves induce evaluation. if they are not well-typed, no reduction.
7. K x y = x

Can we remove type arguments from K and K' altogether? Almost certainly.
1. K x y = x,

Can we internalize the typing judgment?

K : Prop → (Prop → Prop) → Prop

⊢ y β x = (∶ (β x) y)

Oh god that is beautiful.

(∶ T) ∘ K, we should be able to infer the judgment from this.

Inference rules:

1. (∶ T x) : Prop
2. ((f : Pi t_in t_out) x)

: (∶ TT t) x
^ cannot keep recursing forever, though.
need base case.

Prop and Type.

K : Pi id

In S, the judgment expression internalizes the condition for strong normalization.

This implies that x = ⊢.

⊢ should do application.

⊢ (∶

What is a proof of (∶ Tk K)?

There is no proof.

Feels like K' shouldn't exist.

K' is just an "interpretation" under (∶.).

Yes, this does mean there are mutliple ValidJudgment.

This means we don't have UIP.

Is ⊢ even necessary?

(∶ could do it with just a fancy reduction rule,
although ⊢ is nice.

S x y z = (x z) (y z), these are all Props, or maybe they are functions on Prop. ⊢.

Start with K first.

Check if ValidJudgment ⸨∶ α x⸩ x.

K doesn't have type arguments.

Its types just specify "capabilities."

K' : Pi (∶ Prp) (K (∶ ? (Pi (∶ Prp)

fst and snd may not be necessary YET.

Pi t_in t_out : Type
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
  | k      : IsStep ⸨K x y⸩ x
  | s      : IsStep ⸨S x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | fst    : IsStep ⸨fst ⸨∶ T x⸩⸩ t
  | snd    : IsStep ⸨snd ⸨∶ T x⸩⸩ ⸨∶ x⸩
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

K : (∶ Prop) → (∶ Prop) → (∶ α (K x y))
⸨∶ α ⸨K ⸨∶ α x⸩ ⸨∶ β y⸩⸩⸩

⊢ may not be necessary. we will see until S.

Note: we don't need to (∶ terms inline every time.
ValidJudgment can figure this out for us. These are kind of built-in axioms.

we want to make

(∶ α (K (∶ α x)))

we can simplify actually.

(∶ (cod x) (f x))

make

S (K (∶ α)) (S (K ((K (∶ α x))) I))

S (K (∶ α)) (S (K ((K (∶ α x))) I))

S (K (∶ α)) (S (K ((K (∶ α x))) I)) (∶ β y)
= (∶ α) (((K (∶ α x))) (∶ β y))

S (K (∶ α)) (S (K ((K (∶ α x))) I))

⸨S ⸨S ⸨K S⸩ (K ∘ snd)⸩ (S ∘ ⸨S (K ∘ K) ⸨K I⸩)⸩
-/
def K'.type : Expr :=
  ⸨Π' ⸨∶ Prp⸩
    (⸨Π' ⸨∶ Prp⸩⸩ ∘ ⸨S ⸨S ⸨K S⸩ (K ∘ snd)⸩ (K ∘ fst)⸩)⸩

/-
(: T x) : Prop

∶ : Pi (∶ Ty) (S (Pi ∘ (∶)) t_out)

t_out α = ((∶ Prp) ∘ (Pi α))

: Pi (∶ Ty) (S (Pi ∘ (∶)) (S (K (B (∶ Prp))) Pi))
-/
def judge.type : Expr :=
  ⸨Pi ⸨∶ Ty⸩ ⸨S (Pi ∘ (∶)) K⸩⸩

inductive ValidJudgment : Expr → Expr → Prop
  | app   : ValidJudgment ⸨∶ ⸨Pi dom cod⸩ f⸩ f
    → ValidJudgment ⸨dom x⸩ x
    → ValidJudgment ⸨∶ ⸨cod x⸩ ⸨f x⸩⸩ ⸨f x⸩
  | ty    : ValidJudgment ⸨∶ Ty Ty⸩ Ty
  | prp   : ValidJudgment ⸨∶ Ty Prp⸩ Prp
  | judge : ValidJudgment ⸨∶ judge.type ∶⸩ ∶
  | k'    : ValidJudgment ⸨∶ K'.type K⸩ K
  | defeq : ValidJudgment ⸨∶ t₁ x⸩ x
    → DefEq t₁ t₂
    → ValidJudgment ⸨∶ t₂ x⸩ x

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
  step k
  intro h
  defeq trans, step
  step k
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
  step left, left, left, k
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
  step k
  defeq trans, step
  step s
  defeq left, step
  step k

theorem K'.preservation : ValidJudgment ⸨∶ Ty α⸩ α
  → ValidJudgment ⸨∶ Ty β⸩ β
  → ValidJudgment ⸨∶ α x⸩ x
  → ValidJudgment ⸨∶ β y⸩ y
  → ValidJudgment ⸨∶ α ⸨K ⸨∶ α x⸩ ⸨∶ β y⸩⸩⸩ ⸨K ⸨∶ α x⸩ ⸨∶ β y⸩⸩ := by
  intro h_t_α h_t_β h_t_x h_t_y
  judge defeq, app, defeq, app, k', defeq, app, defeq, app, judge
  assumption
  simp
  defeq symm
  
  sorry
