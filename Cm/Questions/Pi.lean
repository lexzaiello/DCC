import Mathlib.Data.Nat.Notation

/-
  1. Can we do Π as a combinator, instead of an eta-expaned
  Pi : Expr → Expr → Expr?

  What would its type be?

  Pi : (α → Type) → (α → Type) → Type

  Pi : ($ Pi
       , nil (Pi (id Ty) (nil Ty))
       , Pi ($ nil, ($ Pi, id Ty, nil Ty)) ($ const', Ty, nil (Pi (id Ty) (nil Ty)), Ty))
-/

inductive Expr where
  | app    : Expr → Expr → Expr
  /- List-like objects
     They come with built-in projection.
     They are the mirror image of application "as data". -/
  | cons   : Expr → Expr → Expr
  /-
    ::[x, xs] lists are a special case. They are the mirror
    image of application as data. They internalize a projector
    argument π.
  -/
  | Prod   : Expr → Expr → Expr
  /-
    Our representation of curried function types.
    Π t_in t_out
  -/
  | Pi     : Expr
  | both   : Expr
  | const  : Expr
  | const' : Expr
  | id     : Expr
  -- downgrades a term to a type
  | nil    : Expr
  | ty     : Expr

syntax ident ".{" term,* "}"  : term
syntax "::[" term,+ "]"       : term
syntax "($" term,+ ")"        : term

macro_rules
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.cons $x ::[$xs,*])
  | `(($ $x:term) ) => `($x)
  | `(($ $f:term, $x:term )) => `(Expr.app $f $x)
  | `(($ $f, $x:term, $args:term,* )) =>
    `(($ (Expr.app $f $x), $args,*))

notation "Ty" => Expr.ty

open Expr

/-
Arrows:
This assumes only (x : α) is in scope.
-/
def mk_arrow (α β : Expr) : Expr :=
  ($ Pi, ($ nil, α), ($ const', Ty, α, β))

def pop_t_out : Expr → Expr
  | ($ Pi, _t_in, t_out) => t_out
  | e => e

/-
Pi : (α → Type) → (α → Type) → Type
-/
def Pi.type : Expr :=
  ($ Pi
   , ($ Pi, ($ id, Ty), ($ nil, Ty))
   , ($ Pi
     , ($ Pi, ($ id, Ty), ($ nil, Ty))
     , ($ nil, ($ nil, Ty))))

def id.type : Expr :=
  -- (α : Ty) ((x : α) → (_x α))
  ($ Pi, ($ nil, Ty), ($ Pi, nil, nil))

/-
nil : ∀ (α : Type), α → Type

($ nil, ($ nil, Ty)) α = (nil Ty)
(nil Ty) x = Ty
-/
def nil.type : Expr :=
  ($ Pi, ($ nil, Ty), ($ Pi, nil, ($ nil, ($ nil, Ty))))

/-
const' : ∀ (α : Type) (β : Type), α → β → α

-- with α, then β in scope
-- wrap (nil α) in a const
-- const ? ? (nil α)
let x_α := ::[nil, const Ty (Pi (nil Ty) nil)

const : Pi (nil Ty) (Pi (const' (mk_arrow Ty Ty) Ty (nil Ty)) (Pi (nil
-/

inductive IsStepStar {rel : Expr → Expr → Prop} : Expr → Expr → Prop
  | refl  : IsStepStar e e
  | trans : rel e₁ e₂
    → IsStepStar e₂ e₃
    → IsStepStar e₁ e₃

inductive IsBetaEq {s : Expr → Expr → Prop} : Expr → Expr → Prop where
  | rel   : s e₁ e₂ → IsBetaEq e₁ e₂
  | refl  : IsBetaEq e e
  | symm  : IsBetaEq e₁ e₂ → IsBetaEq e₂ e₁
  | trans : IsBetaEq e₁ e₂ → IsBetaEq e₂ e₃ → IsBetaEq e₁ e₃

inductive IsStep : Expr → Expr → Prop
  | sapp   : IsStep ($ ::[x, f], fn) ($ fn, f, x)
  | pi     : IsStep ($ Pi, Tin, Tout, Δ) ($ Pi, ($ Tin, Δ), ($ Tout, Δ))
  | nil    : IsStep ($ nil, α, x) α
  | id     : IsStep ($ Expr.id, _α, x) x
  | both   : IsStep ($ both, _α, _β, _γ, f, g, x)
    ::[($ f, x), ($ g, x)]
  | const' : IsStep ($ const', _α, _β, x, y) x
  | const  : IsStep ($ const, _α, _β, x, y) x
  | left   : IsStep f f'
    → IsStep ($ f, x) ($ f', x)
  | right  : IsStep x x'
    → IsStep ($ f, x) ($ f, x')

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | step    : IsStep e e' → DefEq e e'
  | symm    : DefEq e₁ e₂ → DefEq e₂ e₁
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ($ f, x) ($ f', x)
  | right   : DefEq x x'  → DefEq ($ f, x) ($ f, x')
  | lright  : DefEq f f'  → DefEq ::[x, f] ::[x, f']
  | lleft   : DefEq x x'  → DefEq ::[x, f] ::[x', f]
  | subst   : DefEq ($ Pi, α₁, β₁, x) ($ Pi, α₂, β₂, x)
    → DefEq ($ Pi, α₁, β₁) ($ Pi, α₂, β₂)

inductive IsStepN : ℕ → Expr → Expr → Prop
  | one  : IsStep e e' → IsStepN 1 e e'
  | succ : IsStep e e'' → IsStepN n e'' e'''
    → IsStepN n.succ e e'''

/-
::[a, b] : Prod a b
::[a, b] : {γ : β → α → Type} (π : ∀ (x : β) (y : α), γ x y)
-/

inductive ValidJudgment : Expr → Expr → Prop
  /- TODO: Remove this in the actual calculus
     use type universes
     this module is just for answering reseach questions -/
  | ty        : ValidJudgment Ty Ty
  | cons      : ValidJudgment x α
    → ValidJudgment xs β
    → ValidJudgment ::[x, xs] (Prod α β)
  | id        : ValidJudgment id id.type
  | nil       : ValidJudgment nil nil.type
  | Prod      : ValidJudgment (Prod α β) Ty
  | Pi        : ValidJudgment Pi Pi.type
  --| id        : ValidJudgment id Π[::[nil, id, id], Ty]
  /-
    To check an app:
    - functions have type Π Tin Tout
    - (Π Tin Tout) Δ = (Π (Tin Δ) (Tout Δ)). This mimicks substitution.
    - (Π (Tin arg) (Tout arg))
    - (((f : Π Tin Tout) (x : α)) : (Tout x))
    - To check that x matches the domain, (Tin x)
  -/
  | app       : ValidJudgment f ($ Pi, Tin, Tout)
    → ValidJudgment x ($ Tin, x)
    → ValidJudgment ($ f, x) ($ Tout, x)
  /-
   Apps with ::[x, xs] fn are a special case, since they
   do some type inference

   If γ is a Pi expression, we won't automatically get the output.
   γ is not a Pi expression, it is a function. So this is fine!
  -/
  | sapp      : ValidJudgment ::[a, b] (Prod α β)
    → ValidJudgment a α
    → ValidJudgment b β
    → ValidJudgment γ (mk_arrow β (mk_arrow α Ty))
    → ValidJudgment π ($ Pi, ($ nil, β), ($ Pi, ($ const', (mk_arrow α Ty), β, ($ nil, α)), γ))
    → ValidJudgment ($ ::[a, b], π) ($ γ, b, a)
  | def_eq    : ValidJudgment e α
    → DefEq α β
    → ValidJudgment e β

theorem id_well_typed : ValidJudgment α Ty → ValidJudgment x α → ValidJudgment ($ id, α, x) α := by
  intro h_t_α h_t_x
  apply ValidJudgment.def_eq
  apply ValidJudgment.app
  apply ValidJudgment.def_eq
  apply ValidJudgment.app
  apply ValidJudgment.id
  apply ValidJudgment.def_eq
  assumption
  apply DefEq.symm
  apply DefEq.step
  apply IsStep.nil
  apply DefEq.trans
  apply DefEq.step
  apply IsStep.pi
  apply DefEq.refl
  apply ValidJudgment.def_eq
  assumption
  apply DefEq.symm
  apply DefEq.step
  apply IsStep.nil
  apply DefEq.trans
  apply DefEq.step
  apply IsStep.nil
  apply DefEq.refl

/-
If x : xs, then
::[x, xs] id should always have type xs.
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

abbrev nil_ty_out {α : Expr} : Expr := ($ Pi, Ty, ($ Pi, ($ nil, α), ($ nil, Ty)))

theorem rw_nil_ty : DefEq ($ nil.type, α) (@nil_ty_out α) := by
  unfold nil.type
  defeq trans, step
  step pi
  defeq trans, left, right, step
  step nil
  defeq right, trans, step
  step pi
  defeq trans, right, step
  step nil
  defeq right, refl

abbrev nil_ty₁_out {α : Expr} := ($ Pi, α, Ty)

theorem rw_nil_ty_out : DefEq (pop_t_out (@nil_ty_out α)) ($ Pi, ($ nil, α), ($ nil, Ty)) := by
  simp [pop_t_out]
  defeq refl

theorem rw_nil_ty₁ {α x : Expr} : DefEq ($ (pop_t_out (@nil_ty_out α)), x) (@nil_ty₁_out α) := by
  simp [pop_t_out]
  defeq trans, step
  step pi
  defeq trans, right, step
  step nil
  defeq trans, left, right, step
  step nil
  defeq refl

-- Pi : (α → Type) → (α → Type) → Type
theorem Pi_well_typed_self : ValidJudgment t_in ($ Pi, ($ id, Ty), ($ nil, Ty))
  → ValidJudgment t_out ($ Pi, ($ id, Ty), ($ nil, Ty))
  → ValidJudgment ($ Pi, t_in, t_out) Ty := by
  intro h_t_t_in h_t_t_out
  judge def_eq, app, def_eq, app
  

theorem nil_well_typed : ValidJudgment α Ty
  → ValidJudgment x α
  → ValidJudgment ($ nil, α, x) Ty := by
  intro h_t_α h_t_x
  judge def_eq, app, def_eq, app, nil
  judge def_eq
  exact h_t_α
  defeq symm, trans, step
  step nil
  defeq refl, trans
  show DefEq (pop_t_out (@nil_ty_out α)) _
  apply rw_nil_ty_out
  simp [pop_t_out]
  defeq trans, step
  step pi
  defeq right
  defeq trans, step
  step nil
  defeq refl
  judge def_eq
  exact h_t_x
  defeq symm, trans, step
  step nil
  defeq refl
  defeq trans, step
  step nil
  defeq refl

theorem project_self : ValidJudgment xs Ty → ValidJudgment x xs
  → ValidJudgment γ (mk_arrow Ty (mk_arrow xs Ty))
  → ValidJudgment π ($ Pi, ($ nil, Ty), ($ Pi, ($ const', (mk_arrow xs Ty), Ty, ($ nil, xs)), γ))
  → DefEq ($ γ, xs, x) xs
  → ValidJudgment ($ ::[x, xs], id) xs := by
  intro h_t_xs h_t_x h_t_γ h_t_π h_eq_γ
  judge def_eq, sapp, cons
  repeat assumption
  judge def_eq, id
  defeq symm, subst
  defeq trans, step
  step pi
  defeq trans, left, right, step
  step nil
  defeq trans, right, step
  step pi
  defeq trans, right, left, right, step
  step const'
  defeq symm, trans, step
  step pi
  defeq trans, right, step
  step pi
  defeq trans, left, right, step
  step nil
  defeq right, subst, symm, trans, step
  step pi
  defeq trans, right
  exact h_eq_γ
  defeq trans, left, right, step
  step nil
  defeq symm, trans, step
  step pi
  defeq trans, left, right, step
  step nil
  defeq trans, right, step
  step nil
  defeq refl
  exact h_eq_γ

theorem project_well_typed : ValidJudgment xs β → ValidJudgment x α
  → ValidJudgment γ (mk_arrow β (mk_arrow α Ty))
  → ValidJudgment α Ty
  → ValidJudgment β Ty
  → ValidJudgment δ Ty
  → ValidJudgment π ($ Pi, ($ nil, β), ($ Pi, ($ const', (mk_arrow α Ty), β, ($ nil, α)), γ))
  → DefEq ($ γ, xs, x) δ
  → ValidJudgment ($ ::[x, xs], π) δ := by
  intro h_t_xs h_t_x h_t_γ h_t_α h_t_β h_t_π h_eq_γ
  judge def_eq, sapp, cons
  repeat assumption

