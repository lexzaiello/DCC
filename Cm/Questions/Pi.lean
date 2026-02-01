import Mathlib.Data.Nat.Notation

/-
  1. Can we do Π as a combinator, instead of an eta-expaned
  Pi : Expr → Expr → Expr?

  What would its type be?

  Pi : (α → Type) → (α → Type) → Type

  Pi : ($ Pi
       , nil (Pi (id Ty) (nil Ty))
       , Pi ($ nil, ($ Pi, id Ty, nil Ty)) ($ const', Ty, nil (Pi (id Ty) (nil Ty)), Ty))

  2. Can we extend Pi substitution to lists? Some kind of cons combinator.
    cons a b = ::[b, a]

    Or more like (cons a b) x = ::[($ a, x), ($ b, x)] this is exactly what both
    does.

    Both lets us do list substitution.

  3. We still need some form of composition to fully bridge between lists and
    curried apps. (B f g x) = f (g x)
    we assume (g x) produces some kind of list expression
    (g x) f is what we want, really.

    - We will probably also need "flip" / C combinator.

  4. Is it possible to change the Π substitution rule such that we can form
    Pi types at runtime easier?

    What we could do instead of applying always, and this would make the type
    for Pi more consistent, is mirror how valid_judgment does it.

    (Pi t_in t_out) a = (Pi (t_in a) (t_out a))
    (Pi t_in t_out) a b = (Pi t_in t_out) ::[b, a]

    This is very interesting.

    But, we want these two branches to be exclusive.
    How do we force substitution?

    We could mimick this without a new eval rule with:

    (Pi t_in t_out) ∘ (cons a)
    (Pi t_in t_out) ∘ (cons a) b = (Pi t_in t_out)

    But then we need a new cons operator.

    Another potential idea:
    No substitution happens in Step.

    Can we offload advancing the machine to ValidJudgment?

    (Pi t_in t_out) a b = (Pi t_in t_out) ::[b, a]

    We will answer these questions in Pi2.lean
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
  | Pi     : Expr → Expr → Expr
  /-
    The core SK combinators. Both is kind of a "downgraded" version
    of S meant to work with ::[a, b] lists.
    (both _ _ _ y x z) (id _) = (x z) (y z)
    (both (id _) (const _ _ (both _ _ _ y x))) z
    = ::[z, (both _ _ _ y x)]

    (comp (id _) (both (id _) (const _ _ (both _ _ _ y x)))) z
    = ((both (id _) (const _ _ (both _ _ _ y x))) z) (id _)
    = ::[z, (both _ _ _ y x)] (id _)
    = (both _ _ _ y x) z
    (comp (id _) (comp (id _) (both (id _) (const _ _ (both _ _ _ y x))))) z
    = ((both _ _ _ y x) z) id
    = ::[(y z), (x z)] id
    = (x z) (y z)

    comp (α β γ : Ty) (δ : γ → β → Ty) (f : δ) (g : α → Prod β γ) (x : α)
  -/
  | flip   : Expr
  | comp   : Expr
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
  (Pi ($ nil, α) ($ const', Ty, α, β))

def pop_t_out : Expr → Expr
  | (Pi _t_in t_out) => t_out
  | e => e

/-
Pi : (α → Type) → (α → Type) → Type
-/
def Pi.type : Expr :=
  Ty

def id.type : Expr :=
  -- (α : Ty) ((x : α) → (_x α))
  (Pi ($ nil, Ty) (Pi nil nil))

/-
/-
comp (α β γ : Ty) (δ : γ → β → Ty) (f : ∀ (xs : γ) (x : β), δ) (g : α → Prod β γ) (x : α)

comp _ _ _ _ f g x = ($ ($ g, x), f)

α has just α in scope
β has α and β in scope
-/
def comp.type : Expr :=
  let α := ($ nil, Ty)
  let β := ($ const' (mk_arrow Ty Ty) Ty α)
  let γ := ($ const' (mk_arrow Ty (mk_arrow Ty Ty)) Ty β)

  /-
    δ rejects α, then makes γ → β → Ty,
    which is kind of tricky, since it
    flips the arguemnts.
    Can we substitute into Pi with a list?
    We are allowed to use comp in our own type

    Once we have flip, we can do (const _ _ (flip _ _ _ (Pi (

    Can we derive this comp from other comp?

    Normal comp: (B f g x) = f (g x)

    Another note: this is essentially flipped order of the list comp.

    We might need a flip, corresponding to C.

    C x y z = x z y
    C 
    flip 

    Pi ? ? ::[
  -/

  (Pi α (Pi β (Pi γ (Pi 
  sorry-/

/-
nil : ∀ (α : Type), α → Type

($ nil, ($ nil, Ty)) α = (nil Ty)
(nil Ty) x = Ty
-/
def nil.type : Expr :=
  (Pi ($ nil, Ty) (Pi nil ($ nil, ($ nil, Ty))))

/-
Can we do composition with ::[a, b]?

::[nil, (id Ty)] α =

const' Ty Ty (nil α) β = α

const : ∀ (α : Type) (β : α → Type), α → β → α
(Pi (nil Ty) (Pi (Pi (id Ty)
-/

/-
const' : ∀ (α : Type) (β : Type), α → β → α

(flip (const' Ty)) α β = (const' Ty β α)

(const' ? ? (nil α)) β
= nil α

Composition operator would be REALLY nice.
Or, we could change both

We don't have to change both

((id _) ∘' (both _ _ _ y x)) z = (x z) (y z)

Assume ∘' is list-native.

It would ALSO be really nice if we could build up an n-length context ::[arg₁, arg₂]

(t_in ∘ (:: arg₁)) arg₂ = t_in ::[arg₁, arg₂]

Feels like composition would be really nice.
This may allow us to do substitution in lists.

(const' ? ? (nil α))
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
  | comp   : IsStep ($ comp, α, β, γ, δ, f, g, x) ($ ($g, x), f)
  | sapp   : IsStep ($ ::[x, f], fn) ($ fn, f, x)
  | pi     : IsStep ($ (Pi Tin Tout), Δ) (Pi ($ Tin, Δ) ($ Tout, Δ))
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
  | pright  : DefEq o o'  → DefEq (Pi i o) (Pi i o')
  | pleft   : DefEq i i'  → DefEq (Pi i o) (Pi i' o)
  | subst   : DefEq ($ (Pi α₁ β₁), x) ($ (Pi α₂ β₂), x)
    → DefEq (Pi α₁ β₁) (Pi α₂ β₂)

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
  | Pi        : ValidJudgment t_in (mk_arrow α Ty)
    → ValidJudgment t_out (mk_arrow α Ty)
    → ValidJudgment (Pi t_in t_out) Pi.type
  --| id        : ValidJudgment id Π[::[nil, id, id], Ty]
  /-
    To check an app:
    - functions have type Π Tin Tout
    - (Π Tin Tout) Δ = (Π (Tin Δ) (Tout Δ)). This mimicks substitution.
    - (Π (Tin arg) (Tout arg))
    - (((f : Π Tin Tout) (x : α)) : (Tout x))
    - To check that x matches the domain, (Tin x)
  -/
  | app       : ValidJudgment f (Pi Tin Tout)
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
    → ValidJudgment π (Pi ($ nil, β) (Pi ($ const', (mk_arrow α Ty), β, ($ nil, α)) γ))
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

abbrev nil_ty_out {α : Expr} : Expr := (Pi Ty (Pi ($ nil, α) ($ nil, Ty)))

theorem rw_nil_ty : DefEq ($ nil.type, α) (@nil_ty_out α) := by
  unfold nil.type
  defeq trans, step
  step pi
  defeq trans, pleft, step
  step nil
  defeq pright, trans, step
  step pi
  defeq trans, pright, step
  step nil
  defeq pright, refl

abbrev nil_ty₁_out {α : Expr} := (Pi α Ty)

theorem rw_nil_ty_out : DefEq (pop_t_out (@nil_ty_out α)) (Pi ($ nil, α) ($ nil, Ty)) := by
  simp [pop_t_out]
  defeq refl

theorem rw_nil_ty₁ {α x : Expr} : DefEq ($ (pop_t_out (@nil_ty_out α)), x) (@nil_ty₁_out α) := by
  simp [pop_t_out]
  defeq trans, step
  step pi
  defeq trans, pright, step
  step nil
  defeq trans, pleft, step
  step nil
  defeq refl

-- Pi : (α → Type) → (α → Type) → Type
theorem Pi_well_typed_self : ValidJudgment α Ty
  → ValidJudgment t_in (mk_arrow α Ty)
  → ValidJudgment t_out (mk_arrow α Ty)
  → ValidJudgment (Pi t_in t_out) Ty := by
  intro h_t_α h_t_in h_t_out
  judge Pi
  repeat assumption

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
  defeq pright
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
  → ValidJudgment π (Pi ($ nil, Ty) (Pi ($ const', (mk_arrow xs Ty), Ty, ($ nil, xs)) γ))
  → DefEq ($ γ, xs, x) xs
  → ValidJudgment ($ ::[x, xs], id) xs := by
  intro h_t_xs h_t_x h_t_γ h_t_π h_eq_γ
  judge def_eq, sapp, cons
  repeat assumption
  judge def_eq, id
  defeq symm, subst
  defeq trans, step
  step pi
  defeq trans, pleft, step
  step nil
  defeq trans, pright, step
  step pi
  defeq trans, pright, pleft, step
  step const'
  defeq symm, trans, step
  step pi
  defeq trans, pright, step
  step pi
  defeq trans, pleft, step
  step nil
  defeq pright, subst, symm, trans, step
  step pi
  defeq trans, pright
  exact h_eq_γ
  defeq trans, pleft, step
  step nil
  defeq symm, trans, step
  step pi
  defeq trans, pright, step
  step nil
  defeq trans, pright
  exact h_eq_γ.symm
  defeq trans, pleft
  defeq step
  step nil
  defeq trans, pright
  exact h_eq_γ
  defeq refl
  exact h_eq_γ

theorem project_well_typed : ValidJudgment xs β → ValidJudgment x α
  → ValidJudgment γ (mk_arrow β (mk_arrow α Ty))
  → ValidJudgment α Ty
  → ValidJudgment β Ty
  → ValidJudgment δ Ty
  → ValidJudgment π (Pi ($ nil, β) (Pi ($ const', (mk_arrow α Ty), β, ($ nil, α)) γ))
  → DefEq ($ γ, xs, x) δ
  → ValidJudgment ($ ::[x, xs], π) δ := by
  intro h_t_xs h_t_x h_t_γ h_t_α h_t_β h_t_π h_eq_γ
  judge def_eq, sapp, cons
  repeat assumption

