import Mathlib.Data.Nat.Notation

/-
  Minor alterations to Pi.lean to answer research question #4:
  - Is it possible to change the Π substitution rule such that we can form
    Pi types at runtime easier?

  We would like to form Pi expressions at runtime with the "advancement"
  feature we have in the kernel.

  It's worth considering:

  (Pi t_in t_out) a b = (Pi t_in t_out) ::[b, a]

  I like this approach ^ the best. We can avoid comp for now.

  But, we will need to make use DefEq picks up how to do this.

  We should leave the main Pi ValidJudgment the same, though.

  1. Does this new distinction between ValidJudgment and Pi
    break anything? Probably breaks strong normalization. Maybe.

  2. Prod currently seems quite inflexible.
    Is (Prod α (β : α → Type)) better?

  3. By adding cons' combinator version of cons, we can actually get around
    having a separate IsStep for Pi.

    (Pi t_in t_out) ∘ cons'. Nope.
    But, we should use cons' instead of cons.

    (Pi t_in t_out) a b = (Pi t_in t_out) ::[b, a]

    (Pi t_in t_out) ::[a, b] c = (Pi t_in t_out) (cons' ::[a, b] c) = ::[::[a, b], c]

    cons' should actually be push, I think.

  4. For later: should we special case push and just get rid of cons? Unclear.

  5. Prod α β ::[(x : (α : β → Type)), (xs : β)]?
-/

inductive Expr where
  | app    : Expr → Expr → Expr
  /- List-like objects
     They come with built-in projection.
     They are the mirror image of application "as data". -/
  | cons   : Expr → Expr → Expr
  /-
    Combinator version of cons.

    5. Is this totally unnecessary?
  -/
  | push  : Expr
  /-
    ::[x, xs] lists are a special case. They are the mirror
    image of application as data. They internalize a projector
    argument π.

    Prod (α : β → Type) (β : Type)
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
  | both   : Expr
  | const  : Expr
  | const' : Expr
  | id     : Expr
  -- This is a necessary for bridging ::[a, b] π to π ::[a, b]
  | flip   : Expr
  | comp   : Expr
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

inductive IsStep : Expr → Expr → Prop
  | sapp   : IsStep ($ ::[x, f], fn) ($ fn, f, x)
  -- To allow forming Pi expressions using list syntax.
  -- cons
  | pi     : IsStep ($ Pi Tin Tout, a, b) ($ Pi t_in t_out, ::[b, a])
  | nil    : IsStep ($ nil, α, x) α
  | id     : IsStep ($ Expr.id, _α, x) x
  | both   : IsStep ($ both, _α, _β, _γ, f, g, x)
    ::[($ f, x), ($ g, x)]
  | const' : IsStep ($ const', _α, _β, x, y) x
  | const  : IsStep ($ const, _α, _β, x, y) x
  /-
    This is a less powerful, less dependent version of flip.

    flip (α : Type) (β : α → Type)
      (x : α)
      (y : ∀ (x : α), β x), γ x
  -/
  | flip   : IsStep ($ flip, _α, _β, x, z) ($ z, x)
  /-
    Another less powerful version of the B combinator.

    comp (α β : Type)
      (γ : β → Type)
      (f : ∀ (x : β), γ x)
      (g : α → β)
      (x : α), γ (g x)

    comp f g x = f (g x)
  -/
  | comp   : IsStep ($ comp, α, β, γ, f, g, x) ($ f, ($ g, x))
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
  | pi      : DefEq ($ Pi i o, x) ($ Pi ($ i, x) ($ o, x))
  | subst   : DefEq ($ (Pi α₁ β₁), x) ($ (Pi α₂ β₂), x)
    → DefEq (Pi α₁ β₁) (Pi α₂ β₂)

def mk_arrow (α β : Expr) : Expr :=
  (Pi ($ nil, α) ($ const', Ty, α, β))

def id.type : Expr :=
  (Pi ($ nil, Ty) (Pi nil nil))

def nil.type : Expr :=
  (Pi ($ nil, Ty) (Pi nil ($ nil, ($ nil, Ty))))

def Pi.type : Expr :=
  Ty

/-
::[a, b] fst = a
-/
def fst_postfix (α β : Expr := Ty) : Expr :=
  let f := ($ id, β)
  ($ const', (mk_arrow β β), α, f)

def fst_postfix.type (α β : Expr := Ty) : Expr :=
  (mk_arrow α (mk_arrow β β))

def pair.mk_type (α β : Expr) : Expr :=
  (Prod ($ const', Ty, Ty, α) β)

/-
List projection, but in head position.

fst ::[a, b] = a

This is essentially our flip combinator.

flip fst ::[a, b]

We assume here that (β : α → Type)
-/
def fst (α β : Expr := Ty) : Expr :=
  ($ flip, (fst_postfix.type α β), (Prod α β), (fst_postfix α β))

/-
List projection, but in tail position.

::[a, b] snd = b
-/
def snd_postfix (α β : Expr := Ty) : Expr :=
  ($ const', β, α)

def snd_postfix.type (α β : Expr := Ty) : Expr := (mk_arrow β (mk_arrow α β))

/-
We also assume here (β : α → Type)
-/
def snd (α β : Expr := Ty) : Expr :=
  ($ flip, (snd_postfix.type α β), (Prod α β), (snd_postfix α β))

/-
  Const type now.
  We can use our new substitution here.

  But how do we trigger it?

  Assume for α → β → α that we have ::[β, α] in scope.

  (Pi (fst Ty (Prod Ty Ty)) (Pi (comp (Prod Ty Ty) (nil Ty) _ (fst Ty (Prod Ty Ty))

  (Pi (nil Ty) (Pi (const' (mk_arrow Ty Ty) Ty (nil Ty)) (Pi (
-/

def const.type.mk_out_arr : Expr :=
  /-
    ::[(x : α : β → Type), xs : (β : Type)]
  -/

  let t_β_α := Prod ($ nil, Ty) Ty

  -- with ::[β, α] in scope
  let t_y := (fst ($ nil, Ty) Ty)
  let t_x := (snd ($ nil, Ty) Ty)
  let t_x_β_α := Prod t_x t_β_α
  /- with ::[y, β, α] in scope
   we want just α
   we know that snd will give us
   t_β_α
   ::[β, α]
   we do snd again
  -/
  -- with ::[x, β, α] in scope
  let whole_t_y := ($ comp, t_x_β_α, t_β_α, ($ const', Ty, t_β_α, Ty), (snd ($ nil, Ty) Ty), (snd t_y t_β_α))
  let t_all := Prod whole_t_y t_x_β_α

  -- with ::[y, x, β, α] in scope
  -- then ::[x, β, α]
  -- (snd ∘ snd ∘ snd) ::[y, x, β, α] = α
  -- snd ∘ snd ::[x, β, α] = α
  -- working inside to out
  let α := ($ comp,
    t_all,
    t_x_β_α,
    ($ nil, nil),
    ($ comp, t_x_β_α, t_β_α, (fst ($ nil, Ty) Ty), t_x, t_x),
    (snd whole_t_y t_x_β_α))

  (Pi α (Pi β α))

def const.type : Expr :=
  

inductive ValidJudgment : Expr → Expr → Prop
  /- TODO: Remove this in the actual calculus
     use type universes
     this module is just for answering reseach questions -/
  | ty        : ValidJudgment Ty Ty
  | cons      : ValidJudgment x β
    → ValidJudgment xs α
    → ValidJudgment α Ty
    → ValidJudgment β (mk_arrow α Ty)
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

   Prod α β ::[(x : (β : α → Type)), (xs : α)]
  -/
  | sapp      : ValidJudgment ::[a, b] (Prod α β)
    → ValidJudgment a β
    → ValidJudgment b α
    → ValidJudgment γ (mk_arrow β (mk_arrow α Ty))
    → ValidJudgment π (Pi ($ nil, β) (Pi ($ const', (mk_arrow α Ty), β, ($ nil, α)) γ))
    → ValidJudgment ($ ::[a, b], π) ($ γ, b, a)
  | defeq    : ValidJudgment e α
    → DefEq α β
    → ValidJudgment e β

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

theorem id_well_typed : ValidJudgment α Ty → ValidJudgment x α → ValidJudgment ($ id, α, x) α := by
  intro h_t_α h_t_x
  judge defeq, app, defeq, app, id, defeq
  assumption
  defeq symm, trans, step
  step nil
  defeq refl, trans, pi, refl
  judge defeq
  assumption
  defeq symm, trans, step
  step nil
  defeq refl
  defeq trans, step
  step nil
  defeq refl

abbrev nil_ty_out {α : Expr} : Expr := (Pi Ty (Pi ($ nil, α) ($ nil, Ty)))

theorem rw_nil_ty : DefEq ($ nil.type, α) (@nil_ty_out α) := by
  unfold nil.type
  defeq trans, pi
  defeq trans, pleft, step
  step nil
  defeq trans, pright, pi
  unfold nil_ty_out
  defeq pright, pright, step
  step nil

abbrev nil_ty₁_out {α : Expr} := (Pi α Ty)

def pop_t_out : Expr → Expr
  | (Pi _t_in t_out) => t_out
  | e => e

theorem rw_nil_ty_out : DefEq (pop_t_out (@nil_ty_out α)) (Pi ($ nil, α) ($ nil, Ty)) := by
  simp [pop_t_out]
  defeq refl

theorem rw_nil_ty₁ {α x : Expr} : DefEq ($ (pop_t_out (@nil_ty_out α)), x) (@nil_ty₁_out α) := by
  simp [pop_t_out]
  defeq trans, pi
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
  judge defeq, app, defeq, app, nil
  judge defeq
  exact h_t_α
  defeq symm, trans, step
  step nil
  defeq refl, trans
  show DefEq (pop_t_out (@nil_ty_out α)) _
  apply rw_nil_ty_out
  simp [pop_t_out]
  defeq trans, pi
  defeq pright
  defeq trans, step
  step nil
  defeq refl
  judge defeq
  exact h_t_x
  defeq symm, trans, step
  step nil
  defeq refl
  defeq trans, step
  step nil
  defeq refl

/-theorem project_well_typed : ValidJudgment xs β → ValidJudgment x α
  → ValidJudgment γ (mk_arrow β (mk_arrow α Ty))
  → ValidJudgment α Ty
  → ValidJudgment β Ty
  → ValidJudgment δ Ty
  → ValidJudgment π (Pi ($ nil, β) (Pi ($ const', (mk_arrow α Ty), β, ($ nil, α)) γ))
  → DefEq ($ γ, xs, x) δ
  → ValidJudgment ($ ::[x, xs], π) δ := by
  intro h_t_xs h_t_x h_t_γ h_t_α h_t_β h_t_π h_eq_γ
  judge defeq, sapp, cons
  repeat assumption-/
