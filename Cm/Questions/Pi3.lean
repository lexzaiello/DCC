import Mathlib.Data.Nat.Notation

/-
  More alternations to Pi2 and Pi.lean to answer research question #6:
  Can we make Pi binders list-context native?

  Old way:
    (Pi t_in t_out) a = (Pi (t_in a) (t_in a))

  Lists are SOOOO nice.

  As far as I understand, we can just merge ValidJudgment and the eval rule.
  However, we need to isolate advancing the entire context to just DefEq.

  #7: Can we assume that our t_in and t_out will be operations on lists?
    If so, can we Δ t_in? No, not really.

  #8: Pi types - if we require that all Pi types look like ($ (Pi t_in t_out), Δ),
  will we ever encounter a Pi type without a Δ? Yes. Keep as is.
  We will need to special case Pi application, probably in multiple ways.

  #9: List of list instructions: can we compose list projection nicely?
    ::[snd, fst] ::[::[c, d], a] = ::[::[c, d], a] fst snd
    = ::[c, d] snd
    = d

  That is really quite nice.
  Hypotheses:
  - can we plug the output type of fst into snd somehow to make things smoother?
  - since we are already applying ($ t_in, Δ), we can compose very easily.
    - We can leave comp to do normal term composition

  - if we use dependent versions of the combinators, can we get around
    having to pass in explicit type arguments every time? - no.

  - another take: we should be able to omit things from the context
    (Pi t_in t_out map_ctx) - map_ctx

    For example, in id, the x and y arguments are totally irrelevant.

  - yet another take: there shouldn't be a step rule for Pi.
    Pi is computationally irrelevant.

    App rule using this method:

    - to do this, we will probably need point-free cons. No reason we can't do that.

    ((f : (Pi t_in t_out map_ctx)) (x : α))
    - domain: (t_in (map_ctx α))
    - codomain: (t_out (map_ctx x))

    - can we express ad-hoc α → β with this approach?

    - this approach could be really nice, since we can capture both the ::[] approach
      and the curried approach.

  #10: can we capture the ::[] and curried approaches with the map_ctx approach?

  #11: this approach seems to make cons align nicer with our Prod α β - ::[a, b]

  ::[g, f] l = l f g
-/

inductive Expr where
  | app    : Expr → Expr → Expr
  /- List-like objects
     They come with built-in projection.
     They are the mirror image of application "as data". -/
  | cons   : Expr
  /-
    ::[x, xs] lists are a special case. They are the mirror
    image of application as data. They internalize a projector
    argument π.

    Prod (α : Type) (β : α → Type)
  -/
  | Prod   : Expr → Expr → Expr
  /-
    Our representation of curried function types.
    Π t_in t_out map_arg
  -/
  | Pi     : Expr → Expr → Expr → Expr
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
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.app (Expr.app Expr.cons $x) ::[$xs,*])
  | `(($ $x:term) ) => `($x)
  | `(($ $f:term, $x:term )) => `(Expr.app $f $x)
  | `(($ $f, $x:term, $args:term,* )) =>
    `(($ (Expr.app $f $x), $args,*))

notation "Ty" => Expr.ty

open Expr

inductive IsStep : Expr → Expr → Prop
  | sapp   : IsStep ($ ::[x, f], fn) ($ fn, f, x)
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
  | pright  : DefEq o o'  → DefEq (Pi i o f) (Pi i o' f)
  | pleft   : DefEq i i'  → DefEq (Pi i o f) (Pi i' o f)
  | pf      : DefEq f f'  → DefEq (Pi i o f) (Pi i o f')
  | pi      : DefEq ($ (Pi i o map_arg), x) (Pi i o ($ map_arg, x))
  | subst   : DefEq ($ (Pi α₁ β₁ map_arg₁), x) ($ (Pi α₂ β₂ map_arg₂), x)
    → DefEq (Pi α₁ β₁ map_arg₁) (Pi α₂ β₂ map_arg₂)

/-
α → β
-/
def mk_arrow (α β : Expr) : Expr :=
  (Pi ($ id, Ty) ($ const', Ty, Ty, β) ($ nil, α))

/-
::[a, b] fst = a

β receives (x : α)
-/
def fst_postfix (α β : Expr := Ty) : Expr :=
  let f := ($ id, α)
  ($ const, (mk_arrow α α), β, f)

/-
List projection, but in tail position.

::[a, b] snd = b
::[a, b] snd = snd b a

α receives (x : β)
-/
def snd_postfix (α β : Expr := Ty) : Expr :=
  ($ const, β, α)

/-
::[a, b] id = b a

::[b, id] a =
id a b
-/

def const'.type : Expr :=
  (Pi -- α in scope
    ($ nil, Ty)
    (Pi -- ::[α, β] in scope
      ($ const', Ty, (Prod Ty ($ nil, Ty)), Ty) -- ty is input
      (Pi -- with still ::[α, β] in scope
        ::[snd_postfix, Expr.cons]
        (Pi
          ::[fst_postfix, Expr.cons]
          ::[snd_postfix, Expr.cons]
          ($ const, (Prod Ty ($ nil, Ty)), ::[fst_postfix, Expr.cons]))
        ($ const, (Prod Ty ($ nil, Ty)), ::[snd_postfix, Expr.cons]))
      Expr.cons)
    ($ id, Ty))

def id.type : Expr :=
  (Pi -- α in scope
    ($ nil, Ty)
    (Pi -- still just α in scope
      ($ id, Ty)
      ($ id, Ty)
      nil)
    ($ id, Ty))


def Pi.type : Expr := Ty

/-
  nil : ∀ (α : Ty), α → Ty
-/
def nil.type : Expr :=
  (Pi -- α in scope
    ($ nil, Ty)
    (Pi -- still just α in scope
      ($ id, Ty)
      ($ nil, Ty)
      nil)
    ($ id, Ty))

/-
To check an application:
- a function will have a type (Pi t_in t_out) Ty.
since all of our combinators with Pi types are explicitly typed,
the first argument will always be a Ty.

- Similarly to in the above step rule, ($ (f : (Pi t_in t_out) Δ), x) : (t_out ::[x, Δ])
-/

inductive ValidJudgment : Expr → Expr → Prop
  /- TODO: Remove this in the actual calculus
     use type universes
     this module is just for answering reseach questions -/
  | ty        : ValidJudgment Ty Ty
  | cons      : ValidJudgment x α
    → ValidJudgment xs β
    → ValidJudgment α Ty
    → ValidJudgment β (mk_arrow α Ty)
    → ValidJudgment ::[x, xs] (Prod α β)
  | id        : ValidJudgment Expr.id id.type
  | nil       : ValidJudgment nil nil.type
  | const'    : ValidJudgment const' const'.type
  | Prod      : ValidJudgment (Prod α β) Ty
  | Pi        : ValidJudgment (Pi Tin Tout Marg) Pi.type
  /-
    To check an app:
    - functions have type Π Tin Tout
    - (Π Tin Tout) Δ = (Π (Tin Δ) (Tout Δ)). This mimicks substitution.
    - (Π (Tin arg) (Tout arg))
    - (((f : Π Tin Tout) (x : α)) : (Tout x))
    - To check that x matches the domain, (Tin x)
  -/
  | app       : ValidJudgment f (Pi Tin Tout Marg)
    → ValidJudgment x ($ Tin, ($ Marg, x))
    → ValidJudgment ($ f, x) ($ Tout, ($ Marg, x))
  /-
   Apps with ::[x, xs] fn are a special case, since they
   do some type inference

   If γ is a Pi expression, we won't automatically get the output.
   γ is not a Pi expression, it is a function. So this is fine!

   Prod α β ::[(x : (β : α → Type)), (xs : α)]
  -/
  | sapp      : ValidJudgment ::[a, b] (Prod α β)
    → ValidJudgment a α
    → ValidJudgment b β
    → ValidJudgment γ (mk_arrow β (mk_arrow α Ty))
    → ValidJudgment π (Pi -- x in scope
      ($ nil, β)
      (Pi -- ::[x, y] in scope. we need to flip x, y, then prepend to γ. ::[y, x, y] cons = cons ::[x, y] γ
        ($ const', Ty, (Prod α β), α)
        ($ both
        , (Prod α β)
        , ($ const'
          , Ty
          , (Prod α β)
          , (mk_arrow β (mk_arrow α Ty)))
        , ($ nil, (Prod α β))
        , ($ const'
          , (mk_arrow β (mk_arrow α Ty))
          , (Prod α β)
          , γ)
        , ($ id, (Prod α β)))
        Expr.cons)
      ($ id, β))
    --→ ValidJudgment π (Pi ($ nil, β) (Pi ($ const', (mk_arrow α Ty), β, ($ nil, α)) γ))
    → ValidJudgment ($ ::[a, b], π) ($ γ, b, a)
  | defeq    : ValidJudgment e α
    → DefEq α β
    → ValidJudgment e β

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

@[simp]
theorem rw_snd_postfix {a b α β : Expr} : DefEq ($ ::[a, b], (snd_postfix α β)) b := by
  defeq trans, step
  step sapp
  defeq step
  step const

@[simp]
theorem rw_fst_postfix {a b α β : Expr} : DefEq ($ ::[a, b], (fst_postfix α β)) a := by
  defeq trans, step
  step sapp
  defeq trans, left, step
  step const
  defeq step
  step id

@[simp]
theorem rw_comp : DefEq ($ ::[g, f], ::[a, b]) ($ ::[a, b], f, g) := by
  defeq step
  step sapp

theorem nil_well_typed : ValidJudgment α Ty → ValidJudgment x α → ValidJudgment ($ nil, α, x) Ty := by
  intro h_t_α h_t_x
  judge defeq, app, defeq, app, nil, defeq
  assumption
  defeq symm, trans, step
  step nil
  defeq refl, pi
  judge defeq
  assumption
  defeq symm, trans, step
  step id
  defeq trans, step
  step nil
  defeq trans, step
  step id
  defeq refl
  defeq trans, step
  step nil
  defeq refl

theorem id_well_typed : ValidJudgment α Ty → ValidJudgment x α → ValidJudgment ($ id, α, x) α := by
  intro h_t_α h_t_x
  judge defeq, app, defeq, app, id, defeq
  assumption
  defeq symm, trans, step
  step nil
  defeq refl, pi
  judge defeq
  assumption
  defeq symm, trans, step
  step id
  defeq trans, step
  step nil
  defeq trans, step
  step id
  defeq refl
  defeq trans, step
  step id
  defeq trans, step
  step nil
  defeq step
  step id

theorem const'_well_typed : ValidJudgment α Ty
  → ValidJudgment β Ty
  → ValidJudgment x α
  → ValidJudgment y β
  → ValidJudgment ($ const', α, β, x, y) α := by
  intro h_t_α h_t_β h_t_x h_t_y
  judge defeq, app, defeq, app, defeq, app, defeq, app, const', defeq
  assumption
  defeq symm, trans, step
  step nil
  defeq refl, pi
  judge defeq
  assumption
  defeq symm, trans, step
  step const'
  defeq refl
  defeq pi
  judge defeq
  assumption
  defeq symm, trans, step
  step sapp
  defeq trans, left, left, step
  step const
  defeq trans, left, step
  step sapp
  defeq trans
  apply rw_snd_postfix
  defeq step
  step id
  defeq pi
  judge defeq
  assumption
  defeq symm, trans, step
  step sapp
  defeq trans, left, left, step
  step const
  defeq trans, left, left, step
  step const
  defeq trans, left, step
  step sapp
  defeq trans
  apply rw_fst_postfix
  defeq refl, trans, step
  step sapp
  defeq trans, left, left, step
  step const
  defeq trans, left, left, step
  step const
  defeq trans, left, step
  step sapp
  defeq trans
  apply rw_snd_postfix
  defeq step
  step id

