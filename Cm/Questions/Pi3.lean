import Mathlib.Data.Nat.Notation

/-
  #1: can we derive S from both?

  both _ _ _ f g x = ::[(g x), (f x)]
  ::[(g x), (f x)] (id _) = (id _) (f x) (g x)
  (f x) (g x)

  (both _ _ _ f g x) (id _)
  = (id _) (f x) (g x)

  ::[x, f, g] (both _ _ _)
  ? = (both _ _ _) ::[f, g] x
  = ::[f, g] (both _ _ _) x
  = (both _ _ _) g f x
  = ::[(f, x), (g, x)]

  ::[x, f, g, γ, β, α] ::[both, 
  = both ::[f, g, γ, β, α]

    both ::[f, g, γ, β, α]

  ::[x, f, g, γ, β, α, both] id
  = id ::[f, g, γ, β, α, both] x
  = ::[f, g, γ, β, α, both] x

  #2: Can we make both easier to use by
  using list arguments and returning to app terms?

  both ::[α, β, γ, f, g, x]
  = (f x) (g x)

  Why not?:
    - Forming the type will be easier, since product types are
    really easy to use
    - We will need to change a tiny bit of code
      TODO: sapp judgment rule uses both. Will need modification.

  Answering questions in PiBetterBoth.lean
-/

/-

::[a, ::[b, ::[c, d]]] π = π ::[b, ::[c, d]] a
::[a, ::[b, ::[c, d]]] id = id ::[b, ::[c, d]] a

::[g, f] ::[x, fn] = ::[x, fn] f g
= f fn x g

β : α → Type
(::[x : α, xs : β]) : (Prod α β)
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
Selects two elements from the context, then creates a (α → β) arrow.
-/
def mk_arrow_pointfree (π_t_in : Expr := ::[snd_postfix, Expr.cons])
  (π_t_out : Expr := ::[fst_postfix, Expr.cons])
: Expr :=
  (Pi -- with ::[α, β] in scope, then ::[::[α, β], x]
    π_t_in -- with ::[α, x] in scope. we want just α
    π_t_out
    -- with ::[α, x] in scope. we want to output Type as the output type
    Expr.cons)

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

/-
Dependent K.

K : ∀ (α : Type) (β : α → Type) (x : α) (y : β x), α
-/

def const.type.just_α : Expr :=
  ::[::[fst_postfix, snd_postfix] -- ::[α, β] doesn't get flipped
    , Expr.cons] -- flip to ::[x, ::[α, β]]. then snd, fst to get α

-- with ::[::[α, β], x] in scope. ::[x, ::[α, β]]
def const.type.β_arrow : Expr :=
  mk_arrow_pointfree just_α
    ($ const, (Prod Ty ($ nil, Ty)), ::[snd_postfix, Expr.cons])

/-
  with ::[x, ::[α, β]] in scope.
  we need β x
  once we've typed (β : α → Type),
  we can reduce β x in the context map
  given we have α in scope,
  but then we destroy α
  what we can do is use both to create a relevant context
  with ::[::[α, β], x] in scope
  we can copy α → Type to the context, maybe
  with α → Type in the context
  it will be easier to do the app.

  ::[x, ::[β, α → Type]] ::[id, id] = ::[id, id] ::[β, α → Type] x
  = ::[β, α → Type] id id x
  = ($ id, α → Type, β) id x

  (both _ _ _ 
-/
def const.type.y_type : Expr :=
  sorry

def const.type : Expr :=
  let β_arrow := const.type.β_arrow

  -- for α, β in scope, we need to make a pi binder, but without substituting
  -- pi application (Pi t_in t_out map_ctx) x causes x to be pushed to map_ctx
  -- so, if ::[α, β] is in scope, we can apply t_in_arrow ::[α, β].
  -- we should use cons as our map_ctx
  (Pi -- α in scope
    ($ nil, Ty) -- first argument is of type Ty
    (Pi -- ::[α, β] in scope.
      β_arrow -- β : α → Type 
      (Pi
        const.type.just_α
        (Pi
          const.type.y_type
          _
          _)
        Expr.cons) -- with ::[::[α, β], x] in scope
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

theorem rw_snd_postfix {a b α β : Expr} : DefEq
  ($ ::[a, b], (snd_postfix α β))
  b := by
  defeq trans, step
  step sapp
  defeq step
  step const

theorem rw_fst_postfix {a b α β : Expr} : DefEq ($ ::[a, b], (fst_postfix α β)) a := by
  defeq trans, step
  step sapp
  defeq trans, left, step
  step const
  defeq step
  step id

theorem rw_comp : DefEq ($ ::[g, f], ::[a, b]) ($ ::[a, b], f, g) := by
  defeq step
  step sapp

theorem nil_well_typed : ValidJudgment α Ty
  → ValidJudgment x α
  → ValidJudgment ($ nil, α, x) Ty := by
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

theorem id_well_typed : ValidJudgment α Ty
  → ValidJudgment x α
  → ValidJudgment ($ id, α, x) α := by
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

