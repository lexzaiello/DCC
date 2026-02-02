import Mathlib.Data.Nat.Notation

/-
#1: how valuable are our lists if we don't have substitution?

- Our lists are very minimal. Remember the reduction rule for Π.

(Π t_in t_out) x = Π (t_in x) (t_out x)

We could do something similar for lists.
This would significantly change the meaning, though.

We can recover this functionality with both.

Another question:
- how useful is term both?

if both acts as substitution, that could be quite nice.

Both worked very well before.

TODO: will need to fix instances of both later.

both ::[($ nil, α), β] x
= ::[α, β x]
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
    both creates a new list by applying a value inside a list.
    both α β γ ::[f, g] x
    = ::[(f x), (g x)]
    both ::[($ nil, α), β] x
= ::[α, β x]
  -/
  | both   : Expr
  | const  : Expr
  | const' : Expr
  | id     : Expr
  -- This is a necessary for bridging ::[a, b] π to π ::[a, b]
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
  | both   : IsStep ($ both, _α, _β, _γ, ::[f, g], x) ::[($f, x), ($ g, x)]
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
nondependent fst
-/
def fst_postfix' (α β : Expr := Ty) : Expr :=
  let f := ($ id, α)
  ($ const', (mk_arrow α α), β, f)

/-
List projection, but in tail position.

::[a, b] snd = b
::[a, b] snd = snd b a

α receives (x : β)
-/
def snd_postfix (α β : Expr := Ty) : Expr :=
  ($ const, β, α)

/-
Performs sigma substitution.

β depends on (a : α)
::[a, (b : β)] subst
= b a
-/
def subst_postfix (β : Expr := Ty) : Expr :=
  ($ id, β)

/-
List projection, but in tail position.
Nondependent variant.

::[a, b] snd = b
::[a, b] snd = snd b a

α receives (x : β)
-/
def snd_postfix' (α β : Expr := Ty) : Expr :=
  ($ const', β, α)

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

/-
α : Type
β x : Type
β we assume to be a function of (x : α)

β gets the context ::[α, x]

β : 

β : Prod (Prod Ty ($ id, Ty)) ($ const', Ty, (Prod Ty ($ id, Ty)), Ty)

alternatively:

x : α
y : β x
out: α

so we need to track α, β, and x

β has in scope at first just α
-/
def const.type.β.type : Expr :=
  Pi nil ($ const', Ty, (Prod Ty ($ id, Ty)), Ty) Expr.cons

def const.type.α.type : Expr := Ty

-- ::[α, β], gets α
def const.type.x.type_from_αβ : Expr :=
  ::[snd_postfix const.type.α.type const.type.β.type, ($Expr.cons, Ty)]

-- ::[α, β]
def const.type.αβ.type : Expr :=
  Prod const.type.α.type const.type.β.type

-- ::[::[α, β], x]
-- fake value: ::[::[::[α, β], x], Ty]
def const.type.αβx.type : Expr :=
  Prod const.type.αβ.type const.type.x.type_from_αβ

def const.type.x.type_from_αβx : Expr :=
  ::[::[::[const.type.x.type_from_αβ
        , fst_postfix const.type.αβ.type const.type.x.type_from_αβ]
        , snd_postfix' const.type.αβx.type Ty]
  , ($ Expr.cons, Ty)]

/-
With ::[::[α, β], x] in scope.
-/
def const.type.β.type_from_αβx : Expr :=
  sorry

/-
  with ::[::[α, β], x] in scope

  Remember, β : Pi ...

  ($ both
   , const.type.αβx.type
   , ($ const', Ty, const.type.αβx.type, const.type.β.type)
   , const.type.x.type_from_αβx
   , ::[snd_postfix, fst_postfix]
   , ::[::[snd_postfix const.type.αβ.type const.type.x.type_from_αβ, snd_postfix Ty const.type.αβx.type], (Expr.cons Ty)]
   , ::[fst_postfix _ _, Expr.cons])

  y : β x.
-/
def const.type.y.type : Expr :=
  ($ both
   , const.type.αβx.type
   , const.type.x.type_from_αβx
   , ($ const', Ty, const.type.αβx.type, const.type.β.type) -- with ::[::[α, β], x] in scope
   , ::[snd_postfix, fst_postfix]
   , ::[::[snd_postfix const.type.αβ.type const.type.x.type_from_αβ
         , snd_postfix Ty const.type.αβx.type]
         , ($ Expr.cons, Ty)])

/-
y : (β ::[α, x])
entire context: ::[::[α, β], x]

smart way to do this:
both _ _ _  ::[::[snd_postfix, snd_postfix], Expr.cons] ??
               ^ this grabs β
??

::[x, cons] ::[(flip cons), α]
= ::[(flip cons), α] cons x
= cons α ((flip cons)) x
= ::[α, ((flip cons))] x
= ((flip cons)) x α
= ::[α, x]

flip ::[a, b] = ::[b, a]

flip = ::[id _, Expr.cons]

::[Expr.cons, Expr.cons] ::[a, b] = ::[a, b] Expr.cons id _
= Expr.cons b a (id _)
= ::[b, a] (id _)
= (id _) a b


-/
def const.type.αβxy.type : Expr :=
  Prod const.type.αβx.type const.type.y.type

def const.type : Expr :=
  (Pi
    ($ nil, const.type.α.type)
    (Pi
      const.type.β.type -- this receives ::[α, β]. beta.
      (Pi -- ::[::[α, β], x] in scope
        const.type.x.type_from_αβx -- (x : α)
        (Pi -- ::[::[α, β], x] in scope, but NOT y. y gets discarded.
          const.type.y.type
          const.type.x.type_from_αβx
          ($ const, const.type.αβx.type, const.type.y.type))
      Expr.cons) -- ::[::[α, β], x]
      Expr.cons) -- make ::[α, β]
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
  | const     : ValidJudgment const const.type
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

theorem rw_const_defeq_const' {α β γ δ x y y₂ : Expr} : DefEq ($ const, α, β, x, y) ($ const', γ, δ, x, y₂) := by
  defeq trans, step
  step const
  defeq symm, trans, step
  step const'
  defeq refl

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

theorem const_well_typed : ValidJudgment α Ty
  → ValidJudgment β (Pi ($ nil, α) ($ const', Ty, α, Ty) ($ id, α))
  → ValidJudgment x α
  → ValidJudgment y ($ β, x)
  → ValidJudgment ($ const, α, β, x, y) α := by
  intro h_t_α h_t_β h_t_x h_t_y
  judge defeq, app, defeq, app, defeq, app, defeq, app, const, defeq
  assumption
  defeq symm, trans, step
  step nil
  defeq refl
  defeq pi
  judge defeq
  assumption
  defeq symm, trans
  defeq trans, step
  
  sorry

/-
const : ∀ (α : Type) (β : α → Type) (x : α) (y : β x), α
α = Prod Ty ($ nil, Ty)
β = ($ const', Ty, Prod Ty ($ nil, Ty), Ty)
x = ::[Ty, Ty]
β x = Ty
y : Ty
y = Ty

Trivial example.
-/

example : ValidJudgment ($ const,
  Prod Ty ($ nil, Ty),
  ($ const', Ty, Prod Ty ($ nil, Ty), Ty),
  ::[Ty, Ty],
  Ty) (Prod Ty ($ nil, Ty)) := by
  judge defeq, app, defeq, app, defeq, app, defeq, app, const, defeq, Prod
  defeq symm, trans, right, step
  step id
  defeq trans, step
  step nil
  defeq refl, pi
  judge defeq, app, defeq, app, defeq, app, const', defeq, ty
  defeq symm, trans, step
  step nil
  defeq refl, pi
  judge defeq, Prod
  defeq symm, trans, step
  step const'
  defeq refl
  defeq pi
  judge defeq, ty
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
  unfold const.type.β.type
  unfold const.type.αβ.type
  
