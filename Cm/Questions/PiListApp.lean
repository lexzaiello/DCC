import Mathlib.Data.Nat.Notation

/-
Summary of changes:

- We can actually compose Pi ::[Pi, stuff], and this will induce a normal
Pi expression eventually, but not until we way.
- ($ Pi, ::[t_in, t_out]) - this is insert. This will just do nothing if we try
to substitute.
  - We shouldn't end up with ($ Pi, ::[t_in, t_out]), except after
  running fst or snd to get input / output.
- Removed arg from fst / snd. just snd _ _ ::[a, b]. This will be easier to work
with and avoid redundancy.
we can compose fst and snd.
- Applied Pi is a type, but otherwise, it is an applicable value.
  - Applied Pi, we don't substitute at all?

($ Pi, ::[α, α])
-/

inductive Expr where
  | app    : Expr → Expr → Expr
  | cons   : Expr → Expr → Expr
  | Pi     : Expr
  | Prod   : Expr
  | ty     : Expr
  | const  : Expr
  | const' : Expr
  | both   : Expr
  | id     : Expr
  | nil    : Expr
  | snd    : Expr

syntax ident ".{" term,* "}"  : term
syntax "::[" term,+ "]"       : term
syntax "($" term,+ ")"        : term

macro_rules
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.cons $x ::[$xs,*])
  | `(($ $x:term) ) => `($x)
  | `(($ $f:term, $x:term )) => `(Expr.app $f $x)
  | `(($ $f, $x:term, $args:term,* )) => `(($ (Expr.app $f $x), $args,*))

notation "Ty" => Expr.ty

open Expr

inductive IsStep : Expr → Expr → Prop
  | sapp   : IsStep ($ ::[a, b], x) ($a, ($ b, x))
  | snd    : IsStep ($ snd, α, β, ::[a, b]) b
  | nil    : IsStep ($ nil, α, x) α
  | id     : IsStep ($ Expr.id, _α, x) x
  | both   : IsStep ($ both, _α, _β, _γ, f, g, arg)
    ::[($f, arg), ($ g, arg)]
  | const' : IsStep ($ const', _α, _β, x, y) x
  | const  : IsStep ($ const, _α, _β, x, y) x
  | left   : IsStep f f'
    → IsStep ($ f, x) ($ f', x)
  | right  : IsStep x x'
    → IsStep ($ f, x) ($ f, x')

syntax ident ".{" term,* "}"  : term
syntax "::[" term,+ "]"       : term
syntax "($" term,+ ")"        : term

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | step    : IsStep e e' → DefEq e e'
  | symm    : DefEq e₁ e₂ → DefEq e₂ e₁
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ($ f, x) ($ f', x)
  | right   : DefEq x x'  → DefEq ($ f, x) ($ f, x')
  | subst   : DefEq ($ bdy, x) ($ bdy₂, x)
    → DefEq ($ snd, ($ bdy, x)) ($ snd, ($ bdy₂, x))
    → DefEq ($ Pi, bdy) ($ Pi, bdy₂)

/-
So now we associate to the left for composition.
::[::[::[h, f], g]
-/
def id.type : Expr :=
  ($ Pi, ::[($ nil, Ty)
    , ::[Pi, ($ both, Ty, ($ nil, Ty), ($ nil, Ty), nil, nil)]])

/-
nil.type

γ takes in α, make (α → Ty)
this is another both
output type we want: ($ const', Ty, α, Ty)
output type is just Ty, so it doesn't need the context.

OH WAIT AYO.

($ const', Ty, α, Ty)
(flip ($ const', Ty), Ty)
-/
def nil.type : Expr :=
  ($ Pi, ::[($ nil, Ty)
    , ::[Pi, ($ both, Ty, ($ nil, Ty), ($ nil, Ty), nil, nil)]])

inductive ValidJudgment : Expr → Expr → Prop
  | cons  : ValidJudgment xs β
    → ValidJudgment x α
    → ValidJudgment ::[x, xs] ($ Pi, ::[α, β])
  | Pi    : ValidJudgment Pi   ($ Pi, ::[($ nil, Ty), Prod])
  | Prod  : ValidJudgment Prod ($ Pi, ::[($ nil, Ty), Prod])
  | app   : ValidJudgment fn ($ Pi, ::[t_in, t_out])
    → ValidJudgment arg ($ ::[t_in, t_out], arg)
    → ValidJudgment ($ fn, arg) ($ t_out, arg)
  | id    : ValidJudgment id id.type
  | ty    : ValidJudgment Ty Ty
  | defeq : ValidJudgment e t₁
    → DefEq t₁ t₂
    → ValidJudgment e t₂

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

example : ValidJudgment α Ty → ValidJudgment x α → ValidJudgment ($ id, α, x) α := by
  intro h_t_α h_t_x
  judge defeq, app, defeq, app, id, defeq
  assumption
  defeq symm, trans
  defeq step
  step sapp
  defeq step
  step nil
  defeq trans, step
  step sapp
  defeq trans, right, step
  step both
  defeq refl
  judge defeq
  assumption
  defeq symm, trans, step
  step sapp
  defeq step
  step nil
  defeq step
  step nil

