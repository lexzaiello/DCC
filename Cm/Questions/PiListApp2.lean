import Mathlib.Data.Nat.Notation

/-
Special cases I don't like:

- cons function composition feels like a special case for sure

(Σ t, x) : Prop

-/

inductive Expr where
  | app    : Expr → Expr → Expr
  | cons   : Expr → Expr → Expr
  | Pi     : Expr → Expr
  | pair   : Expr → Expr → Expr
  | Prod   : Expr → Expr → Expr
  | fst    : Expr
  | snd    : Expr
  | ty     : Expr
  -- For delimiting lists
  | nil    : Expr
  /-
    The actual SK combinators.
  -/
  | id     : Expr

syntax "::[" term,+ "]"       : term
syntax "($" term,+ ")"        : term
syntax "⟪" term,+ "⟫"  : term

macro_rules
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.cons $x ::[$xs,*])
  | `(($ $x:term) ) => `($x)
  | `(($ $f:term, $x:term )) => `(Expr.app $f $x)
  | `(($ $f, $x:term, $args:term,* )) => `(($ (Expr.app $f $x), $args,*))
  | `(⟪ $x:term ⟫) => `($x)
  | `(⟪ $x:term, $xs:term,* ⟫) => `(Expr.pair $x ⟪ $xs,* ⟫)

notation "Ty" => Expr.ty

open Expr

inductive IsStep : Expr → Expr → Prop
  | fst    : IsStep ($ fst, ⟪ a, b ⟫) a
  | snd    : IsStep ($ snd, ⟪ a, b ⟫) b
  | comp   : IsStep ($ ::[f, g], x) ($ f, ($ g, x))
  | id     : IsStep ($ id _α, x) x
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
  | lleft   : DefEq a a'  → DefEq ⟪ a, b ⟫ ⟪ a', b ⟫
  | lright  : DefEq b b'  → DefEq ⟪ a, b ⟫ ⟪ a, b' ⟫
  | nil_ctx : DefEq (Pi ⟪ ⟪ α, nil ⟫, Γ ⟫) ($ α, Γ)

/-
α → β
-/
def mk_arrow (α β : Expr) : Expr :=
  (Pi ⟪ ⟪ ::[fst, fst], ::[fst, snd, snd], nil ⟫, ⟪ ⟪ α, Ty ⟫, ⟪ β, Ty ⟫ ⟫ ⟫)

def id.type : Expr :=
  (Pi ⟪ ⟪ fst, ::[fst, fst], ::[snd, fst], nil ⟫, ⟪ Ty, Ty ⟫ ⟫)

/-

-/
def fst.type : Expr :=
  (Pi ⟪ 

def nil.type : Expr := (Prod Ty Ty)

inductive ValidJudgment : Expr → Expr → Prop
  | Pi    : ValidJudgment (Prod t_x t_t) Ty
    → ValidJudgment (Prod t_γ_x t_xs) Ty
    → ValidJudgment Ctx (Prod (Prod t_γ_x t_xs) (Prod t_x t_t))
    → ValidJudgment (Pi Ctx) Ty
  /-
    The kernel stores arguments in this order: ⟪ (x : α), (α : Ty) ⟫
    We represent the type of this with (Prod ($ id, Ty) α)
    Note, α is a function of (α : Ty)
  -/
  | Prod  : ValidJudgment α Ty
    → ValidJudgment (Prod α Ty) Ty
  | pair  : ValidJudgment α Ty
    → ValidJudgment x α
    → ValidJudgment ⟪ x, α ⟫ (Prod α Ty)
  | ty    : ValidJudgment Ty Ty
  | comp : ValidJudgment g (mk_arrow α β)
    → ValidJudgment f (mk_arrow β γ)
    → ValidJudgment ::[f, g] (mk_arrow α γ)
  | nil   : ValidJudgment nil nil.type
  | app   : ValidJudgment f (Pi ⟪ ⟪ α, β ⟫, Γ ⟫)
    → ValidJudgment x ($ α, Γ)
    → ValidJudgment ($ f, x) (Pi ⟪ β, ⟪ ⟪ x, ($ α, Γ) ⟫, Γ ⟫ ⟫)
  | id    : ValidJudgment id id.type
  | defeq : ValidJudgment x t₁
    → DefEq t₁ t₂
    → ValidJudgment x t₂

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
  step fst
  defeq refl
  defeq refl
  judge defeq
  assumption
  defeq symm, trans, step
  step comp
  defeq trans, right, step
  step fst
  defeq step
  step fst
  defeq trans, nil_ctx, trans, step
  step comp
  defeq trans, right, step
  step fst
  defeq trans, step
  step snd
  defeq trans, step
  step comp
  defeq trans, right, step
  step fst
  defeq step
  step fst

/-
fst ⟪ (x : α), (y : β) ⟫ : α
-/
theorem fst_well_typed : ValidJudgment x α → ValidJudgment xs β → ValidJudgment ⟪ x, xs ⟫ (Prod α β) → ValidJudgment ($ fst, ⟪ x, y ⟫) α := by
  intro h_t_x h_t_xs h_t_pair
  judge defeq, app
  
