import Mathlib.Data.Nat.Notation
import Mathlib.Tactic

/-
∧ is the equivalent of our ⊢ before.

It combines 
-/

abbrev Level := ℕ

inductive Expr where
  | app   : Expr  → Expr → Expr
  | vdash : Expr
  | judge : Level → Expr
  | fst   : Expr
  | snd   : Expr
  | id    : Level → Expr
  | prop  : Expr
  | comp  : Expr
  | and   : Expr
  | ty    : Level → Expr

abbrev Term := Expr
abbrev Typ  := Expr

open Expr

syntax "⸨" term+ "⸩"       : term

notation "Ty" => Expr.ty
notation "Prp" => Expr.prop
notation "∶" => Expr.judge

macro_rules
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f $x)
  | `(⸨ $f $x:term $args:term*⸩) => `(⸨ (Expr.app $f $x) $args*⸩)

infixl:90 " ∧ " => (fun f g => ⸨Expr.and f g⸩)

notation "⊢" => Expr.vdash
notation "∘" => Expr.comp

inductive IsStep : Expr → Expr → Prop
  | id     : IsStep ⸨(Expr.id m) _α x⸩ x
  | fst    : IsStep ⸨fst ⸨(∶ m) α x⸩⸩ ⸨(∶ m.succ) (Ty m) α⸩
  | snd    : IsStep ⸨snd ⸨(∶ m.succ) α x⸩⸩ ⸨(∶ m) x⸩
  | japp   : IsStep ⸨⸨(∶ m) α f⸩ ⸨(∶ n) β x⸩⸩ ⸨(∶ (max m n).succ) ⸨α x⸩ ⸨f x⸩⸩
  | fst'   : IsStep ⸨fst (a ∧ b)⸩ a
  | snd'   : IsStep ⸨snd (a ∧ b)⸩ b
  | subst  : IsStep ⸨⸨⊢ α β⸩ x⸩ ⸨⊢ ⸨α x⸩ ⸨β x⸩⸩
  | fdash  : IsStep ⸨fst ⸨⊢ α β⸩⸩ α
  | sdash  : IsStep ⸨snd ⸨⊢ α β⸩⸩ β
  | comp   : IsStep ⸨∘ f g x⸩ ⸨f ⸨g x⸩⸩
  | const' : IsStep ⸨const' _α _β x y⸩ x
  | left   : IsStep f f'
    → IsStep ⸨f x⸩ ⸨f' x⸩
  | right  : IsStep x x'
    → IsStep ⸨f x⸩ ⸨f x'⸩

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | step    : IsStep e e' → DefEq e e'
  | symm    : DefEq e₁ e₂ → DefEq e₂ e₁
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ⸨f x⸩ ⸨f' x⸩
  | right   : DefEq x x'  → DefEq ⸨f x⸩ ⸨f x'⸩

/-
id : ∀ (α : Type), α → α

id : (const' (Ty m) ⊢ snd ⊢ (id Prp)
-/
def id.type (m : Level) : Expr :=
  ⸨⊢ ⸨(∶ m.succ) (Ty m)⸩ ⸨⊢ snd ⸨(id 0) Prp⸩⸩⸩

inductive ValidJudgment : Typ → Term → Prop
  | ty    : ValidJudgment (Ty m.succ) (Ty m)
  | prp   : ValidJudgment (Ty 0) Prp
  | app   : ValidJudgment t_f f
    → ValidJudgment ⸨fst ⸨t_f x⸩⸩ x
    → ValidJudgment ⸨snd ⸨t_f x⸩⸩ ⸨f x⸩
  | defeq : ValidJudgment ⸨(∶ m) t₁ e⸩ e
    → DefEq t₁ t₂
    → ValidJudgment ⸨(∶ m) t₂ e⸩ e
  | id    : ValidJudgment (id.type m) (id m)

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

theorem id_well_typed : ValidJudgment (Ty m) α
  → ValidJudgment α x
  → ValidJudgment ⸨(∶ m) α ⸨(id m) α x⸩ := by
  intro h_t_α h_t_x
  judge defeq
  
  sorry
