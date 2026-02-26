import Dcc.Ast

syntax "mk_arrow.{" term "}("  comb ","  comb ")" : comb
syntax "α_to_set.{" term "}("  comb ")"      : comb
syntax "βx_to_set.{" term "}("  comb "," comb ")" : comb
syntax "K.type.{" term "}" : comb
syntax "K.type.{" term "}" : comb
syntax "K'.type.{" term "}" : comb
syntax "S.type.{" term "}" : comb
syntax "Sf.type.{" term "}" : comb
syntax "Sγ.type.{" term "}(" comb,* ")" : comb
syntax "S.type.type.{" term "}" : comb
syntax "K.type.type.{" term "}" : comb
syntax "K'.type.type.{" term "}" : comb
syntax "Sort.type.{" term "}" : comb
syntax "Π.type.{" term "}" : comb
syntax "MK'.type.{" term "}" : comb
syntax "MK.type.{" term "}" : comb
syntax "MS.type.{" term "}" : comb

macro_rules
  | `(⟪mk_arrow.{[$m, $n]}($α, $β)⟫) =>
    `(⟪Π.{[$m, $n]} $α (K'.{[($n).succ, $m]} (Sort $n) $α $β)⟫)
  | `(⟪α_to_set.{[$m, $n]}($α)⟫) =>
    `(⟪mk_arrow.{[$m, ($n).succ]}($α, Sort $n)⟫)
  | `(⟪βx_to_set.{[$n, $o]}($β, $x)⟫) =>
    `(⟪mk_arrow.{[$n, ($o).succ]}(($β $x), Sort $o)⟫)
  | `(⟪K.type.{[$m, $n]}⟫) => `(⟪Π.{[($m).succ, $m]} (Sort $m) (M K.{[$m, $n]})⟫)
  | `(⟪K'.type.{[$m, $n]}⟫) => `(⟪Π.{[($m).succ, $m]} (Sort $m) (M K'.{[$m, $n]})⟫)
  | `(⟪S.type.{[$m, $n, $o]}⟫) => `(⟪Π.{[($m).succ, $o]} (Sort $m) (M S.{[$m, $n, $o]})⟫)
  | `(⟪S.type.type.{[$_m, $_n, $o]}⟫) => `(⟪Sort $o⟫)
  | `(⟪K.type.type.{[$m, $_n]}⟫) => `(⟪Sort $m⟫)
  | `(⟪K'.type.type.{[$m, $_n]}⟫) => `(⟪Sort $m⟫)
  | `(⟪Sort.type.{[$m]}⟫) => `(⟪Sort ($m).succ⟫)
  | `(⟪Π.type.{[$m, $n]}⟫) => `(⟪mk_arrow.{[($m).succ, ($n).succ]}(Sort $m, Sort $n)⟫)
  | `(⟪MK'.type.{[$m, $_n]}⟫) => `(⟪Sort $m⟫)
  | `(⟪MK.type.{[$m, $_n]}⟫) => `(⟪Sort $m⟫)
  | `(⟪MS.type.{[$_m, $_n, $o]}⟫) => `(⟪Sort $o⟫)
  | `(⟪Sγ.type.{[$m, $n, $o]}($α, $β)⟫) => `(⟪Π.{[$m, ($o).succ.succ]} $α (M Sγ.{[$m, $n, $o]} $α $β)⟫)

inductive IsStepM : Expr → Expr → Prop
  /-
    Nondependent K combinator type:
  -/
  | k'₁     : IsStepM ⟪(M K'.{[m, n]}) α⟫ ⟪Π.{[n.succ, m]} (Sort n) (M (K'.{[m, n]} α))⟫
  | k'₂     : IsStepM ⟪(M (K'.{[m, n]} α)) β⟫ ⟪Π.{[m, m]} α (M (K'.{[m, n]} α β))⟫
  | k'₃     : IsStepM ⟪(M (K'.{[m, n]} α β)) x⟫ ⟪Π.{[m, m]} β (K'.{[m.succ, n]} (Sort m) β α)⟫
  /-
    Dependent K combinator type:
  -/
  | k₁      : IsStepM ⟪(M K.{[m, n]}) α⟫ ⟪Π.{[n.succ.succ, m]}
    α_to_set.{[m, n]}(α)
    (M (K.{[m, n]} α))⟫
  | k₂      : IsStepM ⟪(M (K.{[m, n]} α)) β⟫ ⟪Π.{[m, m]} α (M (K.{[m, n]} α β))⟫
  | k₃      : IsStepM ⟪(M (K.{[m, n]} α β)) x⟫ ⟪Π.{[m, m]} (β x) (M (K.{[m, n]} α β x))⟫
  | k₄      : IsStepM ⟪(M (K.{[m, n]} α β x)) y⟫ α
  /-
    S combinator type:
  -/
  | sγ      : IsStepM ⟪(M Sγ.{[m, n, o]} α β) x⟫ ⟪βx_to_set.{[n, o]}(β, x)⟫
  | sf      : IsStepM ⟪(M (Sf.{[m, n, o]} α β γ)) x⟫ ⟪Π.{[n, o]} (β x) (γ x)⟫
  | s₁      : IsStepM ⟪(M S.{[m, n, o]}) α⟫ ⟪Π.{[n.succ.succ, o]} (α_to_set.{[m, n]}(α))
    (M (S.{[m, n, o]} α))⟫
  | s₂      : IsStepM ⟪(M (S.{[m, n, o]} α)) β⟫ ⟪Π.{[o.succ.succ, o]}
    Sγ.type.{[m, n, o]}(α, β)
    (M (S.{[m, n, o]} α β))⟫
  | s₃      : IsStepM ⟪(M (S.{[m, n, o]} α β)) γ⟫ ⟪Π.{[o, o]} (Π.{[m, o]} α (M (Sf.{[m, n, o]} α β γ)))
    (M (S.{[m, n, o]} α β γ))⟫
  | s₄      : IsStepM ⟪(M (S.{[m, n, o]} α β γ)) x⟫ ⟪Π.{[n, o]} (Π.{[m, n]} α β)
    (M (S.{[m, n, o]} α β γ x))⟫
  | s₅      : IsStepM ⟪(M (S.{[m, n, o]} α β γ x)) y⟫ ⟪Π.{[m, o]} α
    (M (S.{[m, n, o]} α β γ x y))⟫
  | s₆      : IsStepM ⟪(M (S.{[m, n, o]} α β γ x y)) z⟫ ⟪γ z (y z)⟫

inductive IsStep : Expr → Expr → Prop
  | left    : IsStep f f'  → IsStep ⟪f x⟫ ⟪f' x⟫
  | right   : IsStep x x'  → IsStep ⟪f x⟫ ⟪f x'⟫
  | M       : IsStepM x x' → IsStep x x'
  | K       : IsStep ⟪K.{[m, n]} α β x y⟫ x
  | K'      : IsStep ⟪K'.{[m, n]} α β x y⟫ x
  | S       : IsStep ⟪S.{[m, n, o]} α β γ x y z⟫ ⟪(x z) (y z)⟫
  | pi      : IsStep ⟪Π.{[m, n]} α β x⟫ ⟪β x⟫

inductive IsStepStar : Expr → Expr → Prop
  | refl  : IsStepStar e e
  | step  : IsStep e e'
    → IsStepStar e e'
  | trans : IsStepStar e₁ e₂ → IsStepStar e₂ e₃ → IsStepStar e₁ e₃

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | symm    : DefEq e e'  → DefEq e' e
  | step    : IsStep e e' → DefEq e e'
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ⟪f x⟫ ⟪f' x⟫
  | right   : DefEq x x'  → DefEq ⟪f x⟫ ⟪f x'⟫

inductive ValidJudgment : Expr → Expr → Prop
  | Sort  : ValidJudgment ⟪Sort.type.{[m]}⟫ ⟪Sort m⟫
  | S     : ValidJudgment ⟪S.type.{[m, n, o]}⟫ ⟪S.{[m, n, o]}⟫
  | K     : ValidJudgment ⟪K.type.{[m, n]}⟫ ⟪K.{[m, n]}⟫
  | K'    : ValidJudgment ⟪K'.type.{[m, n]}⟫ ⟪K'.{[m, n]}⟫
  | Pi    : ValidJudgment ⟪Π.type.{[m, n]}⟫ ⟪Π.{[m, n]}⟫
  | MK    : ValidJudgment ⟪MK.type.{[m, n]}⟫ ⟪M K.{[m, n]}⟫
  | MK'   : ValidJudgment ⟪MK'.type.{[m, n]}⟫ ⟪M K'.{[m, n]}⟫
  | MS    : ValidJudgment ⟪MS.type.{[m, n, o]}⟫ ⟪M S.{[m, n, o]}⟫
  | app   : ValidJudgment ⟪Π.{[m, n]} α cod⟫ f
    → ValidJudgment α x
    → ValidJudgment ⟪cod x⟫ ⟪f x⟫
  | defeq : ValidJudgment t x
    → IsStepStar t t'
    → ValidJudgment t' x

syntax "defeq" ident,*         : tactic
syntax "step" ident,*          : tactic
syntax "step?" ident,*         : tactic
syntax "stepM?" ident,*     : tactic
syntax "stepM" ident,*         : tactic
syntax "judge" ident,*         : tactic
syntax "judgeEq" ident,*        : tactic

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
  | `(tactic| stepM? $cmd) => do
    let inner ← `(tactic| stepM $cmd)
    `(tactic| (apply IsStepStar.step; $inner))
  | `(tactic| step? refl) => `(tactic| apply IsStepStar.refl)
  | `(tactic| step? trans) => `(tactic| apply IsStepStar.trans)
  | `(tactic| step? $fn:ident,*) => do
    let nms : Array (Lean.TSyntax `tactic) ← (Array.mk <$> (fn.getElems.toList.mapM (fun name =>
      let nm := Lean.mkIdent (Lean.Name.mkStr `IsStep name.getId.toString)
      `(tactic| (apply IsStepStar.step; apply $nm)))))

    `(tactic| $[$nms];*)
  | `(tactic| stepM $fn:ident,*) => do
    let nms : Array (Lean.TSyntax `tactic) ← (Array.mk <$> (fn.getElems.toList.mapM (fun name =>
      let nm := (Lean.mkIdent (Lean.Name.mkStr `IsStepM name.getId.toString))
      `(tactic| (apply IsStep.M; apply $nm)))))

    `(tactic| $[$nms];*)
  | `(tactic| judge $fn:ident,*) => do
    let nms : Array (Lean.TSyntax `tactic) ← (Array.mk <$> (fn.getElems.toList.mapM (fun name =>
      let nm := Lean.mkIdent (Lean.Name.mkStr `ValidJudgment name.getId.toString)
      `(tactic| apply $nm))))

    `(tactic| $[$nms];*)
  | `(tactic| judgeEq $fn:ident,*) => do
    let nms : Array (Lean.TSyntax `tactic) ← (Array.mk <$> (fn.getElems.toList.mapM (fun name =>
      let nm := Lean.mkIdent (Lean.Name.mkStr `ValidJudgment name.getId.toString)
      `(tactic| (apply ValidJudgment.defeq; apply $nm)))))

    `(tactic| $[$nms];*)
