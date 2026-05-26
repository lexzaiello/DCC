import Mathlib.Logic.Relation
import Dcc.Ast
import Dcc.Judge
import Dcc.Attrs
import Dcc.Relation
import Dcc.Attrs
import Dcc.Aff.Red
import Dcc.Eta.Red
import Dcc.Tactic.Reflect
import Lean
import Lean.Elab.Command
import Lean.Parser.Term.Basic
import Qq

open GenAst
open Lean.Elab.Tactic (TacticM)
open Lean.Meta (isDefEq)
open Qq
open Expr (RedEta)

namespace MetaExpr

open Lean Elab Tactic in
def lookup_local_hyp (pre : Lean.Name) (nm : Lean.Expr) : TacticM (Option (MetaExpr × Lean.Expr)) := do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    lctx.findDeclM? (fun decl => do
      match decl.type with
      | .app (.app pre' A) B =>
        if ← isDefEq (.const pre []) pre' then
          if ← isDefEq nm A then
            let B ← MetaExpr.decode B
            return .some (B, (Lean.Expr.const decl.userName []))
          else return .none
        else return .none
      | _ => return .none)

@[dcc_force_reduce, dcc_force_aff]
def step? (e : MetaExpr) : TacticM (Option ((e' : MetaExpr) × (RedAffMeta e e'))) :=
  match e with
  | (DCC[.] (`(_β, _x) _y))                             => return .some ⟨_, .quot⟩
  | (DCC[.] (Id(_α) _x))                                => return .some ⟨_, .id⟩
  | (DCC[.] (Fstc(_α) ⟦_γ⟧(_a, _b)))                    => return .some ⟨_, .fstc⟩
  | (DCC[.] (Sndc(_α) ⟦_γ⟧(_a, _b)))                    => return .some ⟨_, .sndc⟩
  | (DCC[.] ((x ∘' y) z))                               => return .some ⟨(DCC[.] (x (y z))), .comp'⟩
  | (DCC[.] ((x ∘ y) z))                                => return .some ⟨(DCC[.] (x (y z))), .comp⟩
  | (DCC[.] (Λ(_α, β, x) y z))                          => return .some ⟨(DCC[.] (x ⟦β⟧(y, z))), .curr⟩
  | (DCC[.] (Σ(_f_α, _f_β) _env))                       => return .some ⟨_, .sigma⟩
  | DCC[.] ⟦β⟧(x, y) => do
    match ← x.step?, ← y.step? with
    | .some ⟨x', h₁⟩, _ => return .some ⟨(DCC[.] ⟦β⟧(x', y)), .sigl h₁⟩
    | _, .some ⟨y', h₁⟩ => return .some ⟨(DCC[.] ⟦β⟧(x, y')), .sigr h₁⟩
    | _, _ => return .none
  | (DCC[.] (Coup(β))) => do
    match ← β.step? with
    | .some ⟨_, h⟩ => return .some ⟨_, .coup h⟩
    | _ => return .none
  | DCC[.] (f x) => do
    match ← f.step?, ← x.step? with
    | .some ⟨f', h₁⟩, _ => return .some ⟨(DCC[.] (f' x)), .congrFun h₁⟩
    | _, .some ⟨x', h₁⟩ => return .some ⟨(DCC[.] (f x')), .congrArg h₁⟩
    | _, _ => return .none
  | .lean_expr e => do
    match ← lookup_local_hyp ``Expr.RedAff e with
    | .some (a, b) => return .some ⟨a, .lean_expr b⟩
    | _ => return .none
  | _            => return .none

set_option maxHeartbeats 2000000 in
def step_eta? (e : MetaExpr) : TacticM (Option ((e' : MetaExpr) × (RedEtaMeta e e'))) :=
  match e with
  | DCC[.] (Eql(f_α) env x) => return .some ⟨_, .eql⟩
  | DCC[.] (Λ(α, Id(_b), `(Coup(Id(_c)), x)) y) => do
    let some raw_α ← checkTypeQ α.encode q(Expr) | throwError m!"not an expr: {repr _b}"
    let raw_b := _b.encode
    let raw_c := _c.encode
    let some raw_x ← checkTypeQ x.encode q(_root_.Expr) | throwError m!"not an expr: {repr _c}"
    let some raw_y ← checkTypeQ y.encode q(_root_.Expr) | throwError m!"not an expr: {repr _c}"
    if (← isDefEq raw_b raw_α) ∧ (← isDefEq raw_c raw_α) then
      let e := q(RedEta.curr_quot (α := $raw_α) (x := $raw_x) (y := $raw_y))
      return .some ⟨DCC' `(y, x), .lean_expr e⟩
    else pure .none
  | DCC[.] (Λ(_α, β, x ∘ Fstc(_β₂)) y) => return .some ⟨_, .curr_fst⟩
  | DCC[.] (Λ(_α, β, x ∘' Fstc(_β₂)) y) => return .some ⟨_, .curr_fst'⟩
  | DCC[.] Σ(α, f_β) => do
    match ← f_β.step_eta? with
    | .some ⟨_, h⟩ => return .some ⟨_, .sig' h⟩
    | _ => return .none
  /-| DCC[.] (Σ(α, f_β) env) => do
    match ← (DCC[.] (f_β env)).step_eta? with
    | .some ⟨_, h⟩ => return .some ⟨_, .sig h⟩
    | _ => return .none-/
  | DCC[.] `(β, x) => do
    match ← x.step_eta? with
    | .some ⟨_, h⟩ => return .some ⟨_, .quot h⟩
    | _              => return .none
  | DCC[.] (Π(_f_α, f_β) _env) => do
    match ← (DCC[.] Π(_f_α, f_β)).step_eta? with
    | .some ⟨_, h⟩ => return .some ⟨_, .pi h⟩
    | _ => return .none
  | DCC[.] (Π(_f_α, f_β)) => do
    match f_β with
    /-| DCC[.] `(_β, x) =>
      match ← x.step_eta? with
      | .some ⟨_, h⟩ => return .some ⟨_, .pi_quot h⟩
      | _ => return .none-/
    | x =>
      match ← x.step_eta? with
      | .some ⟨_, h⟩ => return .some ⟨_, .pi' h⟩
      | _ => return .none
  | DCC[.] Λ(_α, _β, x) => do
    match ← x.step_eta? with
    | .some ⟨_, h⟩ => return .some ⟨_, .curr h⟩
    | .none => return .none
  | (DCC[.] `(α, x) ∘ Fstc(β)) => return .some ⟨_, .quot_fst⟩
  | (DCC[.] `(α, x) ∘' Fstc(β)) => return .some ⟨_, .quot'_fst⟩
  | (DCC[.] `(α, x) ∘ Sndc(β)) => return .some ⟨_, .quot_snd⟩
  | (DCC[.] `(α, x) ∘' Sndc(β)) => return .some ⟨_, .quot'_snd⟩
  | (DCC[.] (`(α, x) ∘ Fstc(β)) ∘ z) => return .some ⟨_, .quot_fst'⟩
  | (DCC[.] (`(α, x) ∘' Fstc(β)) ∘' z) => return .some ⟨_, .quot'_fst'⟩
  | (DCC[.] (`(α, x) ∘ Sndc(β)) ∘ z) => return .some ⟨_, .quot_snd'⟩
  | (DCC[.] (`(α, x) ∘' Sndc(β)) ∘' z) => return .some ⟨_, .quot'_snd'⟩
  | .lean_expr e => do
    match ← lookup_local_hyp ``Expr.RedEta e with
    | .some (a, b) => return .some ⟨a, .lean_expr b⟩
    | _ => return .none
  | _ => return .none

open Lean Elab Tactic

inductive Mode where
  | norm       : Mode
  | trans      : Mode
  | refl_trans : Mode

inductive Scheme where
  | aff : Scheme
  | eta : Scheme

inductive Cmd where
  | step   : Scheme → Cmd
  | reduce : Scheme → Mode → Cmd

def Scheme.tm_rel (cmd : Scheme) : Q(_root_.Expr → _root_.Expr → Prop) :=
  match cmd with
  | .aff => q(Expr.RedAff)
  | .eta => q(Expr.RedEta)

def Mode.tm_rel (mode : Mode) :
  Q((r : _root_.Expr → _root_.Expr → Prop) → _root_.Expr → _root_.Expr → Prop) :=
  match mode with
  | .refl_trans | .norm => q(Relation.ReflTransGen)
  | .trans => q(Relation.ReflTransGen)

def Scheme.rel (scheme : Scheme) : MetaExpr → MetaExpr → Type :=
  match scheme with
  | .aff => MetaExpr.RedAffMeta
  | .eta => MetaExpr.RedEtaMeta

def Cmd.tm_rel (cmd : Cmd) : Q(_root_.Expr → _root_.Expr → Prop) :=
  match cmd with
  | .step scheme => scheme.tm_rel
  | .reduce scheme mode =>
    let rel   := scheme.tm_rel
    let rel_m := mode.tm_rel
    q($rel_m $rel)

def Scheme.runner (scheme : Scheme) (A : MetaExpr) : TacticM (Option ((A' B' : Q(_root_.Expr))
  × (B : MetaExpr) × (PLift (A' = A.encode ∧ B' = B.encode))
  × Q($(scheme.tm_rel) $A' $B'))) := do
  let A' := A.encode
  match scheme with
  | .aff =>
    match ← step? A with
    | .some ⟨B, h⟩ =>
      let B' := B.encode
      let h' : Q(_root_.Expr.RedAff $A' $B') := h.encode
      return .some ⟨A', B', B, ⟨⟨rfl, rfl⟩⟩, h'⟩
    | _ => pure .none
  | .eta =>
    match ← step_eta? A with
    | .some ⟨B, h⟩ =>
      let B' := B.encode
      let h' : Q(_root_.Expr.RedEta $A' $B') := h.encode
      return .some ⟨A', B', B, ⟨⟨rfl, rfl⟩⟩, h'⟩
    | _ => pure .none

partial def Cmd.runner (cmd : Cmd) (A : MetaExpr) : TacticM (Option ((A' B' : Q(_root_.Expr))
  × (B : MetaExpr) × (PLift (A' = A.encode ∧ B' = B.encode))
  × Q($(cmd.tm_rel) $A' $B'))) :=
  match cmd with
  | .step scheme => scheme.runner A
  | .reduce scheme .refl_trans =>
    let single := scheme.runner
    let rec runner' (A : MetaExpr) : TacticM ((A' B' : Q(_root_.Expr))
      × (B : MetaExpr) × (PLift (A' = A.encode ∧ B' = B.encode))
      × Q(Relation.ReflTransGen $(scheme.tm_rel) $A' $B')) := do
      let A' := A.encode
      match ← single A with
      | .some ⟨A', B', B, ⟨heq₁, heq₂⟩, hr⟩ =>
        let ⟨B', C', C, ⟨heq₃, heq₄⟩, hr₂⟩ ← runner' B
        return ⟨A', C', C, ⟨⟨by simp_all, by simp_all⟩⟩, by
          cases heq₁; cases heq₂; cases heq₃; cases heq₄
          exact q(Relation.ReflTransGen.trans (.single $hr) $hr₂)⟩
      | _ => return ⟨A', A', A, ⟨⟨rfl, rfl⟩⟩, q(.refl)⟩
    runner' A >>= (pure ∘ Option.some)
  | .reduce scheme .trans =>
    let single := scheme.runner
    let rec runner'' (A : MetaExpr) : TacticM (Option ((A' B' : Q(_root_.Expr))
      × (B : MetaExpr) × (PLift (A' = A.encode ∧ B' = B.encode))
      × Q(Relation.TransGen $(scheme.tm_rel) $A' $B'))) := do
      let A' := A.encode
      match ← single A with
      | .some ⟨A', B', B, ⟨⟨heq₁, heq₂⟩⟩, hr₁⟩ =>
        match ← runner'' B with
        | .some ⟨B', C', C, ⟨⟨heq₃, heq₄⟩⟩, hr₂⟩ =>
          return .some ⟨A', C', C, ⟨⟨by simp_all, by simp_all⟩⟩, (by
            cases heq₁; cases heq₂; cases heq₃; cases heq₄
            exact q(Relation.TransGen.trans (.single $hr₁) $hr₂))⟩
        | .none => return .some ⟨A', B', B, ⟨⟨heq₁, heq₂⟩⟩, q(Relation.TransGen.single $hr₁)⟩
      | _ => return .none
    runner'' A
  | _ => return .none

declare_syntax_cat reduce_cmd

syntax "step"   reduce_cmd* : reduce_cmd
syntax "reduce" reduce_cmd* : reduce_cmd
syntax "!"                  : reduce_cmd
syntax "*"                  : reduce_cmd
syntax "+"                  : reduce_cmd
syntax "aff"                : reduce_cmd
syntax "eta"                : reduce_cmd

def parse_mode (stx : TSyntax `reduce_cmd) : MacroM Mode :=
  match stx with
  | `(reduce_cmd| !) => pure .norm
  | `(reduce_cmd| *) => pure .refl_trans
  | `(reduce_cmd| +) => pure .trans
  | e => Macro.throwErrorAt stx s!"unsupported DCC mode: {e}"

def parse_scheme (stx : TSyntax `reduce_cmd) : MacroM Scheme :=
  match stx with
  | `(reduce_cmd| aff) => pure .aff
  | `(reduce_cmd| eta) => pure .eta
  | e => Macro.throwErrorAt stx s!"unsupported DCC scheme: {e}"

partial def parse_cmd (stx : TSyntax `reduce_cmd) : MacroM Cmd :=
  match stx with
  | `(reduce_cmd| step $scheme:reduce_cmd) => do
    let scheme ← parse_scheme scheme
    pure (.step scheme)
  | `(reduce_cmd| reduce $mode:reduce_cmd $scheme:reduce_cmd) => do
    let mode ← parse_mode mode
    let scheme ← parse_scheme scheme
    pure (.reduce scheme mode)
  | e => Macro.throwErrorAt stx s!"unsupported DCC command: {e}"

def find_decl_expr (hyp : TSyntax `ident) (lctx : LocalContext) : TacticM (LocalDecl × Lean.Expr) := do
  let nm  := hyp.getId
  let some decl    ← lctx.findDeclM? (fun decl =>
  if decl.userName.eraseMacroScopes == nm.eraseMacroScopes then
    match decl.type with
    | .app (.app _ _) _ => return Option.some decl
    | e => throwError m!"not a relation on Expr: {e}"
  else return Option.none) | throwError m!"couldn't find hypothesis: {hyp}"
  let some raw_expr ← lctx.findDeclM? (fun decl =>
    if decl.userName == nm then
      match decl.type with
      | .app (.app _ a) _ => return Option.some a
      | e => throwError m!"not a relation on Expr: {e}"
    else return Option.none) | throwError m!"couldn't find the expr: {hyp}"
  return (decl, raw_expr)

def reduce_goal (cmd : TSyntax `reduce_cmd) (hyp : TSyntax `ident) (g : MVarId) : TacticM (MVarId) := do
  g.withContext do
    let lctx ← getLCtx
    let (decl, A_raw) ← find_decl_expr hyp lctx
    let A ← MetaExpr.decode A_raw
    let cmd ← liftMacroM <| parse_cmd cmd
    let runner := cmd.runner
    match ← runner A with
    | .some ⟨A', B', _B, ⟨_heq₁, _heq₂⟩, raw_proof⟩ =>
      let ty : Q(Prop) := q($(cmd.tm_rel) $A' $B')
      let g' ← g.assertAfter decl.fvarId (← Meta.getUnusedUserName hyp.getId) ty raw_proof
      return g'.mvarId
    | .none => logWarning "dcc made no progress" *> return g

partial def exprSize : Lean.Expr → Nat
  | .app f a        => 1 + exprSize f + exprSize a
  | .lam _ t b _    => 1 + exprSize t + exprSize b
  | .forallE _ t b _ => 1 + exprSize t + exprSize b
  | .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
  | .mdata _ e      => 1 + exprSize e
  | .proj _ _ e     => 1 + exprSize e
  | _               => 1

def any_relevant_hyp (g : MVarId) : TacticM (Option (TSyntax `ident)) := do
  g.withContext do
    let lctx ← getLCtx
    lctx.findDeclM? (fun decl => do
      match decl.type with
      | .app (.app (.const _ _) A) B =>
        if exprSize B < exprSize A then
          return .some (mkIdent decl.userName)
        else
          return .none
      | _ => return .none)

def my_sort [Monad m] [Ord β] (key : α → m β) (l : List α) : m (List α) := do
  let keyed ← l.mapM (fun a => do return (← key a, a))
  return (keyed.mergeSort (fun x y => compare x.1 y.1 |>.isLE)).map (·.2)

open Qq in
def split_hyps (g : MVarId) : TacticM (Array MVarId) := do
  g.withContext do
    let lctx ← getLCtx
    let get_components (decl : LocalDecl) : TacticM (Option (Q(_root_.Expr) × Q(_root_.Expr))) := do
      match ← Qq.checkTypeQ decl.type q(Prop) with
      | .some ty =>
        match ty with
        | ~q(Relation.ReflTransGen _root_.Expr.RedAff $A $B) =>
          return .some (A, B)
        | ~q(Relation.TransGen _root_.Expr.RedAff $A $B) =>
          return .some (A, B)
        | ~q(Relation.ReflTransGen _root_.Expr.RedEta $A $B) =>
          return .some (A, B)
        | ~q(Relation.TransGen _root_.Expr.RedEta $A $B) =>
          return .some (A, B)
        | ~q(_root_.Expr.RedAffReflTrans $A $B) =>
          return .some (A, B)
        | ~q(_root_.Expr.RedAffTrans $A $B) =>
          return .some (A, B)
        | _ => return .none
      | _ => return .none
    let get_left_size (decl : LocalDecl) : TacticM ℕ := do
      match ← get_components decl with
      | .some (a, _b) => return exprSize a
      | .none => pure 0
    let get_right_size (decl : LocalDecl) : TacticM ℕ := do
      match ← get_components decl with
      | .some (_a, b) => return exprSize b
      | .none => pure 0
    let left_decls ← my_sort (l := (lctx.decls.toList.filterMap _root_.id)) get_left_size
    let right_decls ← my_sort (l := (lctx.decls.toList.filterMap _root_.id)) get_right_size
    let split (decl : LocalDecl) (nm : Lean.Name) : TacticM (Array MVarId) := do
      let c_head_expr := mkFVar decl.fvarId
      let proof ← Lean.Meta.mkAppM nm #[c_head_expr]
      let ty    ← Lean.Meta.inferType proof
      let nm    ← Meta.getUnusedUserName decl.userName
      let (fvid', g') ← (← g.assert nm ty proof).intro1
      let subgoals ← g'.cases fvid'
      return subgoals.map (·.mvarId)
    -- go with left candidates
    let x : Option (Array MVarId) ←
      if (← left_decls.head?.mapM get_left_size).getD 0 > (← right_decls.head?.mapM get_right_size).getD 0 then
        right_decls.firstM (fun (decl : LocalDecl) => do
          let idt := mkIdent decl.userName
          match ← Qq.checkTypeQ decl.type q(Prop) with
          | Option.some ty =>
            match ty with
            | ~q(Relation.ReflTransGen $r $A $B) =>
              if exprSize B < exprSize A then
                return Option.some (← split decl ``Relation.ReflTransGen.cases_head)
              else return Option.none
            | ~q(Relation.TransGen $r $A $B) =>
              if exprSize B < exprSize A then
                let _ ← evalTactic (← liftMacroM <| `(tactic|
                  cases $idt:ident using Relation.TransGen.head_induction_on with
                  | single h =>
                    ?reflCase
                  | head h ih =>
                    ?headCase))
                let goals  ← getGoals
                let some reflG  ← goals.findM? (fun g => return (← g.getTag) == `reflCase) | throwError m!"cannot find case: refl"
                let .some headG  ← goals.findM? (fun g => return (← g.getTag) == `headCase) | throwError m!"cannot find case: head"
                return .some #[reflG, headG]
              else return Option.none
            | _ => return Option.none
          | .none => return .none)
      else
        right_decls.firstM (fun (decl : LocalDecl) => do
          let idt := mkIdent decl.userName
          match ← Qq.checkTypeQ decl.type q(Prop) with
          | Option.some ty =>
            match ty with
            | ~q(Relation.ReflTransGen $r $A $B) =>
              if exprSize A < exprSize B then
                let g   ← getMainGoal
                return Option.some ((← g.cases decl.fvarId).map (·.mvarId))
              else return Option.none
            | ~q(Relation.TransGen $r $A $B) =>
              if exprSize A < exprSize B then
                let g   ← getMainGoal
                return Option.some (← g.cases decl.fvarId)
              else return Option.none
            | _ => return Option.none
          | _ => return Option.none)
    match x with
    | .some gs =>
      pure gs
    | .none => pure #[g]

elab "dcc" cmd:reduce_cmd "from" hyp:ident : tactic => do
  let g  ← getMainGoal
  g.withContext do
    -- Assume some relation r A B
    let nm_idt  := mkIdent hyp.getId
    let gs ← runTactic' g (← liftMacroM <|`(tactic| dcc_simp at $nm_idt:term))
    replaceMainGoal gs
    let g ← getMainGoal
    g.withContext do
      let lctx ← getLCtx
      match ← (liftMacroM (parse_cmd cmd)) with
      | .reduce _ .norm =>
        let (decl, _) ← find_decl_expr hyp lctx
        let c_head_expr := mkFVar decl.fvarId
        let proof ← Lean.Meta.mkAppM ``Relation.ReflTransGen.cases_head #[c_head_expr]
        let ty    ← Lean.Meta.inferType proof
        let nm    ← Meta.getUnusedUserName hyp.getId
        let (new_fv, g') ← (← g.assert nm ty proof).intro1
        let subgoals ← (← (g'.cases new_fv)).mapM (fun sg => do
          let some relevant_hyp ← any_relevant_hyp sg.mvarId | return sg.mvarId
          reduce_goal cmd relevant_hyp sg.mvarId)
        replaceMainGoal subgoals.toList
      | _ => replaceMainGoal [← reduce_goal cmd hyp g]

namespace _test

open Expr in
example (h_absurd : RedAff (DCC (Id(Sort 1) α)) (DCC Sort 1)) : RedAff (DCC Sort 0) (DCC Sort 1) := by
  dcc step aff from h_absurd
  dcc reduce* aff from h_absurd
  sorry

end _test

end MetaExpr

/-
Producing a proof of IsNorm is not possible since we have holes.
We're chilling I think.
-/
