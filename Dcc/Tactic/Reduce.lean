import Mathlib.Logic.Relation
import Dcc.Ast
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
  | _ => return .none

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
  | DCC[.] (Σ(α, f_β) env) => do
    match ← (DCC[.] (f_β env)).step_eta? with
    | .some ⟨_, h⟩ => return .some ⟨_, .sig h⟩
    | _ => return .none
  | DCC[.] (Π(_f_α, f_β) _env) => do
    match ← (DCC[.] Π(_f_α, f_β)).step_eta? with
    | .some ⟨_, h⟩ => return .some ⟨_, .pi h⟩
    | _ => return .none
  | DCC[.] (Π(_f_α, f_β)) => do
    match f_β with
    | DCC[.] `(_β, x) =>
      match ← x.step_eta? with
      | .some ⟨_, h⟩ => return .some ⟨_, .pi_quot h⟩
      | _ => return .none
    | x =>
      match ← x.step_eta? with
      | .some ⟨_, h⟩ => return .some ⟨_, .pi' h⟩
      | _ => return .none
  | (DCC[.] (Id(_α) ∘ _f)) => return .some ⟨_, .idl⟩
  | (DCC[.] (Id(_α) ∘' _f)) => return .some ⟨_, .idl'⟩
  | DCC[.] Λ(_α, _β, x) => do
    match ← x.step_eta? with
    | .some ⟨_, h⟩ => return .some ⟨_, .curr h⟩
    | .none => return .none
  | (DCC[.] `(α, x) ∘ Fstc(β)) => return .some ⟨_, .quot_fst⟩
  | (DCC[.] `(α, x) ∘' Fstc(β)) => return .some ⟨_, .quot'_fst⟩
  | (DCC[.] `(α, x) ∘ Sndc(β)) => return .some ⟨_, .quot_snd⟩
  | (DCC[.] `(α, x) ∘' Sndc(β)) => return .some ⟨_, .quot'_snd⟩
  | DCC[.] (Π(f_α, f_β) ∘ x) => return .some ⟨_, .pi_comp⟩
  | DCC[.] (Π(f_α, f_β) ∘' x) => return .some ⟨_, .pi'_comp⟩
  | (DCC[.] (`(α, x) ∘ Fstc(β)) ∘ z) => return .some ⟨_, .quot_fst'⟩
  | (DCC[.] (`(α, x) ∘' Fstc(β)) ∘' z) => return .some ⟨_, .quot'_fst'⟩
  | (DCC[.] (`(α, x) ∘ Sndc(β)) ∘ z) => return .some ⟨_, .quot_snd'⟩
  | (DCC[.] (`(α, x) ∘' Sndc(β)) ∘' z) => return .some ⟨_, .quot'_snd'⟩
  | _ => return .none

partial def reduce_aff (e : MetaExpr) : TacticM
  (MetaExpr × Lean.Expr) := do
  match ← step? e with
  | .some ⟨e', h⟩ =>
    let h_raw := h.encode
    let ⟨e'', h₂_raw⟩ ← reduce_aff e'
    return (e'', Lean.Expr.app (.app
      (.const ``Relation.ReflTransGen.trans [])
      (.app (.const ``Relation.ReflTransGen.single []) h_raw)) h₂_raw)
  | .none => return (e, .const ``Relation.ReflTransGen.refl [])

partial def reduce_eta (e : MetaExpr) : TacticM
  (MetaExpr × Lean.Expr) := do
  match ← step_eta? e with
  | .some ⟨e', h⟩ =>
    let h_raw := h.encode
    let ⟨e'', h₂_raw⟩ ← reduce_eta e'
    return (e'', Lean.Expr.app (.app
      (.const ``Relation.ReflTransGen.trans [])
      (.app (.const ``Relation.ReflTransGen.single []) h_raw)) h₂_raw)
  | .none => return (e, .const ``Relation.ReflTransGen.refl [])

declare_syntax_cat reduce_cmd

syntax "step"   reduce_cmd : reduce_cmd
syntax "reduce" reduce_cmd : reduce_cmd
syntax "aff"               : reduce_cmd
syntax "eta"               : reduce_cmd

open Lean Elab Tactic
elab "dcc" cmd:reduce_cmd "from" hyp:ident : tactic => do
  let g  ← getMainGoal
  -- Assume some relation r A B
  let lctx ← getLCtx
  let nm  := hyp.getId
  let nm' := Name.str .anonymous s!"{hyp.getId}_'"
  let some decl    ← lctx.findDeclM? (fun decl =>
    if decl.userName == nm then
      match decl.type with
      | .app (.app _ _) _ => return Option.some decl
      | e => throwError m!"not a relation on Expr: {e}"
    else return Option.none) | throwError m!"couldn't find hypothesis: {hyp}"
  let raw_expr ← lctx.findDeclM? (fun decl =>
    if decl.userName == nm then
      match decl.type with
      | .app (.app _ a) _ => return Option.some a
      | e => throwError m!"not a relation on Expr: {e}"
    else return Option.none)
  match raw_expr with
  | .some A =>
    let dec ← MetaExpr.decode A
    match cmd with
    | `(reduce_cmd| step $kind:reduce_cmd) =>
      let maybe_ty_proof ← match kind with
      | `(reduce_cmd| aff) =>
        match ← dec.step? with
        | .some ⟨actual_B, actual_proof⟩ =>
          let B            := actual_B.encode
          let ty           := Lean.Expr.app (.app (.const ``Expr.RedAff []) A) B
          let raw_proof    := actual_proof.encode
          pure (Option.some (ty, raw_proof))
        | .none => pure Option.none
      | `(reduce_cmd| eta) =>
        match ← dec.step_eta? with
        | .some ⟨actual_B, actual_proof⟩ =>
          let B            := actual_B.encode
          let ty           := Lean.Expr.app (.app (.const ``Expr.RedAff []) A) B
          let raw_proof    := actual_proof.encode
          pure (Option.some (ty, raw_proof))
        | .none => pure .none
      | _ => pure .none
      match maybe_ty_proof with
      | .some (ty, raw_proof) =>
        let g' ← g.assertAfter decl.fvarId nm' ty raw_proof
        replaceMainGoal [g'.mvarId]
      | _ => pure ()
    | _ => pure ()
  | _ => pure ()

namespace _test

open Expr in
example (h_absurd : RedAff (DCC (Id(Sort 1) α)) (DCC Sort 1)) : RedAff (DCC Sort 0) (DCC Sort 1) := by
  dcc step aff from h_absurd
  sorry

end _test

end MetaExpr
