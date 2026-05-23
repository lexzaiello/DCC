import Dcc.Tactic
import Dcc.Aff.Red
import Dcc.Relation
import Lean

open Lean Elab Term Tactic

namespace MetaExpr

mirror from Expr.RedAff
  as RedAffMeta
  with Lean.Expr
  into MetaExpr → MetaExpr → Type

/-
Need encoder for mirrored. This isn't too bad because
it is generated now with the right names.
-/


/-def find_hyp (nm : Name) (for_exp :  : TacticM (Option Lean.Expr) := do
  let lctx ← getLCtx
  let decl ← lctx.findDecl? (fun decl =>
    match decl.type with
    | .app (.app (.const ``RedAffMeta [])
    sorry)
  sorry-/

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
  | .lean_expr lean_e => return .none -- TODO
  | _ => return .none

end MetaExpr

