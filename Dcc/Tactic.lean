import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Red
import Dcc.Eta.Red
import Lean

open Lean (ToExpr)

gen_ast as MetaExpr
  with Lean.Expr *
  deriving BEq, Repr, ToExpr
gen_dsl "DCC'" for MetaExpr

namespace GenAst

open GenAst Lean Elab Command Meta
open Lean Parser Command

open Lean Macro Parser.Command
open Lean (Parser.Command.derivingClass)
open Lean.Parser.Term


open GenAst Lean Elab Command Meta
open Lean Parser Command

open Lean Macro Parser.Command
open Lean (Parser.Command.derivingClass)
open Lean.Parser.Term

abbrev pretty_stx := Lean.PrettyPrinter.delab

def n_explicit_args (cval : ConstructorVal) : MetaM ℕ := do
  forallBoundedTelescope cval.type (some (cval.numParams + cval.numFields)) fun xs _ => do
    let fields := xs.extract cval.numParams xs.size
    let explicitFields ← fields.filterM fun fvar => do
      return (← fvar.fvarId!.getDecl).binderInfo.isExplicit
    pure explicitFields.toList.length

def get_def_flags (nm : Lean.Name) : TermElabM (Flag × Array AstField) := do
  let env ← getEnv
  let some maybe_info ← (pure (env.find? nm)) | throwError m!"couldn't find the declaration: {nm}"
  let info ← match maybe_info with
    | .inductInfo info => pure info
    | _ => throwError m!"this is not an inductive: {nm}"

  let nm'    := Flag.as (mkIdent nm)
  let index  := Flag.index (← liftM <| pretty_stx info.type)
  let fields : List AstField ← info.ctors.mapM (fun cname => do
    let cinfo ← match (← getConstInfo cname) with
      | .ctorInfo info => pure info
      | _ => throwError m!"this is not a constructor: {cname}"
    let constr_nm := cinfo.name.eraseMacroScopes.lastComponentAsString
    let arity ← n_explicit_args cinfo
    let other_params : Array (TSyntax `ident) := ← forallTelescope info.type (fun hyps _ =>
      return hyps.filterMap (fun hyp =>
        if hyp != Lean.Expr.const nm [] then
          match hyp with
          | .const nm _ =>
            .some <| mkIdent nm
          | _ => .none
        else .none)
      )
      return { nm := constr_nm, arity := arity, other_params := other_params })
    return ((nm' ++ index), ⟨fields⟩)

end GenAst
