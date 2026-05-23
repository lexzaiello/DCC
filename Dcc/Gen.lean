import Dcc.Ast
import Lean
import Lean.Elab.Command

namespace GenAst

open GenAst Lean Elab Command Meta
open Lean Parser Command

open Lean Macro Parser.Command
open Lean (Parser.Command.derivingClass)
open Lean.Parser.Term

abbrev pretty_stx := Lean.PrettyPrinter.delab

def get_def_flags (nm : Lean.Name) : TermElabM (Flag × Array AstField) := do
  let info ← match (← getConstInfo nm) with
    | .inductInfo info => pure info
    | _ => throwError m!"this is not an inductive: {nm}"

  let nm'    := Flag.as (mkIdent nm.eraseMacroScopes)
  let index  := Flag.index (← liftM <| pretty_stx info.type)
  let fields : List AstField ← info.ctors.mapM (fun cname => do
    let cinfo ← match (← getConstInfo cname) with
      | .ctorInfo info => pure info
      | _ => throwError m!"this is not a constructor: {cname}"
    let constr_nm := cinfo.name.eraseMacroScopes.lastComponentAsString
    let arity := ← forallTelescope info.type (fun (hyps : Array Lean.Expr) _ => do
      return (List.length ∘ Array.toList) <| hyps.filterMap (fun hyp =>
        if hyp == Lean.Expr.const nm [] then
          .some hyp
        else .none)
      )
    let other_params : Array (TSyntax `ident) := ← forallTelescope info.type (fun hyps _ =>
      return hyps.filterMap (fun hyp =>
        if hyp != Lean.Expr.const nm [] then
          match hyp with
          | .const nm _ =>
            .some <| mkIdent nm.eraseMacroScopes
          | _ => .none
        else .none)
      )
      return { nm := constr_nm, arity := arity, other_params := other_params })
    return ((nm' ++ index), ⟨fields⟩)

/-
TODO: Use this to make elab encoders for RedAff and RedEta. need this to reflect back into term
/ goals.
-/
