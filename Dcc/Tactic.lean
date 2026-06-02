import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Red
import Dcc.Eta.Red
import Lean

open Lean (ToExpr)

gen_ast as MetaExpr
  with Lean.Expr *
  decode sort with _root_.id
  deriving BEq, Repr, ToExpr, Inhabited
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

namespace MetaExpr

open Std (ToFormat Format format) in
def toFormat (e : MetaExpr) (pretty : Bool := False) : Std.Format :=
  let sepD (l : List Std.Format) (sep : Std.Format := ",") (indent : ℕ := 2) : Std.Format :=
    .nest indent (.fill (.joinSep l (sep ++ .line)))
  let paren (s : Std.Format) : Std.Format :=
    .bracket "(" (.fill s) ")"
  let angle (s : Std.Format) : Std.Format :=
    .bracket "⟨" (.fill s) "⟩"
  let bbracket (s : Std.Format) : Std.Format :=
    .bracket "⟦" (.fill s) "⟧"

  let comb (pre : Std.Format) (points : List Std.Format) (paren : Std.Format → Std.Format := paren) : Std.Format :=
    .group (pre ++ (paren (sepD points (indent := pre.pretty.length))))

  match heq₀ : e with
  | (DCC[.] ⊤)                   => "⊤"
  | (DCC[.] ⊥)                   => "⊥"
  | (DCC[.] ∗)                   => "∗"
  | (DCC[.] `(β, x))             => comb "`" [β.toFormat pretty, x.toFormat pretty]
  | (DCC[.] Id(α))               => comb "Id" [α.toFormat pretty]
  | (DCC[.] Sort m)              => "Sort " ++ (Std.format m)
  | (DCC[.] Fstc(β))             => comb "Fstc" [β.toFormat pretty]
  | (DCC[.] Sndc(β))             => comb "Sndc" [β.toFormat pretty]
  | (DCC[.] Eval(α, β, e))       => comb "Eval" [α.toFormat pretty, β.toFormat pretty, e.toFormat pretty]
  | (DCC[.] Λ(α, β, e))          => comb "Λ" [α.toFormat pretty, β.toFormat pretty, e.toFormat pretty]
  | (DCC[.] Π(α, β))             =>
    comb "Π" [α.toFormat pretty, β.toFormat pretty]
  | (DCC[.] *(α))                => comb "*" [α.toFormat pretty]
  | (DCC[.] &(α))                => comb "&" [α.toFormat pretty]
  | (DCC[.] !(α))                => comb "!" [α.toFormat pretty]
  | (DCC[.] ⟦β⟧⟨a, b⟩)           => comb (paren := angle) (bbracket (sepD [β.toFormat pretty])) [a.toFormat pretty, b.toFormat pretty]
  | (DCC[.] ⟦β⟧(a, b))           =>
    comb (bbracket (sepD [β.toFormat pretty])) [a.toFormat pretty, b.toFormat pretty]
  | (DCC[.] Coup(β))             => comb "Coup" [β.toFormat pretty]
  | (DCC[.] Σ(α, β))             => comb "Σ" [α.toFormat pretty, β.toFormat pretty]
  | (DCC[.] x = y)               => sepD [x.toFormat pretty, y.toFormat pretty] " ="
  | (DCC[.] Eql(f_α))            => comb "Eql" [f_α.toFormat pretty]
  | (DCC[.] refl(f_α))           => comb "refl" [f_α.toFormat pretty]
  | (DCC[.] f ∘ g)               =>
    sepD [f.toFormat pretty, g.toFormat pretty] " ∘"
  | (DCC[.] f ∘' g)               =>
    sepD [f.toFormat pretty, g.toFormat pretty] " ∘'"
  | (DCC[.] (f x))               =>
    if pretty then
      match heq₁ : (DCC[.] (f x)) with
      | DCC[.] (Π(Id(Sort m), Λ(_a, _b, `(_c, β))) α) =>
        have _h : sizeOf α < sizeOf e := by
          rw [heq₁] at heq₀
          rw [heq₀]
          simp [sizeOf, MetaExpr._sizeOf_1]
          grind
        have _h : sizeOf β < sizeOf e := by
          rw [heq₁] at heq₀
          rw [heq₀]
          simp [sizeOf, MetaExpr._sizeOf_1]
          grind
        sepD [(paren (sepD [(α.toFormat pretty), s!"Sort {m}"] " :")), β.toFormat pretty] " →"
      | _ => (paren (f.toFormat pretty ++ (.indentD (x.toFormat pretty))))
    else (paren (f.toFormat pretty ++ (.indentD (x.toFormat pretty))))
  | .lean_expr e => Std.format e
termination_by e

open Std (ToFormat Format format) in
def toFormat' (e : MetaExpr) (pretty : Bool := False) : Lean.MetaM Std.Format := do
  let sepD (l : List Std.Format) (sep : Std.Format := ",") (indent : ℕ := 2) : Std.Format :=
    .nest indent (.fill (.joinSep l (sep ++ .line)))
  let paren (s : Std.Format) : Std.Format :=
    .bracket "(" (.fill s) ")"
  let angle (s : Std.Format) : Std.Format :=
    .bracket "⟨" (.fill s) "⟩"
  let bbracket (s : Std.Format) : Std.Format :=
    .bracket "⟦" (.fill s) "⟧"

  let comb (pre : Std.Format) (points : List Std.Format) (paren : Std.Format → Std.Format := paren) : Std.Format :=
    .group (pre ++ (paren (sepD points (indent := pre.pretty.length))))

  match heq₀ : e with
  | (DCC[.] ⊤)                   => return "⊤"
  | (DCC[.] ⊥)                   => return "⊥"
  | (DCC[.] ∗)                   => return "∗"
  | (DCC[.] `(β, x))             => return comb "`" [← β.toFormat' pretty, ← x.toFormat' pretty]
  | (DCC[.] Id(α))               => return comb "Id" [← α.toFormat' pretty]
  | (DCC[.] Sort m)              => return "Sort " ++ (Std.format m)
  | (DCC[.] Fstc(β))             => return comb "Fstc" [← β.toFormat' pretty]
  | (DCC[.] Sndc(β))             => return comb "Sndc" [← β.toFormat' pretty]
  | (DCC[.] Λ(α, β, e))          => return comb "Λ" [← α.toFormat' pretty, ← β.toFormat' pretty, ← e.toFormat' pretty]
  | (DCC[.] Eval(α, β, e))       => return comb "Eval" [← α.toFormat' pretty, ← β.toFormat' pretty, ← e.toFormat' pretty]
  | (DCC[.] Π(α, β))             =>
    return comb "Π" [← α.toFormat' pretty, ← β.toFormat' pretty]
  | (DCC[.] *(α))                => return comb "*" [← α.toFormat' pretty]
  | (DCC[.] &(α))                => return comb "&" [← α.toFormat' pretty]
  | (DCC[.] !(α))                => return comb "!" [← α.toFormat' pretty]
  | (DCC[.] ⟦β⟧⟨a, b⟩)           =>
    return comb (paren := angle) (bbracket (sepD [β.toFormat pretty])) [a.toFormat pretty, b.toFormat pretty]
  | (DCC[.] ⟦β⟧(a, b))           =>
    return comb (bbracket (sepD [← β.toFormat' pretty])) [← a.toFormat' pretty, ← b.toFormat' pretty]
  | (DCC[.] Coup(β))             => return comb "Coup" [← β.toFormat' pretty]
  | (DCC[.] Σ(α, β))             => return comb "Σ" [← α.toFormat' pretty, ← β.toFormat' pretty]
  | (DCC[.] x = y)               => return sepD [← x.toFormat' pretty, ← y.toFormat' pretty] " ="
  | (DCC[.] Eql(f_α))            => return comb "Eql" [← f_α.toFormat' pretty]
  | (DCC[.] refl(f_α))           => return comb "refl" [← f_α.toFormat' pretty]
  | (DCC[.] f ∘ g)               =>
    return sepD [← f.toFormat' pretty, ← g.toFormat' pretty] " ∘"
  | (DCC[.] f ∘' g)               =>
    return sepD [← f.toFormat' pretty, ← g.toFormat' pretty] " ∘'"
  | (DCC[.] (f x))               =>
    if pretty then
      match heq₁ : (DCC[.] (f x)) with
      | DCC[.] (Π(Id(Sort m), Λ(_a, _b, `(_c, β))) α) =>
        have _h : sizeOf α < sizeOf e := by
          rw [heq₁] at heq₀
          rw [heq₀]
          simp [sizeOf, MetaExpr._sizeOf_1]
          grind
        have _h : sizeOf β < sizeOf e := by
          rw [heq₁] at heq₀
          rw [heq₀]
          simp [sizeOf, MetaExpr._sizeOf_1]
          grind
        return sepD [(paren (sepD [(← α.toFormat' pretty), s!"Sort {m}"] " :")), ← β.toFormat' pretty] " →"
      | _ => return (paren ((← f.toFormat' pretty) ++ (.indentD (← x.toFormat' pretty))))
    else return (paren ((← f.toFormat' pretty) ++ (.indentD ((← x.toFormat' pretty)))))
  | .lean_expr e =>
    return (← Lean.Meta.ppExpr e).pretty
termination_by e

open Std (ToFormat Format format) in
instance instToFormat : Std.ToFormat (MetaExpr) :=
  ⟨MetaExpr.toFormat (pretty := true)⟩
open Std (ToFormat Format format) in
instance instToString : ToString MetaExpr :=
  ⟨toString ∘ toFormat (pretty := true)⟩
open Std (ToFormat Format format) in
instance instRepr : Repr MetaExpr :=
  ⟨Function.const _ ∘ toFormat (pretty := false)⟩

instance instOptToFormat : Std.ToFormat (Option MetaExpr) := ⟨fun me =>
  match me with
  | .none => Std.format me
  | .some e =>
    let l := "(some".length.succ
    .group ("(some " ++ (.fill (.nest l (e.toFormat (pretty := true)))) ++ ")")⟩

end MetaExpr
