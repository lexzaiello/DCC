import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Red
import Dcc.Eta.Red
import Lean

open Lean Elab Term Tactic

gen_ast as MetaExpr
  with Lean.Expr
  deriving BEq, Repr
gen_dsl "DCC'" for MetaExpr

namespace MetaExpr

mirror from Expr.RedAff
  with Lean.Expr
  as RedAffMeta
  into MetaExpr → MetaExpr → Type
mirror from Expr.RedEta
  with Lean.Expr
  as RedEtaMeta
  into MetaExpr → MetaExpr → Type

#check MetaExpr.ext
-- MetaExpr.ext : Lean.Expr → MetaExpr
#check RedAffMeta
-- RedAffMeta : MetaExpr → MetaExpr → Type
#check RedAffMeta.«Lean.Expr0»
-- RedAffMeta.«Lean.Expr0» {a a¹ : MetaExpr} : Lean.Expr → RedAffMeta a a¹

#check RedAffMeta.id (α := DCC[MetaExpr] Sort 1) (x := DCC[MetaExpr] Sort 0)

end MetaExpr
