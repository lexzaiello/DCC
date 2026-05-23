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

namespace MetaExpr

mirror from Expr.RedAff
  as RedAffMeta
  with Lean.Expr
  into MetaExpr → MetaExpr → Type
mirror from Expr.RedEta
  with Lean.Expr
  as RedEtaMeta
  into MetaExpr → MetaExpr → Type

#check MetaExpr.lean_expr
-- MetaExpr.ext : Lean.Expr → MetaExpr
#check RedAffMeta
-- RedAffMeta : MetaExpr → MetaExpr → Type
#check RedAffMeta.lean_expr
-- MetaExpr.RedAffMeta.lean_expr {a a¹ : MetaExpr} : Lean.Expr → a.RedAffMeta a¹

#check RedAffMeta.id (α := DCC[MetaExpr] Sort 1) (x := DCC[MetaExpr] Sort 0)

end MetaExpr
