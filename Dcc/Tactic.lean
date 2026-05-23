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
