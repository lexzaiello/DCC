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

end MetaExpr

