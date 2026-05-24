import Dcc.Tactic
import Dcc.Aff.Red
import Dcc.Relation
import Lean

open Lean Elab Term Tactic

namespace MetaExpr

inductive RedAffMeta : MetaExpr → MetaExpr → Type
  | quot      : RedAffMeta (DCC[.] (`(β, x) y)) x
  | id        : RedAffMeta (DCC[.] (Id(α) x)) x
  | fstc      : RedAffMeta (DCC[.] (Fstc(_α) ⟦β⟧(a, b))) a
  | sndc      : RedAffMeta (DCC[.] (Sndc(_α) ⟦β⟧(a, b))) b
  | comp'     : RedAffMeta (DCC[.] ((x ∘' y) z)) (DCC[.] (x (y z)))
  | comp      : RedAffMeta (DCC[.] ((x ∘ y) z)) (DCC[.] (x (y z)))
  | curr      : RedAffMeta (DCC[.] (Λ(α, β, x) y z)) (DCC[.] (x ⟦β⟧(y, z)))
  | sigl      : RedAffMeta x x' → RedAffMeta (DCC[.] ⟦β⟧(x, y)) (DCC[.] ⟦β⟧(x', y))
  | sigr      : RedAffMeta y y' → RedAffMeta (DCC[.] ⟦β⟧(x, y)) (DCC[.] ⟦β⟧(x, y'))
  | sigma     : RedAffMeta (DCC[.] (Σ(f_α, f_β) env)) (DCC[.] (Coup((f_β env))))
  | coup      : RedAffMeta β β' → RedAffMeta (DCC[.] (Coup(β))) (DCC[.] (Coup(β')))
  | congrFun  : RedAffMeta f f' → RedAffMeta (DCC[.] (f x)) (DCC[.] (f' x))
  | congrArg  : RedAffMeta x x' → RedAffMeta (DCC[.] (f x)) (DCC[.] (f x'))
  | lean_expr : Lean.Expr → RedAffMeta a b

end MetaExpr
