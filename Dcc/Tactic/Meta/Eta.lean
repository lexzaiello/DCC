import Dcc.Tactic.Meta.Ast
import Dcc.Aff.Red
import Dcc.Relation
import Lean
import Qq
import Qq.MetaM

namespace MetaExpr

inductive RedEtaMeta : MetaExpr → MetaExpr → Type
  --| curr       : RedEtaMeta x x' → RedEtaMeta (DCC[.] (Λ(α, β, x))) (DCC[.] (Λ(α, β, x')))
  | curr_quot  : RedEtaMeta (DCC[.] (Λ(α, Id(α), `(Coup(Id(α)), x)) y)) (DCC[.] `(y, x))
  | curr_fst   : RedEtaMeta (DCC[.] (Λ(α, β, x ∘ Fst(β₂)) y)) (DCC[.] `((β y), (x y)))
  | curr_fst'  : RedEtaMeta (DCC[.] (Λ(α, β, x ∘' Fst(β₂)) y)) (DCC[.] `((β y), (x y)))
  | pi         : RedEtaMeta (DCC[.] Π(α, β)) p' → RedEtaMeta (DCC[.] (Π(α, β) env)) (DCC[.] (p' env))
  --| pi_quot    : RedEtaMeta x x' → RedEtaMeta (DCC[.] (Π(α, `(β, x)))) (DCC[.] (Π(α, `(β, x'))))
  | pi'        : RedEtaMeta β β' → RedEtaMeta (DCC[.] (Π(α, β))) (DCC[.] (Π(α, β')))
  --| quot       : RedEtaMeta x x' → RedEtaMeta (DCC[.] `(β, x)) (DCC[.] `(β, x'))
  --| sig        : RedEtaMeta (DCC[.] (β env)) β' → RedEtaMeta (DCC[.] (Σ(α, β) env)) (DCC[.] Coup(β'))
  | sig'       : RedEtaMeta β β' → RedEtaMeta (DCC[.] (Σ(α, β))) (DCC[.] Σ(α, β'))
  | quot_fst   : RedEtaMeta (DCC[.] `(α, x) ∘ Fst(β)) (DCC[.] `(Coup(β), x))
  | quot'_fst  : RedEtaMeta (DCC[.] `(α, x) ∘' Fst(β)) (DCC[.] `(Coup(β), x))
  | quot_snd   : RedEtaMeta (DCC[.] `(α, x) ∘ Snd(β)) (DCC[.] `(Coup(β), x))
  | quot'_snd  : RedEtaMeta (DCC[.] `(α, x) ∘' Snd(β)) (DCC[.] `(Coup(β), x))
  | quot_fst'  : RedEtaMeta (DCC[.] (`(α, x) ∘ Fst(β)) ∘ z) (DCC[.] `(Coup(β), x) ∘ z)
  | quot'_fst' : RedEtaMeta (DCC[.] (`(α, x) ∘' Fst(β)) ∘' z) (DCC[.] `(Coup(β), x) ∘' z)
  | quot_snd'  : RedEtaMeta (DCC[.] (`(α, x) ∘ Snd(β)) ∘ z) (DCC[.] `(Coup(β), x) ∘ z)
  | quot'_snd' : RedEtaMeta (DCC[.] (`(α, x) ∘' Snd(β)) ∘' z) (DCC[.] `(Coup(β), x) ∘' z)
  | eql        : RedEtaMeta (DCC[.] (Eql(f_α) env x)) (DCC[.] (x = x))
  | lean_expr  : Lean.Expr → RedEtaMeta a b

end MetaExpr
