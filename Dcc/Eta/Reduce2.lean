import Dcc.Eta.Ast
import Dcc.Aff.Red
import Dcc.Relation
import Dcc.Types

/-
Improvement to code structure in Reduce.lean

- Dedicated inductive MkHole : Expr → Domain → Expr → Prop
  - Generate hole based on domain (no need for seperate TmEtaReduces cases)
- TmEtaReduces does the const check FIRST using MkHole
  - If contains hole arg:
    - only one constructor: mk EtaResult dom (reduce' (f' #(mk_hole ...))).fst (mk_hole ...) f''
      → TmEtaReduces level f f'', same as before
    EtaMap has f' argument, so we can reduce and do is_norm_aff
  - Not contains, same as before
- TmEtaReduces₂: Same changes as TmEtaReduces
- FnEtaReduces
  - pi case
  - arity 1 case
  - arity 2 case
  - refl no TmEtaReduces₂ arity 2 case
- RedEta? same as before
  - (can we make ¬ contains_hole a theorem though??)
- RedEta??
  - Reduce all points first
  - Then RedEta?? points
  - inductive to get points of type terms with zero arity that are not Π(f_α, f_β) env
    - Recurse
    - Make from points
    - Done
  - Π comp case
  - refl case
  - step IsEtaTm e case
- RedEta₂ same as before
-/

namespace GenericExpr

section

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

inductive MkHole : (level : ℕ) → (f : GenericExpr (@EtaConst τ_c)) → (GenericExpr (@EtaConst τ_c)) → Type u
  | coupl : Domain f (DCC? Coup(β)) → MkHole level f (DCC? ⟦β⟧(&(hole(level + 1)), &(hole(level + 2))))
  | tm    : Domain f τ → (ViewCoup τ → False) → MkHole level f (DCC? hole(level + 1))
  | bang  : Domain f (DCC? !(Coup(β))) → MkHole level f (DCC? ⟦β⟧(&(hole(level + 1)), &(hole(level + 2))))

def mk_hole (level : ℕ) (e : GenericExpr (@EtaConst τ_c)) : Option ((hole : GenericExpr (@EtaConst τ_c)) × MkHole level f hole) :=
  match domain? e with
  | .some ⟨h, ⟨

end

end GenericExpr
