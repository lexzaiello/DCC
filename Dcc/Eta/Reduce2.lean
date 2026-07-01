import Dcc.Eta.Ast
import Dcc.Aff.Red
import Dcc.Relation
import Dcc.Types
import Mathlib.Logic.Equiv.Defs

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

open Monad in
class EtaRel.{u, v} {τ_c : Type u} [DecidableEq τ_c] (r : GenericExpr τ_c → GenericExpr τ_c → Sort v)
  (m : Type (max u v) → Type (max u v) := Option) [_hM : AlternativeMonad m] where
  is_norm_aff   : r A B → IsNorm RedAff B
  run           : ∀ (A : GenericExpr τ_c), m ((B : GenericExpr τ_c) × (PULift.{v + 1, v} (r A B)))
  complete      : ∀ (h : r A B), run A = (pure ⟨B, ⟨h⟩⟩)
  none          : ∀ (_h : run A = failure) (_hr : r A B), False
  sound         : (run A = pure ⟨B, ⟨h⟩⟩) → r A B := fun (_heq : run A = pure ⟨B, ⟨h⟩⟩) => h

attribute [grind ., grind! .] EtaRel.complete
attribute [grind] EtaRel.run
attribute [grind] EtaRel.sound

open EtaRel in
open Monad in
class EtaRelProp {τ_c : Type u} [DecidableEq τ_c] (r : GenericExpr τ_c → GenericExpr τ_c → Prop)
  (m : Type u → Type u := Option) [_hM : AlternativeMonad m] : Type max u u extends (EtaRel r m) where
  none_complete : (¬ ∃ B, r A B)  → run A = failure

attribute [grind =] EtaRelProp.none_complete

open Monad in
class OptionEtaRel.{u, v} {τ_c : Type u} [DecidableEq τ_c] (r : GenericExpr τ_c → GenericExpr τ_c → Prop)
  : Type max u v extends (EtaRelProp r Option) where
  none          : ∀ {A B : GenericExpr τ_c} (_h : run A = failure) (_hr : r A B), False := fun heq hr => by
    simp_all [complete hr, failure, pure]
  none_complete := fun hn => by
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, ⟨h⟩⟩
    grind

open OptionEtaRel in
open Monad in
@[grind =]
theorem OptionEtaRel.none_complete'.{u} {τ_c : Type u} [DecidableEq τ_c]
  (r : GenericExpr τ_c → GenericExpr τ_c → Prop) [hR : OptionEtaRel r] {A : GenericExpr τ_c} : (¬ ∃ B, r A B) → hR.run A = .none := hR.none_complete

end GenericExpr
