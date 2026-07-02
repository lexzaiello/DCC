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

@[grind]
def mk_hole (level : ℕ) (e : GenericExpr (@EtaConst τ_c)) : Option ((hole : GenericExpr (@EtaConst τ_c)) × (PULift.{u + 2, u + 1} (MkHole level e hole))) :=
  match domain? e with
  | .some ⟨τ, ⟨h⟩⟩ =>
    match heq : τ.view_coup? with
    | .some .coup => .some ⟨_, ⟨.coupl h⟩⟩
    | .some .bang => .some ⟨_, ⟨.bang h⟩⟩
    | .none => .some ⟨_, ⟨.tm h (fun h => by
      have h := h.complete
      grind)⟩⟩
  | .none => .none

@[dcc_rel, aesop safe apply (rule_sets := [DccRel])]
theorem Domain.eq {e τ : GenericExpr τ_c} (h₁ h₂ : Domain e τ) : h₁ = h₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all

open EtaRel in
@[dcc_rel, aesop safe apply (rule_sets := [DccRel])]
theorem MkHole.eq {f f' : GenericExpr (@EtaConst τ_c)} (h₁ h₂ : MkHole level f f') : h₁ = h₂ := by
  induction h₁
  case bang | coupl =>
    cases h₂
    rename_i hr₁ hr₂
    · have heq₁ := Domain.instEtaRel.complete hr₁
      have heq₂ := Domain.instEtaRel.complete hr₂
      grind
    · rename_i hr₁ hr₂
      have heq₁ := Domain.instEtaRel.complete hr₁
      have heq₂ := Domain.instEtaRel.complete hr₂
      have h := hr₁.deterministic hr₂
      grind
  · cases h₂
    rename_i h_dom₁ hn₁ _ hn₂ h_dom₂
    have heq₁ := Domain.instEtaRel.complete h_dom₁
    have heq₂ := Domain.instEtaRel.complete h_dom₂
    have h := h_dom₁.deterministic h_dom₂
    grind

theorem MkHole.complete {A B : GenericExpr (@EtaConst τ_c)} (h : MkHole level A B) : mk_hole level A = .some ⟨B, ⟨h⟩⟩ := by
  unfold mk_hole
  split
  · rename_i h_dom₁ h_dom₂
    split
    case h_1 =>
      simp_all
      cases h
      · dcc_aesop
      · simp_all [dcc_rel]
        rename_i h_dom₁ h_dom₂ _ hn h_dom₃
        cases OptionEtaRel.unique h_dom₃ h_dom₁
        try (exact hn (by constructor))
      · simp_all
        rename_i h_dom₁ h_dom₂ heq h_dom₃
        cases OptionEtaRel.unique h_dom₃ h_dom₁
    case h_2 h_dom₁ h_dom₂ heq₁ heq₂ =>
      simp_all [view_coup?]
      have h := h_dom₁.complete
      rename_i hr _ _ _
      cases hr
      · dcc_aesop
      · simp_all [dcc_rel]
        rename_i h_dom₁ h_dom₂ _ hn h_dom₃
        cases OptionEtaRel.unique h_dom₃ h_dom₁
        try (exact hn (by constructor))
      · simp_all
        rename_i h_dom₄
        cases OptionEtaRel.unique h_dom₁ h_dom₄
        simp_all
        dcc_aesop
    case h_3 =>
      rename_i hr₂ _ _ h_dom₃ heq₁ heq₂
      have heq := h.eq h_dom₃
      cases hr₂
      · rename_i h_dom'
        have h := OptionEtaRel.unique h_dom₃ h_dom'
        cases h
        grind
      · rename_i h_dom'
        have h := OptionEtaRel.unique h_dom₃ h_dom'
        cases h
        simp_all
        exact h_dom₃.eq h_dom'
      · rename_i h_dom'
        have h := OptionEtaRel.unique h_dom₃ h_dom'
        cases h
        grind
  case h_2 hn =>
    cases h <;> (
      rename_i h_dom
      have h := h_dom.complete
      simp_all)

instance : EtaRel (τ_c := (@EtaConst τ_c)) (MkHole level) where
  is_norm_aff := fun h hr => by
    cases hr
    any_goals (
      focus
      intro ⟨_, hr⟩
      cases hr
      try (
        any_goals (
        focus
        rename_i hr
        cases hr)))
  run := mk_hole level
  complete := MkHole.complete
  none := fun h hr => by simp_all [hr.complete, failure]
  none_complete := fun h => by
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, ⟨hr⟩⟩
    exact (h hr).elim

end

end GenericExpr
