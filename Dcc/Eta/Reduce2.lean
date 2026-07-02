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

inductive MkHole₂ : (level : ℕ) → (f : GenericExpr (@EtaConst τ_c)) → (GenericExpr (@EtaConst τ_c)) → (GenericExpr (@EtaConst τ_c)) → Type u
  | bang : Domain₂ f (DCC? !(α)) (DCC? !<β>) → MkHole₂ level f (DCC? &(hole(level + 1))) (DCC? &(hole(level + 2)))
  | tm   : Domain₂ f α β → (GenericExpr.is_bang α = .none) → MkHole₂ level f (DCC? hole(level + 1)) (DCC? hole(level + 2))

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

@[grind]
def mk_hole₂ (level : ℕ) (e : GenericExpr (@EtaConst τ_c)) : Option ((hole₁ hole₂ : GenericExpr (@EtaConst τ_c)) × (PULift.{u + 2, u + 1} (MkHole₂ level e hole₁ hole₂))) :=
  match heq : domain₂? e with
  | .some ⟨(DCC? !(α)), (DCC? !<β>), ⟨h⟩⟩ => .some ⟨(DCC? &(hole(level + 1))), (DCC? &(hole(level + 2))), ⟨.bang h⟩⟩
  | .some ⟨α, β, ⟨h⟩⟩ =>
    if heq₂ : α.is_bang.isNone then
        .some ⟨_, _, ⟨.tm h (by simp_all)⟩⟩
      else .none
  | .none => .none

@[dcc_rel, aesop safe apply (rule_sets := [DccRel])]
def Domain₂.eq {e α β : GenericExpr τ_c} (h₁ h₂ : Domain₂ e α β) : h₁ = h₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all

@[dcc_rel, aesop safe apply (rule_sets := [DccRel])]
def Domain.eq {e τ : GenericExpr τ_c} (h₁ h₂ : Domain e τ) : h₁ = h₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all

@[dcc_rel, aesop safe forward (rule_sets := [DccRel])]
def MkHole₂.complete {f hole₁ hole₂ : GenericExpr (@EtaConst τ_c)} (h : MkHole₂ level f hole₁ hole₂) : mk_hole₂ level f = .some ⟨hole₁, hole₂, ⟨h⟩⟩ := by
  induction h with
  | bang h_dom => rw [mk_hole₂, h_dom.complete]
  | tm  h_dom h_bang =>
    rw [mk_hole₂, h_dom.complete]
    simp
    split
    case h_1 h_dom₂ heq =>
      have ha := h_dom.complete
      have hb := h_dom₂.complete
      simp_all [h_dom₂.complete]
      rw [heq.left] at h_bang
      simp_all [is_bang]
    · dcc_aesop
    · simp_all

open EtaRel in
@[dcc_rel, aesop safe apply (rule_sets := [DccRel])]
def MkHole.eq {f f' : GenericExpr (@EtaConst τ_c)} (h₁ h₂ : MkHole level f f') : h₁ = h₂ := by
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

@[dcc_rel, aesop safe forward (rule_sets := [DccRel])]
def MkHole.complete {A B : GenericExpr (@EtaConst τ_c)} (h : MkHole level A B) : mk_hole level A = .some ⟨B, ⟨h⟩⟩ := by
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

inductive EtaMap : (dom : GenericExpr (τ := EtaConst (τ := τ_c))) → (out : GenericExpr (τ := EtaConst (τ := τ_c))) → (hole_arg : GenericExpr (τ := EtaConst (τ := τ_c))) → (f : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Type u
  | id    : EtaMap dom hole_arg hole_arg f (DCC? Id(dom))
  | par   : RedAffReflTrans f f' → IsNorm RedAff f' → EtaMap dom (DCC? (f hole_arg)) hole_arg f f'
  | fstc  : EtaMap dom (DCC? &(hole(a + 1))) (DCC? ⟦β⟧(&(hole(a + 1)), &(hole(a + 2)))) f (DCC? Fstc(β))
  | sndc  : EtaMap dom (DCC? &(hole(a + 2))) (DCC? ⟦β⟧(&(hole(a + 1)), &(hole(a + 2)))) f (DCC? Sndc(β))
  | fstc' : EtaMap dom (DCC? hole(a + 1)) (DCC? &(⟦β⟧(&(hole(a + 1)), &(hole(a + 2))))) f (DCC? *<Fstc(β)>)
  | sndc' : EtaMap dom (DCC? hole(a + 2)) (DCC? &(⟦β⟧(&(hole(a + 1)), &(hole(a + 2))))) f (DCC? *<Sndc(β)>)
  --| quot  : (¬ GenericExpr.contains out (DCC? hole(level + 1))) → (¬ GenericExpr.contains out (DCC? hole(level + 2))) → EtaMap level dom out hole_arg f (DCC? `(dom, out))

def map_eta (dom out hole_arg f : GenericExpr (τ := EtaConst (τ := τ_c))) : Option ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × PULift.{u + 2, u + 1} (EtaMap dom out hole_arg f f')) :=
  --if heq₀ : GenericExpr.contains out (DCC? hole(level + 1)) ∨ GenericExpr.contains out (DCC? hole(level + 2)) then
    if heq : out = hole_arg then
      heq ▸ .some ⟨_, ⟨.id⟩⟩
    else
      match out, hole_arg with
      | DCC? (_f hole_arg₂), hole_arg =>
        if heq : hole_arg₂ = hole_arg then
          if heq₃ : _f = f then
            heq₃ ▸ heq ▸ .some ⟨_, ⟨.par (reduce_sound rfl) (reduce_norm rfl)⟩⟩
          else .none
        else .none
      | (DCC? &(hole(n))), (DCC? ⟦_β⟧(&(hole(a + 1)), &(hole(b + 2)))) =>
        if h₁ : b = a then
          if h₂ : a + 1 = n then by
            --if h₃ : n = level + 1 then by
            --cases h₁; cases h₂ --; cases h₃
            cases h₁.symm; cases h₂.symm
            exact .some ⟨_, ⟨.fstc⟩⟩
          else if h₃ : n = b + 2 then by
            cases h₁; cases h₃; --cases h₂;
            exact .some ⟨_, ⟨.sndc⟩⟩
          else .none
        else .none
      | (DCC? hole(n)), (DCC? &(⟦_β⟧(&(hole(a + 1)), &(hole(b + 2))))) =>
        if h₁ : b = a then
          if h₂ : a + 1 = n then by
            cases h₁; cases h₂
            exact .some ⟨_, ⟨.fstc'⟩⟩
          else if h₃ : n = b + 2 then by
            cases h₁; cases h₃
            exact .some ⟨_, ⟨.sndc'⟩⟩
          else .none
        else .none
      | _, _ => .none
  --else .some ⟨_, ⟨.quot (by simp_all) (by simp_all)⟩⟩

@[aesop safe forward (rule_sets := [DccReduce])]
def EtaMap.complete {dom out hole_arg f f' : GenericExpr (τ := EtaConst (τ := τ_c))}
  (h : EtaMap (τ_c := τ_c) dom out hole_arg f f') : map_eta dom out hole_arg f = .some ⟨f', ⟨h⟩⟩ := by
  dsimp [map_eta]
  --split
  --case isTrue =>
  cases h
  any_goals (
    focus
    simp
    done)
  case par hn₁ hrt₁ =>
    have h := reduce_complete hrt₁ hn₁
    have heq : (reduce RedAff f).fst = f' := by simp_all
    cases heq
    simp_all
    intro heq
    cases heq
  /-case isFalse heq =>
    cases h
    · sorry
    · unfold contains at heq
      simp at heq
      replace heq := heq.right.right
      unfold contains at heq
      simp at heq
    · unfold contains at heq
      simp at heq-/

instance : EtaRel (EtaMap (τ_c := τ_c) dom out hole_arg) where
  run := map_eta dom out hole_arg
  is_norm_aff := fun hn hr => by
    induction hr
    any_goals (
      focus
      intro ⟨_, h⟩
      cases h
      done)
    case par hrt₁ hn₂ => exact hn₂
  complete := EtaMap.complete
  none := fun heq₁ hr => by aesop (rule_sets := [DccReduce])
  none_complete := fun hn => by
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, ⟨hr⟩⟩
    aesop (rule_sets := [DccReduce])

inductive EtaMap₂ : (dom₁ : GenericExpr (τ := EtaConst (τ := τ_c)))
  -- β hole₁
  → (dom₂ : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (out : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (hole₁ : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (hole₂ : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (f : GenericExpr (τ := EtaConst (τ := τ_c)))
  → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Type u
  | par      : RedAffReflTrans f f' → IsNorm RedAff f' → EtaMap₂ dom₁ dom₂ (DCC? (f hole₁ hole₂)) hole₁ hole₂ f f'
  | id       : EtaMap₂ dom₁ dom₂ (DCC? (hole₁ hole₂)) (DCC? hole₁) (DCC? hole₂) f (DCC? Id(dom₁))
-- hole₁ hole₂ = ⟦dom₂⟧(hole₁, hole₂) means this is Λ(dom₁, dom₂, Id(Coup(dom₂)))
-- this is basically 2 arg version of id
  | curr     : EtaMap₂ dom₁ dom₂ (DCC? ⟦dom₂⟧(hole₁, hole₂)) hole₁ hole₂ f (DCC? Λ(dom₁, dom₂, Id(Coup(dom₂))))
  | curr'    : EtaMap₂ (DCC? !(α)) (DCC? !<β>)
      (DCC? &(⟦β⟧(hole₁, hole₂)))
      (DCC? &(hole₁)) (DCC? &(hole₂))
      f
      (DCC? !Λ(α, β, Id(!(Coup(β)))))
  -- Exclusive with other two
  -- this is couple quotation
  -- if dom₂ is quotation i.e., `(dom₁, dom₂), then
  -- this is just simple double quotation `(dom₁, `(dom₂, c))

def map_eta₂ (dom₁ dom₂ out hole₁ hole₂ f : GenericExpr (τ := EtaConst (τ := τ_c))) : Option
  ((f' : GenericExpr (τ := EtaConst (τ := τ_c))) × (PULift.{u + 2, u + 1}
  (EtaMap₂ dom₁ dom₂ out hole₁ hole₂ f f'))) :=
  if heqa : out = (DCC? (hole₁ hole₂)) then by
    cases heqa
    exact .some ⟨_, ⟨.id⟩⟩
  else
    match heq₁ : out with
    | (DCC? (_f hole₃ hole₄)) =>
      if heq₂ : (DCC? (_f hole₃ hole₄)) = (DCC? (f hole₁ hole₂)) then by
        simp_all
        exact .some ⟨_, ⟨.par (reduce_sound rfl) (reduce_norm rfl)⟩⟩
      else .none
    | (DCC? ⟦dom₃⟧(hole₃, hole₄)) =>
      if heq₂ : (DCC? ⟦dom₃⟧(hole₃, hole₄)) = (DCC? ⟦dom₂⟧(hole₁, hole₂)) then by
        rw [heq₂]
        exact .some ⟨_, ⟨.curr⟩⟩
      else .none
    | (DCC? &(⟦β⟧(hole₃, hole₄))) =>
      match heq₂ : dom₁, heq₃ : dom₂, heq₄ : hole₁, heq₅ : hole₂ with
      | (DCC? !(α)), (DCC? !<β₂>), (DCC? &(ha)), (DCC? &(hb)) =>
        if heq₄ : (DCC? &(⟦β⟧(hole₃, hole₄))) = (DCC? &(⟦β₂⟧(ha, hb))) then by
          rw [heq₄]
          cases heq₄
          exact .some ⟨_, ⟨.curr'⟩⟩
        else .none
      | _, _, _, _ => .none
    | _ => .none

@[aesop safe forward (rule_sets := [DccReduce])]
def EtaMap₂.complete
  {dom₁ dom₂ out hole₁ hole₂ f f' : GenericExpr (τ := EtaConst (τ := τ_c))} (h : GenericExpr.EtaMap₂ (τ_c := τ_c) dom₁ dom₂ out hole₁ hole₂ f f') : map_eta₂ dom₁ dom₂ out hole₁ hole₂ f = .some ⟨f', ⟨h⟩⟩ := by
  dsimp [map_eta₂]
  cases h
  any_goals (
    focus
    simp
    done)
  case par hn₁ hrt₁ =>
    have h := reduce_complete hrt₁ hn₁
    have heq : (reduce RedAff f).fst = f' := by simp_all
    cases heq
    simp_all
    intro heq
    cases heq

instance : EtaRel (EtaMap₂ (τ_c := τ_c) dom₁ dom₂ out hole_arg₁ hole_arg₂) where
  run := map_eta₂ dom₁ dom₂ out hole_arg₁ hole_arg₂
  is_norm_aff := fun hn hr => by
    induction hr
    any_goals (
      focus
      intro ⟨_, h⟩
      cases h
      done)
    case par hrt₁ hn₂ => exact hn₂
  complete := EtaMap₂.complete
  none := fun heq₁ hr => by aesop (rule_sets := [DccReduce])
  none_complete := fun hn => by
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, ⟨hr⟩⟩
    aesop (rule_sets := [DccReduce])

/-
When the resulting η-reduced function contains a hole
-/
inductive TmEtaReduces : (level : ℕ) → (f : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Type u
  | arity₁ : RedAffReflTrans f f'
    → IsNorm RedAff f'
    → f'.tm_arity = 1
    → Domain f' τ
    → MkHole level f' hole
    → RedAffReflTrans (DCC? (f' hole)) e'
    → IsNorm RedAff e'
    → (e'.contains (DCC? hole(level + 1)) ∨ e'.contains (DCC? hole(level + 2)))
    → EtaMap τ e' hole f' f''
    → TmEtaReduces level f f''
  | arity₂ : RedAffReflTrans f f'
    → IsNorm RedAff f'
    → f'.tm_arity = 2
    → Domain₂ α β f
    → MkHole₂ level f' hole₁ hole₂
    → RedAffReflTrans (DCC? (f' hole₁ hole₂)) e'
    → IsNorm RedAff e'
    → (e'.contains (DCC? hole(level + 1)) ∨ e'.contains (DCC? hole(level + 2)))
    → EtaMap₂ α β e' hole₁ hole₂ f' f''
    → TmEtaReduces level f f''
  | quot₁  : RedAffReflTrans f f'
    → IsNorm RedAff f'
    → f'.tm_arity = 1
    → Domain f' τ
    → MkHole level f' hole
    → RedAffReflTrans (DCC? (f' hole)) e'
    → IsNorm RedAff e'
    → (¬ e'.contains (DCC? hole(level + 1)))
    → (¬ e'.contains (DCC? hole(level + 2)))
    → TmEtaReduces level f (DCC? `(dom
  | pi     : TmEtaReduces level.succ f_α f_α'
    → TmEtaReduces level.succ.succ f_β f_β'
    → TmEtaReduces level (DCC? Π(f_α, f_β)) (DCC? Π(f_α', f_β'))

end

end GenericExpr
