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

@[inline]
abbrev EtaExpr := GenericExpr (@EtaConst τ_c)

inductive MkHole : (ar : ℕ) → (heq : arity f = ar) → (level : ℕ) → (f : GenericExpr (@EtaConst τ_c)) → (GenericExpr (@EtaConst τ_c)) → Type u
  | coupl : Domain f (DCC? Coup(β)) → MkHole 1 heq level f (DCC? (f ⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))))
  | tm    : Domain f τ → (ViewCoup τ → False) → MkHole 1 heq level f (DCC? (f hole(level + 1)))
  | bang  : Domain f (DCC? !(Coup(β))) → MkHole 1 heq level f (DCC? (f ⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))))
  | bang₂ : Domain₂ f (DCC? !(α)) (DCC? !<β>) → MkHole 2 heq level f (DCC? (f &(hole(level + 1)) &(hole(level + 2))))
  | tm₂   : Domain₂ f α β → (GenericExpr.is_bang α = .none) → MkHole 2 heq level f (DCC? (f hole(level + 1) hole(level + 2)))

@[grind]
def mk_hole (heq : arity e = n) (level : ℕ) (e : GenericExpr (@EtaConst τ_c)) : Option ((f' : GenericExpr (@EtaConst τ_c)) × (PULift.{u + 2, u + 1} (MkHole n heq level e f'))) :=
  match n with
  | 1 =>
    match domain? e with
    | .some ⟨τ, ⟨h⟩⟩ =>
      match heq : τ.view_coup? with
      | .some .coup => .some ⟨_, ⟨.coupl h⟩⟩
      | .some .bang => .some ⟨_, ⟨.bang h⟩⟩
      | .none => .some ⟨_, ⟨.tm h (fun h => by
        have h := h.complete
        grind)⟩⟩
    | .none => .none
  | 2 =>
    match heq : domain₂? e with
    | .some ⟨(DCC? !(α)), (DCC? !<β>), ⟨h⟩⟩ => .some ⟨_, ⟨.bang₂ h⟩⟩
    | .some ⟨α, β, ⟨h⟩⟩ =>
      if heq₂ : α.is_bang.isNone then
          .some ⟨_, ⟨.tm₂ h (by simp_all)⟩⟩
        else .none
    | .none => .none
  | _ => .none

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

open EtaRel in
@[aesop safe destruct (rule_sets := [DccRel])]
def MkHole.eq {f f' : GenericExpr (@EtaConst τ_c)} (h₁ h₂ : MkHole n heq level f f') : h₁ = h₂ := by
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
  · cases h₂
    rename_i heq₂ level₂ h_dom₁ _ _ h_dom₂
    simp_all [dcc_rel]
    have ha := h_dom₁.deterministic h_dom₂
    simp_all
    cases ha.left; cases ha.right
    simp [h_dom₁.eq h_dom₂]
  · cases h₂
    rename_i heq _ h_dom₁ heq₂ _ _ heq₃ h_dom₂
    have ha := h_dom₁.deterministic h_dom₂
    cases ha.left; cases ha.right
    have hb := h_dom₁.eq h_dom₂
    grind

@[dcc_rel, aesop safe forward (rule_sets := [DccRel])]
def MkHole.complete {A B : GenericExpr (@EtaConst τ_c)} (h : MkHole ar heq level A B) : mk_hole heq level A = .some ⟨B, ⟨h⟩⟩ := by
  induction h with
  | bang h_dom | coupl h_dom =>
    simp [mk_hole, h_dom.complete, view_coup?]
  | tm h_dom hn =>
    have h := ViewCoup.complete_none hn
    simp [mk_hole, h_dom.complete]
    split
    · simp_all
    · simp_all
    grind
  | tm₂ h_dom heq =>
    have h := h_dom.complete
    simp [mk_hole]
    split
    · grind
    · simp_all
      cases h.left; cases h.right
      grind
    · simp_all
  | bang₂ h_dom =>
    simp [mk_hole]
    rw [h_dom.complete]

/-
Instead of trying to construct the eta-reduction backwards, compare the output
against the core functions:

at least for most except par.

question again:
shouldn't
-/

/-
Since we have pre and post to compare,
we can combine 2-arity and one arity.
-/
inductive EtaMap : (f : EtaExpr (τ_c := τ_c)) → (pre : EtaExpr (τ_c := τ_c)) → (out : EtaExpr (τ_c := τ_c)) → (f' : EtaExpr (τ_c := τ_c)) → Type u
  | id₁    : (arity f = 1) → Domain f τ → EtaMap f (DCC? (f hole_arg)) hole_arg (DCC? Id(τ))
  | par₁   : (arity f = 1) → Domain f τ
    → (ViewCoup τ → False)
    → Domain f' τ
    → EtaMap f (DCC? (f hole_arg)) (DCC? (f' hole_arg)) f'
  | fstc   : (arity f = 1) → Domain f τ → ViewCoup τ → (a ≠ b) → EtaMap f (DCC? (f ⟦β⟧(a, b))) a (DCC? Fstc(β))
  | sndc   : (arity f = 1) → Domain f τ → ViewCoup τ → (a ≠ b) → EtaMap f (DCC? (f ⟦β⟧(a, b))) b (DCC? Sndc(β))
  | fstc'  : (arity f = 1) → Domain f τ → ViewCoup τ → (a ≠ b) → EtaMap f (DCC? (f &(⟦β⟧(&(a), &(b))))) a (DCC? *<Fstc(β)>)
  | sndc'  : (arity f = 1) → Domain f τ → ViewCoup τ → (a ≠ b) → EtaMap f (DCC? (f &(⟦β⟧(&(a), &(b))))) b (DCC? *<Sndc(β)>)
  -- 2 arity
  | id₂    : (arity f = 2) → Domain f τ → EtaMap f (DCC? (f a b)) (DCC? (a b)) (DCC? Id(τ))
  | par₂   : (arity f = 2) → Domain₂ f α β → Domain₂ f' α β → EtaMap f (DCC? (f a b)) (DCC? (f' a b)) f'

@[grind]
def map_eta (f pre out : EtaExpr (τ_c := τ_c)) : Option ((f' : EtaExpr) × (PULift.{u + 2, u + 1} (EtaMap f pre out f'))) :=
  if h_ar : arity f = 1 then
    match pre with
    | (DCC? (f₁ some_hole)) =>
      if heq₀ : f₁ = f then
         if heq₁ : out = some_hole then
           match f.domain? with
           | .some ⟨_, ⟨h⟩⟩ =>
             heq₀.symm ▸ heq₁ ▸ .some ⟨_, ⟨.id₁ h_ar h⟩⟩
           | _ => .none
         else
           match f.domain? with
           | .some ⟨τ, ⟨h⟩⟩ =>
             match h_coup_eq : τ.view_coup? with
             | .some h_coup =>
               match some_hole with
               | (DCC? ⟦_β⟧(a, b)) =>
                 if heqa : (a ≠ b) then
                   if heq₂ : out = a then
                     heq₀.symm ▸ heq₂ ▸ .some ⟨_, ⟨.fstc h_ar h h_coup (heq₂.symm ▸ heqa)⟩⟩
                   else if heq₂ : out = b then
                     heq₀.symm ▸ heq₂ ▸ .some ⟨_, ⟨.sndc h_ar h h_coup (heq₂.symm ▸ heqa)⟩⟩
                   else .none
                 else .none
               | (DCC? &(⟦_β⟧(&(a), &(b)))) =>
                 if heqa : a ≠ b then
                   if heq₂ : out = a then
                     heq₀.symm ▸ heq₂ ▸ .some ⟨_, ⟨.fstc' h_ar h h_coup (heq₂.symm ▸ heqa)⟩⟩
                   else if heq₂ : out = b then
                     heq₀.symm ▸ heq₂ ▸ .some ⟨_, ⟨.sndc' h_ar h h_coup (heq₂.symm ▸ heqa)⟩⟩
                   else .none
                 else .none
               | _ => .none
             | .none =>
               match out with
               | (DCC? (f' some_hole₂)) =>
                 if heq₂ : some_hole₂ = some_hole then
                   match f'.domain? with
                   | .some ⟨τ', ⟨h'⟩⟩ =>
                     if heq₃ : τ' = τ then
                       heq₀.symm ▸ heq₂.symm ▸ .some ⟨_, ⟨.par₁ h_ar h
                         (view_coup?_none_sound h_coup_eq) (heq₃ ▸ h')⟩⟩
                     else .none
                   | .none => .none
                 else .none
               | _ => .none
           | .none => .none
      else .none
    | _ => .none
  else if h_ar : arity f = 2 then
    match pre with
    | (DCC? (f₁ some_hole₁ some_hole₂)) =>
      if heq₀ : f₁ = f then
        if heq₁ : out = (DCC? (some_hole₁ some_hole₂)) then
          match f.domain? with
          | .some ⟨_, ⟨h⟩⟩ => heq₀.symm ▸ heq₁ ▸ .some ⟨_, ⟨.id₂ h_ar h⟩⟩
          | .none => .none
        else
          match out with
          | (DCC? (f₂ some_hole₁' some_hole₂')) =>
            if heq₁ : (DCC? (f₂ some_hole₁' some_hole₂')) = (DCC? (f₂ some_hole₁ some_hole₂)) then
              match f.domain₂?, f₂.domain₂? with
              | .some ⟨α₁, β₁, ⟨h₁⟩⟩, .some ⟨α₂, β₂, ⟨h₂⟩⟩ =>
                if heq₂ : α₂ = α₁ then
                  if heq₃ : β₂ = β₁ then
                    heq₀.symm ▸ heq₁.symm ▸ .some ⟨_, ⟨.par₂ h_ar h₁ (heq₂ ▸ heq₃ ▸ h₂)⟩⟩
                  else .none
                else .none
              | _, _ => .none
            else .none
          | _ => .none
      else .none
    | _ => .none
  else .none

open EtaRel in
theorem EtaMap.complete (h : EtaMap (τ_c := τ_c) f pre out f') : map_eta f pre out = .some ⟨f', ⟨h⟩⟩ := by
  induction h with
  | id₂ h_arity h_dom | id₁ h_arity h_dom => simp [map_eta, h_dom.complete, h_arity]
  | par₁ h_arity h_dom₁ hn₁ h_dom₂ =>
    dsimp [map_eta]
    simp [h_arity, h_dom₁.complete, h_dom₂.complete]
    split
    case isTrue heq => cases heq
    · grind
  | fstc h_arity h_dom₁ h_coup hneq
  | fstc' h_arity h_dom₁ h_coup hneq
  | sndc h_arity h_dom₁ h_coup hneq
  | sndc' h_arity h_dom₁ h_coup hneq =>
    rename_i τ a b β
    have hneq₁ : a ≠ β.mkc a b := fun heq => by cases heq
    have hneq₂ : b ≠ β.mkc a b := fun heq => by cases heq
    have hneq₃ : β ≠ β.mkc a b := fun heq => by cases heq
    have hneq₄ : a ≠ (DCC? &(⟦β⟧(&(a), &(b)))) := fun heq => by cases heq
    have hneq₅ : b ≠ (DCC? &(⟦β⟧(&(a), &(b)))) := fun heq => by cases heq
    have hneq₆ : β ≠ (DCC? &(⟦β⟧(&(a), &(b)))) := fun heq => by cases heq
    have h_coup := h_coup.complete
    dsimp [map_eta]
    simp [h_arity, h_dom₁.complete, hneq]
    grind
  | par₂ h_arity h_dom₁ h_dom₂ =>
    rename_i α β f' a b
    dsimp [map_eta]
    have hneq : f'.app a ≠ a := fun heq => by cases heq
    simp [h_arity, hneq, h_dom₁.complete, h_dom₂.complete]

inductive TmEtaReduces : (level : ℕ) → (f : @EtaExpr τ_c) → (f' : @EtaExpr τ_c) → Type u
  -- The reduction is not constant
  | pure : MkHole _ rfl level f f_hole_app
    -- This is decreasing in size because const / hole has size 0
    → RedAffReflTrans f_hole_app e'
    → IsNorm RedAff e'
    → (e'.contains (DCC? hole(level + 1)) ∨ e'.contains (DCC? hole(level + 2)))

/-
Can apply holes. MkHole.


-/

/-instance : EtaRel (τ_c := (@EtaConst τ_c)) (MkHole ar heq level) where
  is_norm_aff := fun h hr => by
    
  run := mk_hole level
  complete := MkHole.complete
  none := fun h hr => by simp_all [hr.complete, failure]
  none_complete := fun h => by
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, ⟨hr⟩⟩
    exact (h hr).elim-/



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

inductive TmEtaReduces : (arity : ℕ) → (level : ℕ) → (f : @EtaExpr τ_C) → (hn : IsNorm RedAff f) → (f' : @EtaExpr τ_c) → Type u
  | pure₁ : 

/-
When the resulting η-reduced function contains a hole
-/
inductive TmEtaReduces : (level : ℕ) → (f : GenericExpr (τ := EtaConst (τ := τ_c))) → (f' : GenericExpr (τ := EtaConst (τ := τ_c))) → Type u
  | arity₁  : RedAffReflTrans f f'
    → IsNorm RedAff f'
    → f'.tm_arity = 1
    → Domain f' τ
    → MkHole level f' hole
    → RedAffReflTrans (DCC? (f' hole)) e'
    → IsNorm RedAff e'
    → (e'.contains (DCC? hole(level + 1)) ∨ e'.contains (DCC? hole(level + 2)))
    → EtaMap τ e' hole f' f''
    → TmEtaReduces level f f''
  | arity₂  : RedAffReflTrans f f'
    → IsNorm RedAff f'
    → f'.tm_arity = 2
    → Domain₂ α β f
    → MkHole₂ level f' hole₁ hole₂
    → RedAffReflTrans (DCC? (f' hole₁ hole₂)) e'
    → IsNorm RedAff e'
    → (e'.contains (DCC? hole(level + 1)) ∨ e'.contains (DCC? hole(level + 2)))
    → EtaMap₂ α β e' hole₁ hole₂ f' f''
    → TmEtaReduces level f f''
  | quot₁   : RedAffReflTrans f f'
    → IsNorm RedAff f'
    → f'.tm_arity = 1
    → Domain f' τ
    → MkHole level f' hole
    → RedAffReflTrans (DCC? (f' hole)) e'
    → IsNorm RedAff e'
    → (¬ e'.contains (DCC? hole(level + 1)))
    → (¬ e'.contains (DCC? hole(level + 2)))
    → TmEtaReduces level f (DCC? `(τ, e'))
  | quot₂   : RedAffReflTrans f f'
    → IsNorm RedAff f'
    → f'.tm_arity = 2
    → Domain₂ f' α f_β
    → (GenericExpr.is_quote f_β = .none)
    → (GenericExpr.is_bang α = .none)
    → (GenericExpr.is_bang_map f_β = .none)
    → MkHole₂ level f' hole₁ hole₂
    → (¬ GenericExpr.contains e' (DCC? hole(level + 1)))
    → (¬ GenericExpr.contains e' (DCC? hole(level + 2)))
    → RedAffReflTrans (DCC? (f hole₁ hole₂)) e'
    → IsNorm RedAff e'
    → TmEtaReduces level f (DCC? Λ(α, f_β, `(Coup(f_β), e')))
  | quot₂'  : RedAffReflTrans f f'
    → IsNorm RedAff f'
    → f'.tm_arity = 2
    → Domain₂ f' α (DCC? `(α₂, β))
    → (GenericExpr.is_bang α = .none)
    → MkHole₂ level f' hole₁ hole₂
    → (¬ GenericExpr.contains e' (DCC? hole(level + 1)))
    → (¬ GenericExpr.contains e' (DCC? hole(level + 2)))
    → RedAffReflTrans (DCC? (f hole₁ hole₂)) e'
    → IsNorm RedAff e'
    → TmEtaReduces level f (DCC? `(α, `(β, e')))
  | quot₂'' : RedAffReflTrans f f'
    → IsNorm RedAff f'
    → f'.tm_arity = 2
    → Domain₂ f' α₀ f_β
    → (GenericExpr.is_bang α₀ = .some α)
    → (GenericExpr.is_bang_map f_β = .some β)
    → MkHole₂ level f' hole₁ hole₂
    → (¬ GenericExpr.contains e' (DCC? hole(level + 1)))
    → (¬ GenericExpr.contains e' (DCC? hole(level + 2)))
    → RedAffReflTrans (DCC? (f hole₁ hole₂)) e'
    → IsNorm RedAff e'
    → TmEtaReduces level f (DCC? !Λ(α, β, `(!(Coup(β)), e')))
  | pi      : TmEtaReduces level.succ f_α f_α'
    → TmEtaReduces level.succ.succ f_β f_β'
    → TmEtaReduces level (DCC? Π(f_α, f_β)) (DCC? Π(f_α', f_β'))

def red_eta_tm (level : ℕ) (f : GenericExpr (@EtaConst τ_c)) : Option ((f' : GenericExpr (@EtaConst τ_c)) × (PULift.{u + 2, u + 1} (TmEtaReduces level f f'))) :=
  let f₁ := (reduce RedAff f).fst
  have h_dec : f₁.size ≤ f.size := decreasing? _ (reduce RedAff f).snd.down
  match f₁.tm_arity with
  | 2 =>
    if h_contains₁ : f₁.contains (DCC? hole(level + 1)) ∨ f₁.contains (DCC? hole(level + 2)) then
      
      sorry
    else
      match f₁.domain₂? with
      | .some ⟨α, DCC? `(α₂, β), ⟨h⟩⟩ =>
        if h_bang : α.is_bang = .none then
          sorry
        else .none
      | .some ⟨
  | 1 =>
    sorry
  | _ =>
    sorry

end

end GenericExpr
