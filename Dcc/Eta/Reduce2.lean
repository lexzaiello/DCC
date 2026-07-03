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


TODO:
- will need domain preservation
-/

namespace GenericExpr

section

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

@[inline]
abbrev EtaExpr := GenericExpr (@EtaConst τ_c)

inductive MkHole : (ar : ℕ) → (level : ℕ) → (f : GenericExpr (@EtaConst τ_c)) → (heq : tm_arity f = ar) → (GenericExpr (@EtaConst τ_c)) → Type u
  | coupl : Domain f (DCC? Coup(β)) → MkHole 1 level f heq (DCC? (f ⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))))
  | tm    : Domain f τ → (ViewCoup τ → False) → MkHole 1 level f heq (DCC? (f hole(level + 1)))
  | bang  : Domain f (DCC? !(Coup(β))) → MkHole 1 level f heq (DCC? (f ⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))))
  | bang₂ : Domain₂ f (DCC? !(α)) (DCC? !<β>) → MkHole 2 level f heq (DCC? (f &(hole(level + 1)) &(hole(level + 2))))
  | tm₂   : Domain₂ f α β → (GenericExpr.is_bang α = .none) → MkHole 2 level f heq (DCC? (f hole(level + 1) hole(level + 2)))

@[grind]
def mk_hole (e : GenericExpr (@EtaConst τ_c)) (heq : tm_arity e = n) (level : ℕ) : Option ((f' : GenericExpr (@EtaConst τ_c)) × (PULift.{u + 2, u + 1} (MkHole n level e heq f'))) :=
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
def MkHole.eq {f f' : GenericExpr (@EtaConst τ_c)} {heq : f.tm_arity = n} (h₁ h₂ : MkHole n level f heq f') : h₁ = h₂ := by
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
def MkHole.complete {A B : GenericExpr (@EtaConst τ_c)} {heq : A.tm_arity = ar} (h : MkHole ar level A heq B) : mk_hole A heq level= .some ⟨B, ⟨h⟩⟩ := by
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
inductive EtaMap : (f : EtaExpr (τ_c := τ_c)) → (pre : EtaExpr (τ_c := τ_c)) → (out : EtaExpr (τ_c := τ_c)) → (hn : IsNorm RedAff out) → (f' : EtaExpr (τ_c := τ_c)) → Type u
  | id₁    : (arity f = 1) → Domain f τ → EtaMap f (DCC? (f hole_arg)) hole_arg hn (DCC? Id(τ))
  | par₁   : (arity f = 1) → Domain f τ
    → (ViewCoup τ → False)
    → Domain f' τ
    → EtaMap f (DCC? (f hole_arg)) (DCC? (f' hole_arg)) hn f'
  | fstc   : (arity f = 1) → Domain f τ → ViewCoup τ → (a ≠ b) → EtaMap f (DCC? (f ⟦β⟧(a, b))) a hn (DCC? Fstc(β))
  | sndc   : (arity f = 1) → Domain f τ → ViewCoup τ → (a ≠ b) → EtaMap f (DCC? (f ⟦β⟧(a, b))) b hn (DCC? Sndc(β))
  | fstc'  : (arity f = 1) → Domain f τ → ViewCoup τ → (a ≠ b) → EtaMap f (DCC? (f &(⟦β⟧(&(a), &(b))))) a hn (DCC? *<Fstc(β)>)
  | sndc'  : (arity f = 1) → Domain f τ → ViewCoup τ → (a ≠ b) → EtaMap f (DCC? (f &(⟦β⟧(&(a), &(b))))) b hn (DCC? *<Sndc(β)>)
  -- 2 arity
  | id₂    : (arity f = 2) → Domain f τ → EtaMap f (DCC? (f a b)) (DCC? (a b)) hn (DCC? Id(τ))
  | par₂   : (arity f = 2) → Domain₂ f α β → Domain₂ f' α β → EtaMap f (DCC? (f a b)) (DCC? (f' a b)) hn f'

@[grind]
def map_eta (f pre out : EtaExpr (τ_c := τ_c)) (hn : IsNorm RedAff out) : Option ((f' : EtaExpr) × (PULift.{u + 2, u + 1} (EtaMap f pre out hn f'))) :=
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
                     if heq₃ : τ' = τ then by
                       cases heq₀; cases heq₃; simp_all
                       exact .some ⟨_, ⟨.par₁ h_ar h
                         (view_coup?_none_sound h_coup_eq) h'⟩⟩
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
          | .some ⟨_, ⟨h⟩⟩ => by
            cases heq₀
            simp_all
            exact .some ⟨_, ⟨.id₂ h_ar h⟩⟩
          | .none => .none
        else
          match out with
          | (DCC? (f₂ some_hole₁' some_hole₂')) =>
            if heq₁ : (DCC? (f₂ some_hole₁' some_hole₂')) = (DCC? (f₂ some_hole₁ some_hole₂)) then
              match f.domain₂?, f₂.domain₂? with
              | .some ⟨α₁, β₁, ⟨h₁⟩⟩, .some ⟨α₂, β₂, ⟨h₂⟩⟩ =>
                if heq₂ : α₂ = α₁ then
                  if heq₃ : β₂ = β₁ then by
                    cases heq₀; cases heq₂; cases heq₃; simp_all
                    cases heq₁.left; cases heq₁.right
                    exact .some ⟨_, ⟨.par₂ h_ar h₁ h₂⟩⟩
                  else .none
                else .none
              | _, _ => .none
            else .none
          | _ => .none
      else .none
    | _ => .none
  else .none

open EtaRel in
def EtaMap.complete (h : EtaMap (τ_c := τ_c) f pre out hn f') : map_eta f pre out hn = .some ⟨f', ⟨h⟩⟩ := by
  induction h with
  | id₂ h_arity h_dom | id₁ h_arity h_dom => simp [map_eta, h_dom.complete, h_arity]
  | par₁ h_arity h_dom₁ hn₁ h_dom₂ =>
    rename_i τ f₁ hole_arg _
    have hneq : f₁.app hole_arg ≠ hole_arg := fun hr => by cases hr
    dsimp [map_eta]
    simp [h_arity, h_dom₁.complete, h_dom₂.complete, hneq]
    have h := ViewCoup.complete_none hn₁
    aesop
  | fstc h_arity h_dom₁ h_coup hneq
  | fstc' h_arity h_dom₁ h_coup hneq
  | sndc h_arity h_dom₁ h_coup hneq
  | sndc' h_arity h_dom₁ h_coup hneq =>
    rename_i τ a b β _hn
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
    rename_i α β f' a b _hn
    dsimp [map_eta]
    have hneq : f'.app a ≠ a := fun heq => by cases heq
    simp [h_arity, hneq, h_dom₁.complete, h_dom₂.complete]

instance EtaMap.instEtaRel : EtaRel (τ_c := (@EtaConst τ_c)) (fun f f' => EtaMap f pre out hn f') where
  run := fun a => map_eta a pre out hn
  is_norm_aff := fun hn hr => by
    induction hr
    any_goals (
      focus
      intro ⟨_, hr⟩
      cases hr
      done)
    case par₁ hn' heq h_dom₁ hn_coup h_dom₂ =>
      exact hn'.congrFun
    case par₂ hn' h_ar h_dom₁ h_dom₂ =>
      exact hn'.congrFun.congrFun
  complete         := EtaMap.complete
  none heq hr      := by simp_all [hr.complete]
  none_complete h  := by
    simp [failure]
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, ⟨hr⟩⟩
    exact (h hr).elim

instance : OptionEtaRel (τ_c := (@EtaConst τ_c)) (fun f f' => EtaMap (τ_c := τ_c) f pre out hn f') where

inductive EtaQuote : (f : EtaExpr (τ_c := τ_c)) → (out : EtaExpr (τ_c := τ_c)) → (hn : IsNorm RedAff out) → (f' : EtaExpr (τ_c := τ_c)) → Type u
  | tm₁     : (arity f = 1) → Domain f τ → EtaQuote f c hn (DCC? `(τ, c))
  | tm₂     : (arity f = 2) → Domain₂ f α (DCC? `(α₂, β))
    → EtaQuote f c hn (DCC? `(α, `(β, c)))
  | bang    : (arity f = 2) → Domain₂ f (DCC? !(α)) (DCC? !<β>)
    → EtaQuote f c hn (DCC? !Λ(α, β, `(!(Coup(β)), c)))
  | dep     : (arity f = 2) → Domain₂ f α β
    → (GenericExpr.is_bang_map β = .none)
    → (GenericExpr.is_quote β = .none)
    → EtaQuote f c hn (DCC? Λ(α, β, `(Coup(β), c)))

def quote_eta (f out : EtaExpr (τ_c := τ_c)) (hn : IsNorm RedAff out) : Option ((f' : EtaExpr) × (PULift.{u + 2, u + 1} (EtaQuote f out hn f'))) :=
  if h_ar : arity f = 1 then
    match f.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.tm₁ h_ar h⟩⟩
    | .none => .none
  else if h_ar : arity f = 2 then
    match f.domain₂? with
    | .some ⟨_α, (DCC? `(_α₂, _β)), ⟨h_dom⟩⟩ =>
      .some ⟨_, ⟨.tm₂ h_ar h_dom⟩⟩
    | .some ⟨(DCC? !(_α)), (DCC? !<_β>), ⟨h_dom⟩⟩ =>
      .some ⟨_, ⟨.bang h_ar h_dom⟩⟩
    | .some ⟨_α, β, ⟨h_dom⟩⟩ =>
      if heq₁ : β.is_bang_map = .none then
        if heq₂ : β.is_quote = .none then
          .some ⟨_, ⟨.dep h_ar h_dom heq₁ heq₂⟩⟩
        else .none
      else .none
    | .none => .none
  else .none

@[dcc_rel, aesop safe forward (rule_sets := [DccRel])]
def EtaQuote.complete (h : EtaQuote (τ_c := τ_c) f out hn f') : quote_eta f out hn = .some ⟨f', ⟨h⟩⟩ := by
  induction h with
  | tm₂ h_ar h_dom | bang h_ar h_dom | tm₁ h_ar h_dom => simp [quote_eta, h_ar, h_dom.complete]
  | dep h_ar h_dom hneq₁ hneq₂ =>
    simp [quote_eta, h_ar, h_dom.complete]
    split
    case h_1 h_dom₂ heq₂ =>
      have h := h_dom.deterministic h_dom₂
      simp_all
      cases h.right
      simp [is_quote] at hneq₂
    case h_2 h_dom₂ heq =>
      have h := h_dom.deterministic h_dom₂
      simp_all
      cases h.right; cases h.left
      simp [is_bang_map] at hneq₁
    case h_3 h_dom₂ ih₁ ih₂ heq =>
      have h := h_dom.deterministic h_dom₂
      cases h.left; cases h.right
      grind
    · simp_all

instance EtaQuote.instEtaRel : EtaRel (τ_c := (@EtaConst τ_c)) (fun f f' => EtaQuote f out hn f') where
  run := fun a => quote_eta a out hn
  is_norm_aff := fun hn hr => by induction hr <;> (intro ⟨_, hr⟩; cases hr)
  complete         := EtaQuote.complete
  none heq hr      := by simp_all [hr.complete]
  none_complete h  := by
    simp [failure]
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, ⟨hr⟩⟩
    exact (h hr).elim

instance EtaQuote.instOptionEtaRel : OptionEtaRel (τ_c := (@EtaConst τ_c)) (fun f f' => EtaQuote (τ_c := τ_c) f out hn f') where

instance EtaMap.instOptionEtaRel : OptionEtaRel (τ_c := (@EtaConst τ_c)) (fun f f' => EtaMap (τ_c := τ_c) f pre out hn f') where

inductive TmEtaReduces : (level : ℕ) → (f : @EtaExpr τ_c) → (f' : @EtaExpr τ_c) → Type u
  -- The reduction is not constant
  | map   : MkHole (tm_arity f)  level f rfl f_hole_app
    -- This is decreasing in size because const / hole has size 0
    → RedAffReflTrans f_hole_app e'
    → (hn : IsNorm RedAff e')
    → (e'.contains (DCC? hole(level + 1)) ∨ e'.contains (DCC? hole(level + 2)))
    → EtaMap f f_hole_app e' hn f'
    → TmEtaReduces level f f'
  | const : MkHole (tm_arity f) level f rfl f_hole_app
    -- This is decreasing in size because const / hole has size 0
    → RedAffReflTrans f_hole_app e'
    → (hn : IsNorm RedAff e')
    → (¬ e'.contains (DCC? hole(level + 1)))
    → (¬ e'.contains (DCC? hole(level + 2)))
    → EtaQuote f e' hn f'
    → TmEtaReduces level f f'

def red_eta_tm (level : ℕ) (f : @EtaExpr τ_c) : Option ((f' : @EtaExpr τ_c) × (PULift.{u + 2, u + 1} (TmEtaReduces level f f'))) :=
  match mk_hole f rfl level with
  | .some ⟨f_hole_app, ⟨h₁⟩⟩ =>
    let e' := (reduce RedAff f_hole_app).fst
    if h_contains : (e'.contains (DCC? hole(level + 1)) ∨ e'.contains (DCC? hole(level + 2))) then
      match map_eta f f_hole_app e' (reduce_norm rfl) with
      | .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.map h₁ (reduce_sound rfl) (reduce_norm rfl) (by grind) h₂⟩⟩
      | .none => .none
    else
      match quote_eta f e' (reduce_norm rfl) with
      | .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.const h₁ (reduce_sound rfl) (reduce_norm rfl) (by grind) (by grind) h₂⟩⟩
      | .none => .none
  | .none => .none

open EtaRel in
def TmEtaReduces.complete (h : TmEtaReduces (τ_c := τ_c) level f f') : red_eta_tm level f = .some ⟨f', ⟨h⟩⟩ := by
  induction h with
  | map h_mk_hole hrt hn h_contains h_map =>
    simp [red_eta_tm, h_mk_hole.complete, reduce_complete hrt hn, h_contains]
    have h_map_eq := h_map.complete
    cases (reduce_complete_fst hrt hn).symm
    simp [h_map_eq]
  | const h_mk_hole hrt hn h_contains₁ h_contains₂ h_quot =>
    simp [red_eta_tm, h_mk_hole.complete, reduce_complete hrt hn, h_contains₁, h_contains₂]
    have h_quot_eq := h_quot.complete
    cases (reduce_complete_fst hrt hn).symm
    simp [h_quot_eq]

instance TmEtaReduces.instEtaRel : EtaRel (TmEtaReduces (τ_c := τ_c) level) where
  run := red_eta_tm level
  is_norm_aff := fun hn hr => by
    induction hr
    · rename_i h_map
      exact EtaMap.instEtaRel.is_norm_aff hn h_map
    · rename_i h_quot
      exact EtaQuote.instEtaRel.is_norm_aff hn h_quot
  complete := TmEtaReduces.complete
  none heq hr      := by simp_all [hr.complete]
  none_complete h  := by
    simp [failure]
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, ⟨hr⟩⟩
    exact (h hr).elim
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
