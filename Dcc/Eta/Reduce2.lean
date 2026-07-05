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

section

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

abbrev EtaExpr.Norm := NormExpr (τ := @EtaConst τ_c) GenericExpr.RedAff

namespace NormExpr

/-
An η-reducible function is in normal form, has an arity of 1 or 2, and has known domain
-/
inductive EtaFn : (f : @EtaExpr.Norm τ_c) → (ar : ℕ) → Vector EtaExpr.Norm ar → Type u
  | tm₁ : (heq : arity f = 1)
    → (h_dom : Domain f α)
    → EtaFn f 1 (Vector.mk ⟨[α]⟩ (by grind))
  | tm₂  : (heq : arity f = 2)
    → (h_dom : Domain₂ f α β) → EtaFn f 2 (Vector.mk ⟨[α, β]⟩ (by grind))

@[aesop safe forward (rule_sets := [DccSize])]
def EtaFn.decreasing {f τ : @EtaExpr.Norm τ_c} (h : EtaFn f 1 ⟨⟨[τ]⟩, by grind⟩) : τ.size < f.size :=
  match h with
  | .tm₁ _heq h_dom => Domain.instRedRel.decreasing h_dom

@[grind]
def EtaFn.head_dom (e_f : EtaFn f ar doms) : ((τ : @EtaExpr.Norm τ_c) × (Domain f τ)) :=
  match e_f with
  | .tm₁ _ h_dom => ⟨_, h_dom⟩
  | .tm₂ _ h_dom => ⟨_, h_dom.to_domain⟩

/-def EtaFn.dom_size_lt' {f τ : @EtaExpr.Norm τ_c} (h : EtaFn f 1 ⟨⟨[τ]⟩, by grind⟩) : (DCC? Id(τ.raw)).size < f.size :=
  have h_lt := h.decreasing
  match h with
  | .tm₁ _heq h_dom => by
    induction h_dom
    any_goals (grind)
    case unmap h_dom₁ hrt₁ hn₁ ih =>
      simp_all [size]
      have ha := Domain.instRedRel.decreasing h_dom₁
      have hb := decreasing? _ hrt₁
      have h := ih (.tm₁ (by simp_all [arity]) h_dom₁) ha (by grind) (hn₁ := (by assumption))
      --have h := ih (.tm₁ _heq (.unmap (by assumption) (by assumption) (by assumption)))
      sorry-/

/-@[aesop safe forward (rule_sets := [DccSize])]
def EtaFn.dom_size_lt' {f τ : @EtaExpr τ_c} {hn₁ : IsNorm RedAff f} {hn₂ : IsNorm RedAff τ} (h : EtaFn ⟨f, hn₁⟩ 1
  ⟨⟨[⟨τ, hn₂⟩]⟩, by grind⟩) : size (DCC? Id(τ)) < size f :=
  have h₀ := h.dom_size_lt
  match h with
  | .tm₁ _heq h_dom => by
    have h₁ := Domain.instRedRel.decreasing h_dom
    induction h_dom
    any_goals (grind)
    case unmap h_dom₁ hrt₁ hn₁ ih =>
      have h := ih (.tm₁ (by grind) h_dom₁) (Domain.instRedRel.decreasing h_dom₁) (by grind)
      have h := ih (.tm₁ (by rw [arity] at _heq; exact _heq) h_dom₁) (by
        have h_dec₁ := decreasing? _ hrt₁
        simp_all [size]
        grind
        sorry)
      sorry-/

@[grind]
def view_eta_fn (f : @EtaExpr.Norm τ_c) : Option ((ar : ℕ) × (doms : Vector (@EtaExpr.Norm τ_c) ar) × EtaFn f ar doms) :=
  if heq : f.arity = 1 then
    match f.domain? with
    | .some ⟨_, h⟩ => .some ⟨_, _, .tm₁ heq h⟩
    | .none => .none
  else if heq : f.arity = 2 then
    match f.domain₂? with
    | .some ⟨_, _, h⟩ => .some ⟨_, _, .tm₂ heq h⟩
    | .none => .none
  else .none

def EtaFn.complete {f : @EtaExpr.Norm τ_c} (h : EtaFn f ar doms) : view_eta_fn f = .some ⟨ar, doms, h⟩ := by
  induction h with
  | tm₂ h_ar h_dom | tm₁ h_ar h_dom => simp [view_eta_fn, h_ar, h_dom.complete]

--def EtaFn.eq (h₁ h₂ : EtaFn f ar doms)

instance EtaFn.instEtaRel : EtaRel
  (α := @EtaExpr.Norm τ_c) (β := ((ar : ℕ) × Vector (@EtaExpr.Norm τ_c) ar))
    (fun f h => EtaFn f h.fst h.snd) (m := Option)  where
  run := fun e => match view_eta_fn e with
    | .some ⟨ar, doms, h⟩ => .some ⟨⟨ar, doms⟩, h⟩
    | .none => .none
  complete := fun h => by
    simp [h.complete]

open GenericExpr in
inductive Hole : (α : @EtaExpr.Norm τ_c)
  → (level : ℕ)
  → (hole_e : @EtaExpr.Norm τ_c)
  → Type u
  | pure : (ViewCoup α → False)
    → Hole ⟨α, hn⟩ level ⟨(DCC? hole(level)), fun ⟨_, h⟩ => by cases h⟩
  | coup : Domain ⟨β, fun ⟨_, h⟩ => hn ⟨_, .coup h⟩⟩ α
    → Hole α (level + 2) ⟨hole₁, hn_hole₁⟩
    → RedAffNorm (DCC? (β hole₁)) τ_snd
    → Hole τ_snd (level + 1) ⟨hole₂, hn_hole₂⟩
    → Hole ⟨(DCC? Coup(β)), hn⟩ level ⟨DCC? ⟦β⟧(hole₁, hole₂), fun ⟨_, h⟩ =>
      match h with
      | .sigl h => hn_hole₁ ⟨_, h⟩
      | .sigr h => hn_hole₂ ⟨_, h⟩⟩
  | bang : Hole ⟨α, hn_α⟩ (level + 1) ⟨hole, hn_hole⟩ → Hole ⟨(DCC? !(α)), fun ⟨_, h⟩ =>
    match h with
    | .bang h => hn_α ⟨_, h⟩⟩ level ⟨(DCC? &(hole)), fun ⟨_, h⟩ => nomatch h⟩

@[dcc_size]
def Hole.size_zero (h : Hole α level hole_e) : hole_e.size = 0 := by
  induction h <;> grind

open GenericExpr in
@[grind]
def mk_hole (α : @EtaExpr.Norm τ_c) (level : ℕ) : Option ((hole_e : @EtaExpr.Norm τ_c) × Hole α level hole_e) :=
  match α with
  | ⟨α, hn_α⟩ =>
    if h_coup_some : α.view_coup?.isSome then
      match α, α.view_coup?.get h_coup_some with
      | DCC? Coup(β₀), .coup =>
        let β := (NormExpr.mk β₀ (fun ⟨_, h⟩ => hn_α ⟨_, .coup h⟩))
        match β.domain? with
        | .some ⟨α, h_dom⟩ =>
          have h_dec₁ : α.size < β.size := Domain.instRedRel.decreasing h_dom
          have h_dec₂ : α.size < β₀.size := by
            grind
          have h_dec₃ : α.size < (NormExpr.mk β₀.coup hn_α).size := by
            grind
          match α.mk_hole (level + 2) with
          | .some ⟨⟨hole₁, hn_hole₁⟩, h_hole₁⟩ =>
            let τ_snd      := red_aff (A := (DCC? (β₀ hole₁)))
            have h_size_eq := h_hole₁.size_zero
            have h_dec₁ : (β₀.app hole₁).red_aff.size ≤ (β₀.app hole₁).size := by
              grind
            have h_dec₂ : (β₀.app hole₁).red_aff.size < (mk β₀.coup hn_α).size := by
              grind
            match τ_snd.mk_hole (level + 1) with
            | .some ⟨⟨hole₂, hn_hole₂⟩, h_hole₂⟩ =>
              .some ⟨_, .coup h_dom h_hole₁ (aff_sound rfl) h_hole₂⟩
            | .none => .none
          | .none => .none
        | .none => .none
      | DCC? !(α₀), .bang =>
        let hn := (fun ⟨_, h⟩ => hn_α ⟨_, .bang h⟩)
        let α  := NormExpr.mk α₀ hn
        have h_dec : (NormExpr.mk α₀ hn).size < (mk α₀.bang hn_α).size := by
          grind
        match α.mk_hole (level + 1) with
        | .some ⟨_, h_hole₁⟩ => .some ⟨_, .bang h_hole₁⟩
        | .none => .none
    else
      .some ⟨_, .pure (α.view_coup?_none_sound (by simp_all))⟩
termination_by α.size

@[aesop safe apply (rule_sets := [DccSize])]
def Hole.complete {α hole_e : @EtaExpr.Norm τ_c} (h : Hole α level hole_e) : mk_hole α level = .some ⟨hole_e, h⟩ := by
  induction h with
  | pure hn =>
    unfold mk_hole
    simp [GenericExpr.ViewCoup.complete_none hn]
  | bang h_hole heq =>
    unfold mk_hole
    simp [GenericExpr.view_coup?, heq]
  | coup h_dom h_hole₁ hr₁ h_hole₂ heq₁ heq₂ =>
    unfold mk_hole
    have ha := hr₁.complete
    simp [GenericExpr.view_coup?, h_dom.complete, heq₁]
    cases ha.symm
    simp_all [GenericExpr.red_aff, hr₁.eq]

namespace EtaFn

/-
Need to recursively generate holes:

e.g., &(hole)

the problem is what to induct on.

However, dom should decrease.
we should make it over Dom first.

Note: Dom₂ ⊆ Dom
-/

open GenericExpr

def dom_norm (_e_f : EtaFn (τ_c := τ_c) f ar doms) (idx : Fin ar) : IsNorm RedAff doms[idx].raw := doms[idx].is_norm

inductive ArgTy : (e_f : EtaFn (τ_c := τ_c) f ar doms) → {idx : Fin ar}
  → (args : Vector (@EtaExpr.Norm τ_c) (Fin.toNat idx)) → @EtaExpr.Norm τ_c → Type u
  | mk {e_f : EtaFn f ar doms} {idx : Fin ar}
    {args : Vector (@EtaExpr.Norm τ_c) (Fin.toNat idx)} :
    (hr : RedAffNorm ((args.map NormExpr.raw).foldl .app doms[↑ idx].raw) τ)
    → ArgTy e_f args τ

@[grind]
def get_arg_ty (e_f : EtaFn f ar doms) {idx : Fin ar}
  (args : Vector (@EtaExpr.Norm τ_c) (Fin.toNat idx)) : ((t : @EtaExpr.Norm τ_c) × ArgTy e_f args t) := by
  cases e_f <;> exact ⟨_, .mk (aff_sound rfl)⟩

def ArgTy.complete {e_f : EtaFn (τ_c := τ_c) f ar doms}
  {idx : Fin ar} {args : Vector (@EtaExpr.Norm τ_c) idx}
  (h : ArgTy (idx := idx) e_f args τ) : e_f.get_arg_ty args = ⟨τ, h⟩ :=
  match h with
  | .mk hrt => by
    rename_i τ₁
    unfold get_arg_ty
    cases e_f <;> (
      dsimp
      cases hrt.out_eq
      dsimp [red_aff]
      simp [hrt.eq])

instance ArgTy.instEtaRel {e_f : EtaFn f ar doms} {idx : Fin ar} : EtaRel
  (α := Vector (@EtaExpr.Norm τ_c) idx) (β := EtaExpr.Norm) (ArgTy e_f (idx := idx)) (m := Id)  where
  run := get_arg_ty (idx := idx) e_f
  complete := ArgTy.complete (idx := idx) (e_f := e_f) (ar := ar) (doms := doms)

inductive Holes : (e_f : EtaFn (τ_c := τ_c) f ar doms)
  → (level : ℕ)
  → (holes : Vector (@EtaExpr.Norm τ_c) ar) → Type u
  | tm₁ {e_f : EtaFn f 1 ⟨#[α], by grind⟩} : Hole α level hole_e
    → Holes e_f level ⟨#[hole_e], by grind⟩
  | tm₂ {e_f : EtaFn f 2 ⟨#[α, ⟨β₀, h_n_β⟩], by grind⟩} : Hole α (level + 2) ⟨hole₁, hn_hole₁⟩
    → RedAffNorm (DCC? (β₀ hole₁)) β
    → Hole β (level + 1) hole₂
    → Holes (ar := 2) e_f level ⟨#[⟨hole₁, hn_hole₁⟩, hole₂], by grind⟩

@[grind]
def holes (e_f : EtaFn (τ_c := τ_c) f ar doms) (level : ℕ)
  : Option ((holes : Vector (@EtaExpr.Norm τ_c) ar) × Holes e_f level holes) := by
  cases e_f with
  | tm₁ heq h_dom =>
    rename_i α
    match α.mk_hole level with
    | .some ⟨_, h⟩ => exact .some ⟨_, .tm₁ h⟩
    | .none => exact .none
  | tm₂ heq h_dom₂ =>
    rename_i α β₀
    match α.mk_hole (level + 2) with
    | .some ⟨⟨hole₁, _hn_hole₁⟩, h₁⟩ =>
      match (red_aff (DCC? (β₀.raw hole₁))).mk_hole (level + 1) with
      | .some ⟨_hole₂, h₂⟩ =>
        exact .some ⟨_, .tm₂ h₁ (aff_sound rfl) h₂⟩
      | .none => exact .none
    | .none => exact .none

@[dcc_force_reduce, aesop safe apply (rule_sets := [DccForceReduce])]
def Holes.complete (h : Holes (τ_c := τ_c) e_f level hole_elems) : holes e_f level = .some ⟨hole_elems, h⟩ := by
  cases h with
  | tm₁ h_hole =>
    rename_i e_f
    cases e_f with
    | tm₁ heq dom => simp [holes, h_hole.complete]
  | tm₂ hr₁ h_hole₁ h_hole₂ =>
    rename_i e_f
    cases e_f with
    | tm₂ heq dom =>
      simp [holes, hr₁.complete, raw, (h_hole₁.complete ▸ h_hole₂).complete, h_hole₁.aff_complete]
      dcc_simp
      have h := (h_hole₁.out_eq ▸ h_hole₁).eq
      grind

end EtaFn

end NormExpr

namespace GenericExpr

/-
Holes are either couples, or banged couples.

Coup(β)

a hole for β is the fst element
-/
inductive MkHole : (dom : @EtaExpr τ_c) → (level : ℕ) → (hole_e : @EtaExpr τ_c) → Type u
  -- No more recursion. This is a terminal leaf
  | pure : (ViewCoup dom → False) → MkHole dom level (DCC? hole(level))
  | coup : Domain β α → MkHole α (level + 1) x
    → (RedAffNorm (DCC? (β x)) τ_y)
    → MkHole τ_y (level + 2) y
    → MkHole (DCC? Coup(β)) level (DCC? ⟦β⟧(x, y))
  | bang : MkHole α (level + 1) x → MkHole (DCC? !(α)) level (DCC? &(x))

inductive AppHoles : (ar : ℕ) → (level : ℕ) → (f : @EtaExpr τ_c) → (heq : arity f = ar) → (holes : List (@EtaExpr τ_c)) → Type u
  | tm₁ : Domain f α
    → MkHole α (level + 1) hole₁
    → AppHoles 1 level f heq [hole₁]
  | tm₂ : Domain₂ f α β → MkHole α (level + 1) hole₁
    → RedAffNorm (DCC? (β hole₁)) β'
    → MkHole β' (level + 2) hole₂
    → AppHoles 2 level f heq [hole₁, hole₂]

@[dcc_size]
def MkHole.size_zero (h : MkHole dom level hole_e) : hole_e.size = 0 :=
  match h with
  | .pure hn => by grind
  | .coup h_dom h_mk₁ ⟨hrt₁, hn₁⟩ h_mk₂ =>
    have ha := h_mk₁.size_zero
    have hb := h_mk₂.size_zero
    by grind
  | .bang h_mk =>
    have ha := h_mk.size_zero
    by grind

/-inductive MkHole : (ar : ℕ) → (level : ℕ) → (f : GenericExpr (@EtaConst τ_c)) → (heq : tm_arity f = ar) → (GenericExpr (@EtaConst τ_c)) → Type u
  | coupl : Domain f (DCC? Coup(β)) → MkHole 1 level f heq (DCC? (f ⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))))
  | tm    : Domain f τ → (ViewCoup τ → False) → MkHole 1 level f heq (DCC? (f hole(level + 1)))
  | bang  : Domain f (DCC? !(Coup(β))) → MkHole 1 level f heq (DCC? (f ⟦β⟧(&(hole(level + 1)), &(hole(level + 2)))))
  | bang₂ : Domain₂ f (DCC? !(α)) (DCC? !<β>) → MkHole 2 level f heq (DCC? (f &(hole(level + 1)) &(hole(level + 2))))
  | tm₂   : Domain₂ f α β → (GenericExpr.is_bang α = .none) → MkHole 2 level f heq (DCC? (f hole(level + 1) hole(level + 2)))-/

@[grind]
def mk_hole (dom : @EtaExpr τ_c) (level : ℕ) : Option ((f' : GenericExpr (@EtaConst τ_c)) × (MkHole dom level f')) :=
  if heq : dom.view_coup?.isSome then
    match heq : dom.view_coup?.get heq with
    | (.coup (β := β)) =>
      match GenericExpr.domain? β with
      | .some ⟨α, h_dom_β⟩ =>
        have h_dec : α.size < β.coup.size := by
          have h := Domain.instRedRel.decreasing h_dom_β
          grind
        match mk_hole α (level + 1) with
        | .some ⟨x, h₁⟩ =>
          have h_dec : (DCC? (β x)).size < (DCC? Coup(β)).size := by
            have ha := h₁.size_zero
            grind
          have h_dec₂ : (reduce RedAff (DCC? (β x))).fst.size < (DCC? Coup(β)).size := by
            have h := decreasing? RedAff (reduce_sound (A := (DCC? (β x))) rfl)
            grind
          match mk_hole (reduce RedAff (DCC? (β x))).fst (level + 2) with
          | .some ⟨_, h₂⟩ =>
            .some ⟨_, .coup h_dom_β h₁ (reduce_sound rfl) (reduce_norm rfl) h₂⟩
          | .none => .none
        | .none => .none
      | .none => .none
    | (.bang (α := α)) =>
      have h_dec : α.size < α.bang.size := by
        grind
      match mk_hole α (level + 1) with
      | .some ⟨_, h⟩ => .some ⟨_, .bang h⟩
      | .none => .none
  else
    .some ⟨_, .pure (view_coup?_none_sound (by simp_all))⟩
termination_by dom.size

def app_holes (ar level : ℕ) (f : @EtaExpr τ_c) (heq : arity f = ar) : Option ((holes : List (@EtaExpr τ_c)) × (AppHoles ar level f heq holes)) :=
  if heq : ar = 1 then
    match f.domain? with
    | .some ⟨_, h_dom⟩ =>
      sorry
    | .none => .none
  else if heq : ar = 2 then
    match f.domain₂? with
    | .some ⟨_, _, h_dom⟩ =>
      sorry
  else .none

def MkHole.complete {dom hole_e : @EtaExpr τ_c} (h : MkHole dom level hole_e) : mk_hole dom level = .some ⟨hole_e, h⟩ := by
  induction h with
  | pure hn => simp [mk_hole, ViewCoup.complete_none hn]
  | coup h_dom h_mk₁ hrt₁ hn₁ h_mk₂ heq₁ heq₂ =>
    have h := reduce_complete_fst hrt₁ hn₁
    rw [mk_hole]
    simp [view_coup?, h_dom.complete, heq₁]
    cases h
    simp [heq₂]
  | bang h_mk heq =>
    rw [mk_hole]
    simp [view_coup?, heq]

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
def MkHole.eq {dom hole_e : @EtaExpr τ_c} (h₁ h₂ : MkHole dom level hole_e) : h₁ = h₂ := by
  have heq₁ := h₁.complete
  have heq₂ := h₂.complete
  grind

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
  | eval   : (arity f = 1)
    → Domain f τ
    → ViewCoup τ
    → (a ≠ b)
    → Domain₂ f' α β
    → EtaMap f (DCC? (f ⟦β⟧(a, b))) (DCC? (f' a b)) hn (DCC? Eval(α, β, f'))
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
def map_eta (f pre out : EtaExpr (τ_c := τ_c)) (hn : IsNorm RedAff out) : Option ((f' : EtaExpr) × (EtaMap f pre out hn f')) :=
  if h_ar : arity f = 1 then
    match pre with
    | (DCC? (f₁ some_hole)) =>
      if heq₀ : f₁ = f then
         if heq₁ : out = some_hole then
           match f.domain? with
           | .some ⟨_, h⟩ =>
             heq₀.symm ▸ heq₁ ▸ .some ⟨_, .id₁ h_ar h⟩
           | _ => .none
         else
           match f.domain? with
           | .some ⟨τ, h⟩ =>
             match h_coup_eq : τ.view_coup? with
             | .some h_coup =>
               match some_hole with
               | (DCC? ⟦_β⟧(a, b)) =>
                 if heqa : (a ≠ b) then
                   if heq₂ : out = a then
                     heq₀.symm ▸ heq₂ ▸ .some ⟨_, .fstc h_ar h h_coup (heq₂.symm ▸ heqa)⟩
                   else if heq₂ : out = b then
                     heq₀.symm ▸ heq₂ ▸ .some ⟨_, .sndc h_ar h h_coup (heq₂.symm ▸ heqa)⟩
                   else
                     match out with
                     | (DCC? (f' a' b')) =>
                       match f'.domain₂? with
                       | .some ⟨α, β₂, h_dom_f'⟩ =>
                         if heq₃ : β₂ = _β then
                           if heq₂ : (DCC? (f' a' b')) = (DCC? (f' a b)) then by
                             cases heq₂
                             exact heq₀.symm ▸ (heq₃ ▸ (.some ⟨_, .eval h_ar h h_coup heqa h_dom_f'⟩)) --heq₂ ▸ .some ⟨_, ⟨.eval h_ar h h_coup heqa h_dom_f'⟩⟩
                           else .none
                         else .none
                       | .none => .none
                     | _ => .none
                 else .none
               | (DCC? &(⟦_β⟧(&(a), &(b)))) =>
                 if heqa : a ≠ b then
                   if heq₂ : out = a then
                     heq₀.symm ▸ heq₂ ▸ .some ⟨_, .fstc' h_ar h h_coup (heq₂.symm ▸ heqa)⟩
                   else if heq₂ : out = b then
                     heq₀.symm ▸ heq₂ ▸ .some ⟨_, .sndc' h_ar h h_coup (heq₂.symm ▸ heqa)⟩
                   else .none
                 else .none
               | _ => .none
             | .none =>
               match out with
               | (DCC? (f' some_hole₂)) =>
                 if heq₂ : some_hole₂ = some_hole then
                   match f'.domain? with
                   | .some ⟨τ', h'⟩ =>
                     if heq₃ : τ' = τ then by
                       cases heq₀; cases heq₃; simp_all
                       exact .some ⟨_, .par₁ h_ar h
                         (view_coup?_none_sound h_coup_eq) h'⟩
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
          | .some ⟨_, h⟩ => by
            cases heq₀
            simp_all
            exact .some ⟨_, .id₂ h_ar h⟩
          | .none => .none
        else
          match out with
          | (DCC? (f₂ some_hole₁' some_hole₂')) =>
            if heq₁ : (DCC? (f₂ some_hole₁' some_hole₂')) = (DCC? (f₂ some_hole₁ some_hole₂)) then
              match f.domain₂?, f₂.domain₂? with
              | .some ⟨α₁, β₁, h₁⟩, .some ⟨α₂, β₂, h₂⟩ =>
                if heq₂ : α₂ = α₁ then
                  if heq₃ : β₂ = β₁ then by
                    cases heq₀; cases heq₂; cases heq₃; simp_all
                    cases heq₁.left; cases heq₁.right
                    exact .some ⟨_, .par₂ h_ar h₁ h₂⟩
                  else .none
                else .none
              | _, _ => .none
            else .none
          | _ => .none
      else .none
    | _ => .none
  else .none

open EtaRel in
def EtaMap.complete (h : EtaMap (τ_c := τ_c) f pre out hn f') : map_eta f pre out hn = .some ⟨f', h⟩ := by
  induction h with
  | eval h_arity h_dom₁ h_coup hneq h_dom₂ =>
    rename_i τ a b f' α β hn
    dsimp [map_eta]
    have h := h_coup.complete
    have hneq₁ : (f'.app a).app b ≠ a := fun heq => by cases heq
    have hneq₂ : (f'.app a).app b ≠ b := fun heq => by cases heq
    have hneq₃ : b ≠ β.mkc a b := fun heq => by cases heq
    simp [h_arity, h_dom₁.complete, h_dom₂.complete, hneq]
    grind
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

-- TODO: maybe precondition that f does not contain holes?
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

instance TmEtaReduces.instOptionEtaRel : OptionEtaRel (TmEtaReduces (τ_c := τ_c) level) where

inductive RedEtaAtom : (e : GenericExpr (τ := τ_c)) → (e' : GenericExpr (τ := τ_c)) → Type u
  | mk    : TmEtaReduces 0 (expr_to_eta e₁) e₃ → (hn : ¬ e₃.contains_hole) → RedEtaAtom e₁ (eta_to_expr e₃ hn)
  | refl  : TmEtaReduces 0 (expr_to_eta e₁) e₃ → (hn : e₃.contains_hole) → RedEtaAtom e₁ e₁
  | refl₂ : (∀ {e₃ : EtaExpr}, TmEtaReduces 0 (expr_to_eta e₁) e₃ → False) → RedEtaAtom e₁ e₁

def red_eta_atom (e : @GenericExpr τ_c) : ((e' : @GenericExpr τ_c) × (PULift.{u + 2, u + 1} (RedEtaAtom e e'))) :=
  match heq : red_eta_tm 0 (expr_to_eta e) with
  | .some ⟨e', ⟨h⟩⟩ =>
    if heq₂ : e'.contains_hole then
      ⟨_, ⟨.refl h heq₂⟩⟩
    else⟨_, ⟨.mk h heq₂⟩⟩
  | .none => ⟨_, ⟨.refl₂ (TmEtaReduces.instEtaRel.none heq)⟩⟩

open OptionEtaRel in
def RedEtaAtom.complete (hr : RedEtaAtom (τ_c := τ_c) e e') : red_eta_atom e = ⟨e', ⟨hr⟩⟩ := by
  induction hr with
  | refl h_red h_contains | mk h_red h_contains =>
    have ha := h_red.complete
    simp [red_eta_atom]
    grind
  | refl₂ hn =>
    simp [red_eta_atom]
    split
    case h_1 hr heq =>
      exact (hn hr).elim
    rfl

def MkHole.arity_pos (h : MkHole ar level f heq f') : 0 < ar := by
  cases h <;> simp_all

def TmEtaReduces.arity_pos {e e' : EtaExpr} (h : TmEtaReduces (τ_c := τ_c) level e e') : 0 < tm_arity e := by
  induction h <;> exact MkHole.arity_pos (by assumption)

def tm_arity_zero_no_tm_eta_red {e e' : EtaExpr} (h : tm_arity e = 0) (hr : TmEtaReduces (τ_c := τ_c) level e e') : False := by
  have h := hr.arity_pos
  grind

inductive RedEta₂ : (e : GenericExpr (τ := τ_c)) → (e' : GenericExpr (τ := τ_c)) → Type u
  | pi₁  : RedEta₂ f_α f_α'
    → Domain (expr_to_eta f_α) δ
    → (hn : ¬ δ.contains_hole)
    → RedEta₂ env env'
    → RedAffReflTrans (DCC? (f_β env)) f_β_env
    → IsNorm RedAff f_β_env
    → RedEta₂ f_β_env f_β'
    → RedEta₂ (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', `(#(eta_to_expr δ hn), f_β')) env'))
  | pi₂   : RedEta₂ f_α f_α'
    → ((∀ {δ : EtaExpr}, Domain (expr_to_eta f_α) δ → PEmpty.{u + 1}) ⊕
      ((δ : EtaExpr) × (Domain (expr_to_eta f_α) δ) × (PULift.{u + 1, 0} (δ.contains_hole = true))))
    → RedEta₂ env env'
    → RedEta₂ f_β f_β'
    → RedEta₂ (DCC? (Π(f_α, f_β) env)) (DCC? (Π(f_α', f_β') env'))
  | coup  : RedEta₂ β β' → RedEta₂ (DCC? Coup(β)) (DCC? Coup(β'))
  | bang  : RedEta₂ β β' → RedEta₂ (DCC? !(β)) (DCC? !(β'))
  | pi₃   : RedEta₂ f_α f_α'
    → RedEta₂ f_β f_β'
    → RedEta₂ (DCC? Π(f_α, f_β)) (DCC? Π(f_α', f_β'))
  | pi₄   : RedAffReflTrans (DCC? f_α) f_α₁
    → IsNorm RedAff f_α₁
    → RedEta₂ (DCC? (f_α₁ ∘' g)) f_α'
    → RedAffReflTrans (DCC? f_β) f_β₁
    → IsNorm RedAff f_β₁
    → RedEta₂ (DCC? (f_β₁ ∘' g)) f_β'
    → RedEta₂ (DCC? (Π(f_α, f_β) ∘' g)) (DCC? Π(f_α', f_β'))
  | tm    : (ViewEta e → False) → RedEtaAtom e e' → RedEta₂ e e'

@[dcc_force_reduce]
def red_eta (e : GenericExpr τ_c) : ((e' : GenericExpr τ_c) × (PULift.{u + 2, u + 1} (RedEta₂ e e'))) :=
  if h_some : e.view_eta?.isSome then
    match e.view_eta?.get h_some with
    | (.pi_type (f_α := f_α) (f_β := f_β) (env := env)) =>
      have h_dec₁ : env.size < (DCC? (Π(f_α, f_β) env)).size := by
        grind
      have h_dec₂ : f_α.size < (DCC? (Π(f_α, f_β) env)).size := by
        grind
      have h_dec₂ : (DCC? (f_α env)).size < (DCC? (Π(f_α, f_β) env)).size := by
        grind
      have h_dec' : f_β.size < (DCC? (Π(f_α, f_β) env)).size := by
        grind
      match h_dom_eq : f_α.expr_to_eta.domain? with
      | .some ⟨δ, ⟨h₂⟩⟩ =>
        have h_dec₃ : (reduce RedAff (DCC? (f_β env))).fst.size < (DCC? (Π(f_α, f_β) env)).size := by
          have h := (reduce RedAff (DCC? (f_β env))).snd.down
          have h_le : (reduce RedAff (DCC? (f_β env))).fst.size ≤ (DCC? (f_β env)).size :=
            red_aff_decreasing? h
          grind
        if h₃ : δ.contains_hole then
          ⟨_, ⟨.pi₂ f_α.red_eta.snd.down (.inr ⟨δ, h₂, ⟨h₃⟩⟩) env.red_eta.snd.down f_β.red_eta.snd.down⟩⟩
        else
          ⟨_, ⟨.pi₁ f_α.red_eta.snd.down h₂ h₃ env.red_eta.snd.down
            (reduce_sound rfl) (reduce_norm rfl) (reduce RedAff (DCC? (f_β env))).fst.red_eta.snd.down⟩⟩
      | .none =>
        ⟨_, ⟨.pi₂ f_α.red_eta.snd.down (.inl (fun h_dom => by
          have h := h_dom.complete
          simp_all)) env.red_eta.snd.down f_β.red_eta.snd.down⟩⟩
    | (.pi (f_α := f_α) (f_β := f_β)) =>
      have h_dec₁ : f_α.size < (DCC? Π(f_α, f_β)).size := by
        grind
      have h_dec₂ : f_β.size < (DCC? Π(f_α, f_β)).size := by
        grind
      match f_α.red_eta, f_β.red_eta with
      | ⟨_, ⟨h₁⟩⟩, ⟨_, ⟨h₂⟩⟩ => ⟨_, ⟨.pi₃ h₁ h₂⟩⟩
    | (.pi_comp (f_α := f_α) (f_β := f_β) (g := g)) =>
      have h_dec₁ : (reduce RedAff f_α).fst.size ≤ f_α.size :=
        decreasing? _ (reduce RedAff f_α).snd.down
      have h_dec₂ : (reduce RedAff f_β).fst.size ≤ f_β.size :=
        decreasing? _ (reduce RedAff f_β).snd.down
      have h_dec₃ : (DCC? (#((reduce RedAff f_α).fst) ∘' g)).size < (DCC? Π(f_α, f_β) ∘' g).size := by
        grind
      have h_dec₄ : (DCC? (#((reduce RedAff f_β).fst) ∘' g)).size < (DCC? Π(f_α, f_β) ∘' g).size := by
        grind
      ⟨_, ⟨.pi₄ (reduce_sound rfl) (reduce_norm rfl) (DCC? (#((reduce RedAff f_α).fst) ∘' g)).red_eta.snd.down (reduce_sound rfl) (reduce_norm rfl) (DCC? (#((reduce RedAff f_β).fst) ∘' g)).red_eta.snd.down⟩⟩
    | (.coup (β := β)) =>
      have h_dec : β.size < (DCC? Coup(β)).size := by
        grind
      match β.red_eta with
      | ⟨_, ⟨h⟩⟩ => ⟨_, ⟨.coup h⟩⟩
    | (.bang (β := β)) =>
      have h_dec : β.size < (DCC? !(β)).size := by
        grind
      match β.red_eta with
      | ⟨_, ⟨h⟩⟩ =>
        ⟨_, ⟨.bang h⟩⟩
  else
    have h := view_eta?_none_sound (e := e) (by simp_all)
    ⟨_, ⟨.tm h (red_eta_atom e).snd.down⟩⟩
termination_by e.size

def RedEta₂.complete {e e' : GenericExpr τ_c} (h : RedEta₂ e e') : red_eta e = ⟨e', ⟨h⟩⟩ := by
  induction h
  case pi₁ hr₁ h_dom₁ hn₁ hr₂ hrt₁ hn₂ hr₃ heq₁ heq₂ heq₃ =>
    have hb := h_dom₁.complete
    have hd := reduce_complete hrt₁ hn₂
    rename_i f_α f_α' δ env env' f_β f_β_env f_β'
    let red_env_eq : (reduce RedAff (f_β.app env)).fst = f_β_env := by simp_all
    unfold red_eta
    simp [view_eta?]
    split
    case h_1 h_dom₂ heq₄ =>
      have heq₅ := h_dom₁.deterministic h_dom₂
      cases heq₅.symm
      simp_all
      cases red_env_eq
      grind
    · simp_all
  case pi₂ hr₁ ih hr₂ hr₃ heq₁ heq₂ heq₃ =>
    simp [red_eta, view_eta?]
    match h_ok_eq : ih with
    | .inl h =>
      split
      case h_1 h_dom heq => cases h h_dom
      simp_all
      cases h_ok_eq.symm
      congr <;> grind
    | .inr ⟨δ', h₁, ⟨h₂⟩⟩ =>
      split
      case h_1 h_dom heq =>
        have ha := h₁.deterministic h_dom
        have hb := (ha ▸ h₁).eq h_dom
        cases ha
        simp [h₂]
        simp_all
        congr <;> grind
      · have h := h₁.complete
        grind
  case pi₃ hr₁ hr₂ heq₁ heq₂ | bang hr ih | coup hr ih =>
    rw [red_eta]
    dsimp only [view_eta?]
    dsimp
    simp [*]
    congr <;> grind
  case pi₄ hrt₁ hn₁ hr₁ hrt₂ hn₂ hr₂ heq₁ heq₂ =>
    have ha := reduce_complete hrt₁ hn₁
    have hb := reduce_complete hrt₂ hn₂
    rename_i f_α f_α₁ g f_α' f_β f_β₁ f_β'
    have heqa : (reduce RedAff f_α).fst = f_α₁ := by simp_all
    have heqb : (reduce RedAff f_β).fst = f_β₁ := by simp_all
    rw [red_eta]
    dsimp only [view_eta?]
    dsimp
    cases heqa; cases heqb
    grind
  case tm hn_view hr =>
    have h := hr.complete
    rw [red_eta]
    simp [ViewEta.complete_none hn_view, h]
    congr <;> grind

end

end GenericExpr
