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
  - refl no TmEtaReduces₂ arity 2 case3

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

namespace Vector

end Vector

namespace NormExpr

/-
An η-reducible function is in normal form, has an arity of 1 or 2, and has known domain
-/
inductive EtaFn : (f : @EtaExpr.Norm τ_c) → (ar : ℕ) → Vector EtaExpr.Norm ar → Type u
  | tm₁ : {_heq : arity f = 1}
    → (h_dom : Domain f α)
    → EtaFn f 1 (Vector.mk ⟨[α]⟩ (by grind))
  | tm₂  : {_heq : arity f = 2}
    → (h_dom : Domain₂ f α β) → EtaFn f 2 (Vector.mk ⟨[α, β]⟩ (by grind))

@[dcc_size]
def EtaFn.arity_pos (e : EtaFn f ar doms) : 0 < ar :=
  match e with
  | .tm₁ h => by grind
  | .tm₂ h => by grind

@[grind]
def EtaFn.points (_h : EtaFn (τ_c := τ_c) ⟨f, hn⟩ ar doms) : Vector (EtaExpr.Norm (τ_c := τ_c)) (GenericExpr.point_arity f) :=
  (GenericExpr.points f).map GenericExpr.red_aff

/-def EtaFn.indices (h : EtaFn (τ_c := τ_c) ⟨f, hn⟩ ar doms) : Vector ((f' : @EtaExpr.Norm τ_c) × (ar' : ℕ) × (doms' : Vector EtaExpr.Norm ar') × (EtaFn f' ar' doms')) f.n_indices :=
  match h with
  | .tm₁ heq h_dom => by
    cases h_dom
    
    sorry
  | .tm₂ heq h_dom₂ =>
    sorry-/

@[aesop safe forward (rule_sets := [DccSize])]
def EtaFn.decreasing {f τ : @EtaExpr.Norm τ_c} {hn} (h : EtaFn f 1 ⟨⟨[τ]⟩, hn⟩) : τ.size < f.size :=
  match h with
  | .tm₁ h_dom => Domain.instRedRel.decreasing h_dom

@[grind]
def EtaFn.head_dom (e_f : EtaFn f ar doms) : ((τ : @EtaExpr.Norm τ_c) × (Domain f τ)) :=
  match e_f with
  | .tm₁ h_dom => ⟨_, h_dom⟩
  | .tm₂ h_dom => ⟨_, h_dom.to_domain⟩

@[grind]
def view_eta_fn (f : @EtaExpr.Norm τ_c) : Option ((ar : ℕ) × (doms : Vector (@EtaExpr.Norm τ_c) ar) × EtaFn f ar doms) :=
  if heq : f.arity = 1 then
    match f.domain? with
    | .some ⟨_, h⟩ => .some ⟨_, _, .tm₁ (_heq := heq) h⟩
    | .none => .none
  else if heq : f.arity = 2 then
    match f.domain₂? with
    | .some ⟨_, _, h⟩ => .some ⟨_, _, .tm₂ (_heq := heq) h⟩
    | .none => .none
  else .none

def EtaFn.complete {f : @EtaExpr.Norm τ_c} {doms : Vector EtaExpr.Norm ar} (h : EtaFn f ar doms) : view_eta_fn f = .some ⟨ar, doms, h⟩ := by
  induction h with
  | tm₂ h_dom | tm₁ h_dom => simp_all [view_eta_fn, h_dom.complete]

--def EtaFn.eq (h₁ h₂ : EtaFn f ar doms)

/-instance EtaFn.instEtaRel : EtaRel
  (α := @EtaExpr.Norm τ_c) (β := ((ar : ℕ) × Vector (@EtaExpr.Norm τ_c) ar))
    (fun f h => EtaFn f h.fst h.snd) (m := Option)  where
  run := fun e => match view_eta_fn e with
    | .some ⟨ar, doms, h⟩ => .some ⟨⟨ar, doms⟩, h⟩
    | .none => .none
  complete := fun h => by
    simp [h.complete]-/

open GenericExpr in
inductive Hole : (α : @EtaExpr.Norm τ_c)
  → (level : ℕ)
  → (hole_e : @EtaExpr.Norm τ_c)
  → Type u
  | pure : (ViewBangCoup α → False)
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
    if h_coup_some : α.view_bang_coup?.isSome then
      match α, α.view_bang_coup?.get h_coup_some with
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
      .some ⟨_, .pure (α.view_bang_coup?_none_sound (by simp_all))⟩
termination_by α.size

open GenericExpr in
def Hole.is_norm (_h : Hole α level ⟨tm_hole, hn_hole⟩) : IsNorm RedAff tm_hole := hn_hole

open GenericExpr in
def Hole.points_norm (h : Hole (τ_c := τ_c) α level ⟨tm_hole, hn_hole⟩) (point_idx : Fin (GenericExpr.point_arity tm_hole)) : IsNorm RedAff tm_hole.points[point_idx] := by
  cases h with
  | pure =>
    simp [point_arity] at point_idx
    nomatch point_idx
  | bang h_inner =>
    simp [point_arity] at point_idx
    match point_idx with
    | ⟨0, h_lt⟩ =>
      rename_i α hn_α hole hn_hole
      change IsNorm RedAff hole
      assumption
  | coup =>
    simp [point_arity] at point_idx
    match point_idx with
    | ⟨0, h_lt⟩ =>
      refine IsNorm.coup ?_
      assumption
    | ⟨1, h_lt⟩ => assumption
    | ⟨2, h_lt⟩ => assumption

@[aesop safe apply (rule_sets := [DccSize])]
def Hole.complete {α hole_e : @EtaExpr.Norm τ_c} (h : Hole α level hole_e) : mk_hole α level = .some ⟨hole_e, h⟩ := by
  induction h with
  | pure hn =>
    unfold mk_hole
    simp [GenericExpr.ViewBangCoup.complete_none hn]
  | bang h_hole heq =>
    unfold mk_hole
    simp [GenericExpr.view_bang_coup?, heq]
  | coup h_dom h_hole₁ hr₁ h_hole₂ heq₁ heq₂ =>
    unfold mk_hole
    have ha := hr₁.complete
    simp [GenericExpr.view_bang_coup?, h_dom.complete, heq₁]
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
  complete := ArgTy.complete (idx := idx) (e_f := e_f) (doms := doms)

inductive Holes : (e_f : EtaFn (τ_c := τ_c) f ar doms)
  → (level : ℕ)
  → (holes : Vector (@EtaExpr.Norm τ_c) ar) → Type u
  | tm₁ {e_f : EtaFn f 1 ⟨#[α], h⟩} : Hole α level hole_e
    → Holes e_f level ⟨#[hole_e], by grind⟩
  | tm₂ {e_f : EtaFn f 2 ⟨#[α, ⟨β₀, h_n_β⟩], h⟩} : Hole α (level + 2) ⟨hole₁, hn_hole₁⟩
    → RedAffNorm (DCC? (β₀ hole₁)) β
    → Hole β (level + 1) hole₂
    → Holes e_f level ⟨#[⟨hole₁, hn_hole₁⟩, hole₂], by grind⟩

@[grind]
def Holes.app {f : @EtaExpr.Norm τ_c} {doms : Vector (@EtaExpr.Norm τ_c) ar}
  {e_f : EtaFn f ar doms} {holes : Vector (@EtaExpr.Norm τ_c) ar}
  (_h : Holes e_f level holes) : @EtaExpr τ_c :=
  ((holes.map NormExpr.raw).foldl GenericExpr.app f.raw)

@[grind]
def Holes.app_reduce {e_f : EtaFn f ar doms} (_h : Holes e_f level holes) : ((e' : EtaExpr.Norm) ×
  (RedAffNorm ((holes.map NormExpr.raw).foldl GenericExpr.app f.raw) e')) :=
  ⟨_, aff_sound rfl⟩

@[grind]
def Holes.Reduces {e_f : EtaFn (τ_c := τ_c) f ar doms} (_h : Holes e_f level holes) (B : EtaExpr.Norm (τ_c := τ_c)) : Type u :=
  (RedAffNorm ((holes.map NormExpr.raw).foldl GenericExpr.app f.raw) B)

@[grind]
def Holes.fold {e_f : EtaFn (τ_c := τ_c) f ar doms} (on_f : @EtaExpr.Norm τ_c) (_h : Holes e_f level holes) : @EtaExpr.Norm τ_c :=
  let ⟨⟨τ₁, hn_τ⟩, h_arg⟩ := e_f.get_arg_ty (idx := ⟨0, e_f.arity_pos⟩) ⟨#[], by simp⟩
  red_aff <| (holes.map NormExpr.raw).foldl GenericExpr.app on_f.raw

@[grind]
def holes (e_f : EtaFn (τ_c := τ_c) f ar doms) (level : ℕ)
  : Option ((holes : Vector (@EtaExpr.Norm τ_c) ar) × Holes e_f level holes) := by
  cases e_f with
  | tm₁ h_dom =>
    rename_i α _
    match α.mk_hole level with
    | .some ⟨_, h⟩ => exact .some ⟨_, .tm₁ h⟩
    | .none => exact .none
  | tm₂ h_dom₂ =>
    rename_i α β₀ _
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
    | tm₁ dom => simp [holes, h_hole.complete]
  | tm₂ hr₁ h_hole₁ h_hole₂ =>
    rename_i e_f
    cases e_f with
    | tm₂ dom =>
      simp [holes, hr₁.complete, raw, (h_hole₁.complete ▸ h_hole₂).complete, h_hole₁.aff_complete]
      dcc_simp
      have h := (h_hole₁.out_eq ▸ h_hole₁).eq
      grind

def Holes.points_norm {e_f : EtaFn f ar doms} {hole_elems : Vector (@EtaExpr.Norm τ_c) ar}
  (h : Holes e_f level hole_elems)
  (idx    : Fin ar)
  (b_idx  : Fin hole_elems[idx].raw.point_arity) : IsNorm RedAff hole_elems[idx].raw.points[b_idx] := by
  cases h with
  | tm₁ h_hole =>
    rename_i hole_e e_f
    match idx with
    | ⟨0, h_lt⟩ => exact h_hole.points_norm b_idx
  | tm₂ h_hole₁ _ h_hole₂ =>
    match idx with
    | ⟨1, h_lt⟩ => exact h_hole₂.points_norm b_idx
    | ⟨0, h_lt⟩ => exact h_hole₁.points_norm b_idx

/-
Expressions that index an environment like Π(f_α, f_β) may be composed:
Π(f_α, f_β) ∘' g => Π(f_α ∘' g, f_β ∘' g)

However, this should occur as a last step, so as not to complicate
recursion.

the resulting updated indices are supplied
-/
--inductive Inline : (EtaFn f ar doms) → (indices : Vector (@EtaExpr

/-inductive Holes.Red : {e_f : EtaFn (τ_c := τ_c) f doms}
  → {level : ℕ}
  → (h : Holes (τ_c := τ_c) e_f level hole_tms)
  → @EtaExpr.Norm τ_c
  → Type u
  | id : {f        : @EtaExpr.Norm τ_c}
       → {doms     : Vector (@EtaExpr.Norm τ_c) (arity f)}
       → {level    : ℕ}
       → {e_f      : EtaFn f doms}
       → {hole_tms : Vector (@EtaExpr.Norm τ_c) (arity f)}
       → (e_h      : e_f.Holes level hole_tms)
       → (hr       : e_h.Reduces (Holes.-/

/-
Holes apply function that makes a Holes.Red
-/

set_option pp.rawOnError true
inductive Canonicalize : (e_f : EtaFn (τ_c := τ_c) f ar doms)
  → (e_f' : EtaFn (τ_c := τ_c) f' ar doms)
  → Type u
  | id₁   : (e_f : EtaFn f 1 ⟨#[α], by grind⟩)
    → (e_h : Holes e_f 0 ⟨#[hole₁], by grind⟩)
    → RedAffNorm (DCC? (f.raw hole₁.raw)) hole₁
    → Canonicalize e_f (.tm₁ (_heq := (by grind)) (.id ⟨.refl, α.is_norm⟩))
  | fstc  : (e_f : EtaFn f 1 ⟨#[⟨DCC? Coup(β), hn_coup⟩], by grind⟩)
    → (e_h : Holes e_f 0 ⟨#[⟨DCC? ⟦β⟧(a, b), hn_hole₁⟩], by grind⟩)
    → RedAffNorm (DCC? (f.raw ⟦β⟧(a, b))) ⟨a, hn_hole₁.sigl⟩
    → Canonicalize e_f (.tm₁ (_heq := (by grind)) (.fstc ⟨.refl, hn_coup.coup⟩))
  | sndc  : (e_f : EtaFn f 1 ⟨#[⟨DCC? Coup(β), hn_coup⟩], by grind⟩)
    → (e_h : Holes e_f 0 ⟨#[⟨DCC? ⟦β⟧(a, b), hn_hole₁⟩], by grind⟩)
    → RedAffNorm (DCC? (f.raw ⟦β⟧(a, b))) ⟨a, hn_hole₁.sigl⟩
    → Canonicalize e_f (.tm₁ (_heq := (by grind)) (.sndc ⟨.refl, hn_coup.coup⟩))
  | fstc' : (e_f : EtaFn f 1 ⟨#[⟨DCC? !(Coup(β)), hn_coup⟩], by grind⟩)
    → (e_h : Holes e_f 0 ⟨#[⟨DCC? &(⟦β⟧(a, b)), hn_hole₁⟩], by grind⟩)
    → RedAffNorm (DCC? (f.raw &(⟦β⟧(a, b)))) ⟨a, (fun ⟨_, hr⟩ => by
      have h := e_h.points_norm 0 ⟨0, by simp [dcc_size, raw, Vector.get]⟩
      change IsNorm RedAff (β.mkc a b) at h
      exact h ⟨_, .sigl hr⟩)⟩
    → Canonicalize e_f
      (.tm₁
        (f := ⟨.unmap (.fstc β), fun ⟨_, h⟩ => nomatch h⟩)
        (_heq := (by grind))
        (.unmap ⟨.refl, fun ⟨_, h⟩ => nomatch h⟩ (.fstc ⟨.refl, fun ⟨_, h⟩ => hn_coup ⟨_, .bang (.coup h)⟩⟩)))
  | sndc' : (e_f : EtaFn f 1 ⟨#[⟨DCC? !(Coup(β)), hn_coup⟩], by grind⟩)
    → (e_h : Holes e_f 0 ⟨#[⟨DCC? &(⟦β⟧(a, b)), hn_hole₁⟩], by grind⟩)
    → RedAffNorm (DCC? (f.raw &(⟦β⟧(a, b)))) ⟨b, (fun ⟨_, hr⟩ => by
      have h := e_h.points_norm 0 ⟨0, by simp [dcc_size, raw, Vector.get]⟩
      change IsNorm RedAff (β.mkc a b) at h
      exact h ⟨_, .sigr hr⟩)⟩
    → Canonicalize e_f
      (.tm₁
        (f := ⟨.unmap (.sndc β), fun ⟨_, h⟩ => nomatch h⟩)
        (_heq := (by grind))
        (.unmap ⟨.refl, fun ⟨_, h⟩ => nomatch h⟩ (.sndc ⟨.refl, fun ⟨_, h⟩ => hn_coup ⟨_, .bang (.coup h)⟩⟩)))
  | par   : (e_f : EtaFn f 1 ⟨#[α], by grind⟩)
    → (α.raw.ViewCoupBang → False)
    → (e_h : Holes e_f 0 ⟨#[⟨hole₁, hn_hole₁⟩], by grind⟩)
    → RedAffNorm (DCC? (f.raw hole₁)) ⟨(DCC? (f' hole₁)), hn₂⟩
    → (e_f' : EtaFn ⟨f', hn₂.congrFun⟩ 1 ⟨#[α], by grind⟩)
    → Canonicalize e_f e_f'
  | eval  : (e_f : EtaFn f 1 ⟨#[⟨DCC? Coup(β), hn₁⟩], by grind⟩)
    → (e_h : Holes e_f 0 ⟨#[⟨DCC? ⟦β⟧(a, b), hn_hole₁⟩], by grind⟩)
    → RedAffNorm (DCC? (f.raw ⟦β⟧(a, b))) ⟨DCC? (f' a b), hn'⟩
    → (e_f' : EtaFn ⟨f', hn'.congrFun.congrFun⟩ 2 ⟨#[α, ⟨β, hn₁.coup⟩], by grind⟩)
    → Canonicalize e_f (.tm₁ (_heq := by grind) (.eval (α := α.raw) (β := β) (x := f') ⟨.refl, hn₁.coup⟩))
  

-- remember eval case
/-
The canonical head of a reduction spine
-/
set_option pp.rawOnError true
inductive CanonFn : (e_f : EtaFn (τ_c := τ_c) f doms)
  → {level : ℕ}
  → (h_holes : e_f.Holes level hole_tms)
  → (e_f' : EtaFn f' doms₂)
  → Type (u + 1)
  | eval   : {f     : @EtaExpr.Norm τ_c}
           → {doms  : Vector (@EtaExpr.Norm τ_c) (arity f)}
           → {h_ar₁ : arity f = 1}
           → {level : ℕ}
           → {β     : @EtaExpr τ_c}
           → {hn₁   : IsNorm RedAff (DCC? Coup(β))}
           → (e_f   : EtaFn (τ_c := τ_c) f ⟨#[⟨DCC? Coup(β), hn₁⟩], h_ar₁ ▸ rfl⟩)
           → {ar    : β.arity = 1}
           → {α     : @EtaExpr.Norm τ_c}
           → (e_β       : EtaFn ⟨β, hn₁.coup⟩ ⟨#[α], (by grind)⟩)
           → {a b       : @EtaExpr τ_c}
           → {hn₃       : IsNorm RedAff (DCC? ⟦β⟧(a, b))}
           → (e_holes   : e_f.Holes level ⟨#[⟨(DCC? ⟦β⟧(a, b)), hn₃⟩], h_ar₁ ▸ rfl⟩)
           → {f'  : @EtaExpr τ_c}
           → {hn₄ : IsNorm RedAff (DCC? (f' a b))}
           → (hr        : e_holes.Reduces ⟨(DCC? (f' a b)), hn₄⟩)
           → {f'        : @EtaExpr.Norm τ_c}
           → {h_ar      : arity f' = 2}
           → CanonFn e_f e_holes (EtaFn.tm₁ (.eval (α := α.raw) (β := β) (x := f'.raw) (aff_sound rfl)))
  | id     : {f     : @EtaExpr.Norm τ_c}
           → {doms  : Vector (@EtaExpr.Norm τ_c) (arity f)}
           → {level : ℕ}
           → (e_f       : EtaFn (τ_c := τ_c) f doms)
           → (h_τ_hole₁ : e_f.ArgTy (idx := ⟨0, e_f.arity_pos⟩) ⟨#[], rfl⟩ α)
           → {hole_tms  : Vector (@EtaExpr.Norm τ_c) (arity f)}
           → (e_holes   : e_f.Holes level hole_tms)
           → (hr₁       : e_holes.Reduces (e_holes.fold ⟨DCC? Id(α.raw), by grind⟩))
           → CanonFn e_f e_holes (.tm₁ (.id ⟨.refl, α.is_norm⟩))
  /-| eval   : CanonFn level (.tm₂ f (DCC? (f ⟦β⟧(a, b))) (DCC? (f' a b)) hn (DCC? Eval(α, β, f'))
  | id₁    : (arity f = 1) → Domain f τ → CanonFn f (DCC? (f hole_arg)) hole_arg hn (DCC? Id(τ))
  | par₁   : (arity f = 1) → Domain f τ
    → (ViewCoup τ → False)
    → Domain f' τ
    → CanonFn f (DCC? (f hole_arg)) (DCC? (f' hole_arg)) hn f'
  | fstc   : (arity f = 1) → Domain f τ → ViewCoup τ → (a ≠ b) → CanonFn f (DCC? (f ⟦β⟧(a, b))) a hn (DCC? Fstc(β))
  | sndc   : (arity f = 1) → Domain f τ → ViewCoup τ → (a ≠ b) → CanonFn f (DCC? (f ⟦β⟧(a, b))) b hn (DCC? Sndc(β))
  | fstc'  : (arity f = 1) → Domain f τ → ViewCoup τ → (a ≠ b) → CanonFn f (DCC? (f &(⟦β⟧(&(a), &(b))))) a hn (DCC? *<Fstc(β)>)
  | sndc'  : (arity f = 1) → Domain f τ → ViewCoup τ → (a ≠ b) → CanonFn f (DCC? (f &(⟦β⟧(&(a), &(b))))) b hn (DCC? *<Sndc(β)>)
  -- 2 arity
  | id₂    : (arity f = 2) → Domain f τ → CanonFn f (DCC? (f a b)) (DCC? (a b)) hn (DCC? Id(τ))
  | par₂   : (arity f = 2) → Domain₂ f α β → Domain₂ f' α β → CanonFn f (DCC? (f a b)) (DCC? (f' a b)) hn f'-/

/-
To η-reduce an expression:

1. Apply holes
2. Canonicalize (pi types are a case)
  Notes:
    - Potentially do it type directed.
    - we already have the holes
    - Going backwards?

    inlining should handle Π comp case

  Steps:
  - par case where you just get (f holes)
    - Inline resulting expression
    - Wellfounded recursion: handle inner cases first? norm the points first
  - constant case:

- Reduce inductive only takes holes as parameter

- always inline after canonicalizing
- always fold if possible
3. 
-/
/-inductive Reduce : {f f' : @EtaExpr.Norm τ_c} → (EtaFn f ar doms) → (EtaFn f' ar doms) → Type u
  -/

end EtaFn

end NormExpr

/-
We can generate a list of holes for our expressions. Good.
We can also apply them with foldl.

To do:

- all the old reductions pretty much
  - However, condense into one inductive with new FnEta stuff
- + Eval
- Π still needs to be special cased

- Most ideal:
  - single inductive handles the whole thing
  - we are always reducing a function

  - however, Π terms have a special case
    - Can consider (Π(f_α, f_β) env) as being all points?
    - Π composition is also a special case.
      - Π(f_α, f_β) ∘' g -> Π(f_α ∘' g, f_β ∘' g)
      - we are essentially condensing the points. I like this.
      - any other examples of this behavior?
        - Coup(β)

We still still need to split up between term arity and point arity
maybe?

- FnEta also has a mapping from points to construct the pointed term.

e.g.,

FnEta : (points : ℕ) → 

Points are filled in beforehand, but we should be able to map them.

FnEta.apply (h : EtaFn n_points ar doms) (

We absolutely should be mapping points.

can do this in Ast.lean with a function:

points (e : GenericExpr τ_c) {n : ℕ} : Vector (point_arity e) (GenericExpr τ_c)

map_points (e : GenericExpr τ_c) (new_points : Vector (point_arity e) (GenericExpr τ_c → GenericExpr τ_c))

this is super simple.

^ necessary for handlinlg things like Coup(β)

TODO: how does this solve Π special case?

(Π(f_α, f_β) env)


(Π(f_α, f_β) ∘' g) -> Π(f_α ∘' g, f_β ∘' g)
^ this is folding / simplifying a point in

Π might just be a special case.

However, we might be able to generalize to apps in general with a fold function,
defined on specific values, like Π. yes.

GenericExpr.fold (f : GenericExpr τ_c)
Note: there are other cases like Π
!<β> ∘' ...

- also a concept of indices, which index the environment, but to create a term,
not just for typing information.

- important note: inlining happens after all other steps

these can all be folded.
observation: folding is always done with composition.
actually call this inlining.

Note: Π env case is special because it should theoretically be handled by 2-argument
app. e.g., curr
so, scrap that.

TODO:

- point_arity e
- map_points e, applied with Vector (point_arity e) (GenericExpr τ_c → GenericExpr τ_c)
- points e : Vector (point_arity e) (GenericExpr τ_c)
- Mem for hole list. Vector n (@EtaConst τ_c)
  - holes ∈ e

- inductive to actually do the η-reduction
  - should always η-reduce points. But how do we know we're at a spine?
    - points will not be defined, except at a spine. otherwise no-op
  - Another note: inlining might be subsumed by jsut adding Π as a recognized
    form in main η-reduction.

    - same general cases, but for Π

- tm_arity is useless. remove
-/

namespace GenericExpr

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
