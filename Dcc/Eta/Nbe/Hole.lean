import Dcc.Eta.Ast
import Dcc.Eta.View
import Dcc.Eta.Reflect
import Dcc.Ast.Points
import Dcc.Eta.Nbe.Domain
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic

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

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

/-@[grind =, grind →, grind! →]
theorem cast_mem_tm (h : mem_tm (τ_c := (@EtaConst τ_c)) (expr_to_eta e) to_find) : mem_tm e (eta_to_expr to_find hn_mem) := by
  sorry-/

end GenericExpr

namespace NormExpr

/-def from_eta {f : @GenericExpr (@EtaConst τ_c)} {hn : GenericExpr.IsNorm GenericExpr.RedAff f} (hn_hole : ¬ f.contains_hole) : @NormExpr τ_c GenericExpr.RedAff :=
  ⟨f.eta_to_expr hn_hole, hn.from_eta hn_hole⟩-/

def from_eta' (f : @NormExpr (@EtaConst τ_c) GenericExpr.RedAff) (hn : ¬ GenericExpr.contains_hole f.raw) : @NormExpr τ_c GenericExpr.RedAff :=
  NormExpr.from_eta _ hn

/-
An η-reducible function is in normal form, has an arity of 1 or 2, and has known domain
-/
open GenericExpr

inductive EtaFn : (f : @NormExpr τ_c RedAff) → List (@NormExpr τ_c RedAff) → Type u
  | tm₁  : (h_dom  : Domain f α) → EtaFn f [α]

@[inline, grind]
def EtaFn.arity (_e_f : EtaFn f doms) : ℕ := doms.length

def EtaFn.to_eta {f : @GenericExpr τ_c} {hn : IsNorm RedAff f} (e : EtaFn ⟨f, hn⟩ doms) : EtaFn (mk f hn).to_eta (doms.map (·.to_eta)) := by
  cases e with
  | tm₁ h_dom => expose_names; exact .tm₁ h_dom.to_eta

def EtaFn.from_eta {f : @GenericExpr (@EtaConst τ_c)} {hn : IsNorm RedAff f} (hn_mem : ¬ f.contains_hole) {doms : List (@EtaExpr.Norm τ_c)}
  (e : EtaFn ⟨f, hn⟩ doms) :
    EtaFn ⟨f.eta_to_expr hn_mem, hn.from_eta hn_mem⟩ (by
      cases e with
      | tm₁ =>
        expose_names
        have h := h_dom.no_holes (by grind)
        exact [α.from_eta h]) := by
  simp
  cases e with
  | tm₁ =>
    expose_names
    exact .tm₁ (by
      have hn := h_dom.no_holes (by grind)
      have h  := h_dom.from_eta (by grind) (by grind)
      simp [NormExpr.from_eta] at h
      exact h)

@[grind =, grind =_, grind =>, grind! ., grind! =>]
theorem EtaFn.to_eta_arr_same {e : EtaFn ⟨f, hn⟩ doms} : e.to_eta.arity = e.arity := by
  grind

@[grind]
def EtaFn.vdoms {f : @NormExpr τ_c RedAff}
  {doms : List (@NormExpr τ_c RedAff)}
  (e : EtaFn f doms) : Vector (@NormExpr τ_c RedAff) e.arity :=
  ⟨⟨doms⟩, rfl⟩

@[dcc_size]
def EtaFn.arity_pos (e : EtaFn f doms) : 0 < e.arity := by
  cases e; grind

/-@[dcc_size]
def EtaFn.length (e : EtaFn f doms) : doms.length = arity f := by
  cases e <;> grind

@[grind]
def EtaFn.vdoms {f : @NormExpr τ_c RedAff} {doms : List (@NormExpr τ_c RedAff)}
  (e : EtaFn f doms) : Vector (@NormExpr τ_c RedAff) (arity f) :=
  ⟨⟨doms⟩, e.length⟩

@[dcc_size]
def EtaFn.arity_pos (e : EtaFn f doms) : 0 < (arity f) :=
  match e with
  | .tm₁ h => by grind
  | .tm₂ h => by grind-/

@[grind]
def EtaFn.points (_h : EtaFn (τ_c := τ_c) ⟨f, hn⟩ doms) : Vector (@NormExpr τ_c RedAff) (GenericExpr.point_arity f) :=
  (GenericExpr.points f).map GenericExpr.red_aff

/-def EtaFn.indices (h : EtaFn (τ_c := τ_c) ⟨f, hn⟩ ar doms) : Vector ((f' : @EtaExpr.Norm τ_c) × (ar' : ℕ) × (doms' : Vector EtaExpr.Norm ar') × (EtaFn f' ar' doms')) f.n_indices :=
  match h with
  | .tm₁ heq h_dom => by
    cases h_dom

    sorry
  | .tm₂ heq h_dom₂ =>
    sorry-/

@[aesop safe forward (rule_sets := [DccSize])]
def EtaFn.decreasing {f τ : @NormExpr τ_c RedAff} (h : EtaFn f [τ]) : τ.size < f.size :=
  match h with
  | .tm₁ h_dom => Domain.instRedRel.decreasing h_dom

@[grind]
def EtaFn.head_dom (e_f : EtaFn f [α]) : Domain f α :=
  match e_f with
  | .tm₁ h_dom => h_dom

@[grind]
def view_eta_fn (f : @NormExpr τ_c RedAff) : Option ((doms : List (@NormExpr τ_c RedAff)) × EtaFn f doms) :=
  match f.domain? with
  | .some ⟨_, h⟩ => .some ⟨_, .tm₁ h⟩
  | .none => .none

/-@[grind]
def view_eta_fn (f : @NormExpr τ_c RedAff) : Option ((doms : List (@NormExpr τ_c RedAff)) × EtaFn f doms) :=
  if heq : f.arity = 1 then
    match f.domain? with
    | .some ⟨_, h⟩ =>
      .some ⟨_, .tm₁ (_heq := heq) h⟩
    | .none => .none
  else if heq : f.arity = 2 then
    match f.domain₂? with
    | .some ⟨_, _, h⟩ =>
      .some ⟨_, .tm₂ (_heq := heq) h⟩
    | .none => .none
  else .none-/

def EtaFn.complete {f : @NormExpr τ_c RedAff} {doms : List (@NormExpr τ_c RedAff)} (h : EtaFn f doms) : view_eta_fn f = .some ⟨doms, h⟩ := by
  induction h with
  | tm₁ h_dom =>
    rename_i _heq
    have ha := h_dom.complete
    simp_all [view_eta_fn]

def view_eta_fn_none_sound {f : @NormExpr τ_c RedAff} (h : view_eta_fn f = .none) : ∀ {doms}, EtaFn f doms → False := by
  intro _ h
  have h := h.complete
  grind

def EtaFn.none_complete {f : @NormExpr τ_c RedAff} (h : ∀ {doms}, EtaFn f doms → False) : view_eta_fn f = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨doms, e_f⟩
  exact (h e_f).elim

@[dcc_force_reduce]
def EtaFn.eq (h₁ h₂ : EtaFn (τ_c := τ_c) f doms) : h₁ = h₂ := by
  cases h₁ with
  | tm₁ =>
    cases h₂ with
    | tm₁ =>
      expose_names
      cases h_dom.eq h_dom_1; rfl

/-def EtaFn.arity₁ (h : EtaFn f [dom₁]) : arity f = 1 :=
  match h with
  | .tm₁ (_heq := heq) _ => heq

def EtaFn.arity₂ (h : EtaFn f [dom₁, dom₂]) : arity f = 2 :=
  match h with
  | .tm₂ (_heq := heq) _ => heq

def EtaFn.arity_eq (h : EtaFn f doms) : arity f = doms.length :=
  match h with
  | .tm₁ (_heq := heq) _ => heq
  | .tm₂ (_heq := heq) _ => heq-/

open GenericExpr

inductive Hole : (α : @EtaExpr.Norm τ_c)
  → (level : ℕ)
  → (hole_e : @EtaExpr.Norm τ_c)
  → Type u
  | pure : (ViewBangCoup α → False)
    → Hole ⟨α, hn⟩ level ⟨(DCC? hole(level)), fun ⟨_, h⟩ => by cases h⟩
  | coup : Domain ⟨β, hn.point' 0⟩ α
    → Hole α (level + 2) ⟨hole₁, hn_hole₁⟩
    → RedAffNorm (DCC? (β hole₁)) τ_snd
    → Hole τ_snd (level + 1) ⟨hole₂, hn_hole₂⟩
    → Hole ⟨(DCC? Coup(β)), hn⟩ level ⟨DCC? ⟦hole₁⟧(hole₁, hole₂), fun ⟨_, h⟩ =>
      match h with
      | .sig₀ h => hn_hole₁ ⟨_, h⟩
      | .sig₁ h => hn_hole₁ ⟨_, h⟩
      | .sig₂ h => hn_hole₂ ⟨_, h⟩⟩
  | bang : Hole ⟨α, hn_α⟩ (level + 1) ⟨hole, hn_hole⟩ → Hole ⟨(DCC? !(α)), mk_inner_norm⟩ level
    ⟨(DCC? &(hole)), mk_inner_norm⟩
deriving DecidableEq

def Hole.contains_hole (h : Hole (τ_c := τ_c) α lv hole_e) : hole_e.raw.contains_hole := by
  induction h <;> grind

def Hole.hole_mem_tm (h : Hole (τ_c := τ_c) α lv hole_e) : hole_e.raw.hole_mem_tm := by
  induction h <;> grind

def Hole.sigt_hole_mem_tm (h : Hole (τ_c := τ_c) α lv ⟨(DCC? (⟦β⟧(a, b))), hn⟩) : β.hole_mem_tm := by
  cases h with
  | coup _ ha _ _ => exact ha.hole_mem_tm

def Hole.sigl_hole_mem_tm (h : Hole (τ_c := τ_c) α lv ⟨(DCC? (⟦β⟧(a, b))), hn⟩) : a.hole_mem_tm := by
  cases h with
  | coup _ ha _ _ => exact ha.hole_mem_tm

def Hole.sigl_hole_mem_tm_box (h : Hole (τ_c := τ_c) α lv ⟨(DCC? &(⟦β⟧(a, b))), hn⟩) : a.hole_mem_tm := by
  cases h with
  | bang h =>
    exact h.sigl_hole_mem_tm

def Hole.sigt_hole_mem_tm_box (h : Hole (τ_c := τ_c) α lv ⟨(DCC? &(⟦β⟧(a, b))), hn⟩) : β.hole_mem_tm := by
  cases h with
  | bang h => exact h.sigt_hole_mem_tm

def Hole.sigr_hole_mem_tm (h : Hole (τ_c := τ_c) α lv ⟨(DCC? (⟦β⟧(a, b))), hn⟩) : b.hole_mem_tm := by
  cases h with
  | coup _ _ _ ha => exact ha.hole_mem_tm

def Hole.sigr_hole_mem_tm_box (h : Hole (τ_c := τ_c) α lv ⟨(DCC? &(⟦β⟧(a, b))), hn⟩) : b.hole_mem_tm := by
  cases h with
  | bang h =>
    exact h.sigr_hole_mem_tm

def Hole.is_not_app (h : Hole α lv ⟨a, hn⟩) (heq : a = (DCC? (x y))) : False := by
  cases h <;> cases heq

@[grind]
def Hole.raw (_h : Hole (τ_c := τ_c) α lv hole_e) : @GenericExpr (@EtaConst τ_c) := hole_e.raw

def Hole.level_neq (h₁ : Hole α m x) (h₂ : Hole β n y) (hneq : m ≠ n) : x ≠ y := fun h => by
  induction h₁ generalizing β n y with
  | pure hn_coup =>
    cases h₂ <;> grind
  | bang h_hole ih =>
    cases h₂ with
    | pure =>
      grind
    | bang h_hole =>
      simp_all
      have h := ih (by assumption) (by grind)
      grind
    | coup hrt₂ h_hole₁ hrt h_hole₂ => exact ih h_hole (by grind) rfl
  | coup =>
    cases h₂ with
    | pure =>
      grind
    | coup h_dom h_hole₂ hrt h_hole₁ =>
      simp_all
      rename_i ih₁ ih₂
      rename_i heq
      cases heq
      exact ih₁ h_hole₂ (by grind) rfl
    | bang =>
      rename_i ih₁ ih₂ _ _ _ _ h_hole₂
      exact ih₁ (by assumption) (by grind) rfl

-- HERE: need to use this to prove False in previous file
def Hole.coup_points_neq (h : Hole _a level ⟨(DCC? ⟦β⟧(a, b)), hn_hole⟩) : a ≠ b := fun heq => by
  cases h with
  | coup h_dom h_hole₁ hrt h_hole₂ =>
    cases heq
    exact h_hole₁.level_neq h_hole₂ (by grind) (by grind)

def Hole.bang_coup_points_neq (h : Hole _a level ⟨(DCC? &(⟦β⟧(a, b))), hn_hole⟩) : a ≠ b := fun heq => by
  cases h with
  | bang h =>
    have h := h.coup_points_neq
    grind

@[dcc_size]
def Hole.size_zero (h : Hole α level hole_e) : hole_e.size = 0 := by
  induction h <;> grind

def Hole.arr_zero (h : Hole α level hole_e) : arity hole_e = 0 := by
  induction h <;> grind

@[grind]
def mk_hole (α : @EtaExpr.Norm τ_c) (level : ℕ) : Option ((hole_e : @EtaExpr.Norm τ_c) × Hole α level hole_e) :=
  match α with
  | ⟨α, hn_α⟩ =>
    if h_coup_some : α.view_bang_coup?.isSome then
      match α, α.view_bang_coup?.get h_coup_some with
      | DCC? Coup(β₀), .coup =>
        let β := (NormExpr.mk β₀ (fun ⟨_, h⟩ => hn_α ⟨_, .coup₀ h⟩))
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
        let hn := (fun ⟨_, h⟩ => hn_α ⟨_, .bang₀ h⟩)
        let α  := NormExpr.mk α₀ hn
        have h_dec : (NormExpr.mk α₀ hn).size < (mk α₀.bang hn_α).size := by
          grind
        match α.mk_hole (level + 1) with
        | .some ⟨_, h_hole₁⟩ => .some ⟨_, .bang h_hole₁⟩
        | .none => .none
    else
      .some ⟨_, .pure (α.view_bang_coup?_none_sound (by simp_all))⟩
termination_by α.size

def Hole.is_norm (_h : Hole α level ⟨tm_hole, hn_hole⟩) : IsNorm RedAff tm_hole := hn_hole

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
      simp [points]
      expose_names
      change IsNorm RedAff hole₁.coup
      intro ⟨_, h⟩
      cases h with
      | coup₀ h => exact hn_hole ⟨_, .sig₀ h⟩
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

@[dcc_reduce]
def Hole.unique {e e₁ e₂ : @EtaExpr.Norm τ_c} (h₁ : Hole e level e₁) (h₂ : Hole e level e₂) : e₁ = e₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  grind

def Hole.hole_same {α : @EtaExpr.Norm τ_c} (e_h₁ : Hole α level hole_tm₁) (e_h₂ : Hole α level hole_tm₂) : hole_tm₁ = hole_tm₂ := by
  have ha := e_h₁.complete
  have hb := e_h₂.complete
  grind

/-def Hole.quot_arr_one
  {f : @GenericExpr τ_c}
  {hn_f   : IsNorm RedAff f}
  {e_f    : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩]}
  (h      : Hole ⟨α.expr_to_eta, hn_α.to_eta⟩ lv ⟨hole₁, hn_hole₁⟩)
  (hrt    : RedAffNorm (DCC? (#(expr_to_eta f) hole₁)) ⟨e', hn_e'⟩)
  (hn_mem : ¬ e'.contains_hole)
  (heq    : eta_to_expr e' hn_mem = e'') : GenericExpr.arity (DCC? `(α, e'')) = 1 := by
  have h_arr_f : GenericExpr.arity f = 1 := by
    match e_f with
    | .tm₁ _ (_heq := heq) => exact heq
  have h_e'_mem₀ : (expr_to_eta f).mem_tm e' := by sorry
  have h_e'_mem  : f.mem_tm e'' := heq ▸ cast_mem_tm h_e'_mem₀
  simp [GenericExpr.arity]
  unfold GenericExpr.arity at h_arr_f
  split at h_arr_f
  case h_1 | h_2 | h_3 | h_4 | h_5 | h_6
    | h_7 | h_10 | h_11 | h_12 | h_24 | h_27 | h_31 => grind
  case h_8 | h_13 =>
    simp [mem_tm] at h_e'_mem
    cases h_e'_mem
    have h := hrt.push_head (by constructor)
    unfold eta_to_expr at heq
    simp at heq
    split at heq
    any_goals (grind)
    cases heq
    expose_names
    have h_size₀ := h_1.size_zero
    exact (h.size_absurd (by grind)).elim
  case h_9 =>
    expose_names
    have h_arr_eq' : x.arity = 0 := by grind
    have heq := (hrt.push_head .quot).elim_norm hn_f.to_eta.quot₀
    grind
  case h_14 | h_15 =>
    simp [mem_tm] at h_e'_mem
    cases h_e'_mem
    simp [expr_to_eta, mem_tm] at h_e'_mem₀
    cases h_e'_mem₀
    cases e_f with
    | tm₁ h =>
      cases h
      case _ =>
        cases h with
        | pure hn => exact (hn .coup).elim
        | coup _ h₁ _ h₂ =>
          have ha := h₁.is_norm
          have hb := h₂.is_norm
          have hc := h₁.arr_zero
          have hd := h₂.arr_zero
          have heq := ((hrt.push_head (by constructor)).elim_norm (by assumption))
          grind
  case h_16 =>
    simp [mem_tm] at h_e'_mem
    cases h_e'_mem
    have heq := hrt.elim_norm (fun ⟨_, h⟩ => by
      cases h with
      | congrFun h => exact hn_f.to_eta ⟨_, h⟩
      | congrArg h => exact hn_hole₁ ⟨_, h⟩)
    have h_mem := h.contains_hole
    grind
  case h_17 =>
    simp [mem_tm] at h_e'_mem
    simp [expr_to_eta] at hrt
    replace hrt := hrt.push_head (by constructor)
    cases e_f with
    | tm₁ h_dom =>
      cases h_dom
      case _ hrg h_dom_g =>
        match hrt with
        | ⟨hr, hn⟩ =>
          match hr.cases_head with
          | .inl h =>
            cases h
            have h_mem := h.contains_hole
            dcc_simp at heq
            grind
          | .inr ⟨_, h₁, h₂⟩ =>
            expose_names
            generalize heqa : f.expr_to_eta = f_1
            generalize heqb : g.expr_to_eta = g_1
            rw [heqa, heqb] at h₁
            cases h₁
            case congrFun h =>
              rw [← heqa] at h
              exact (hn_f.comp'l.to_eta ⟨_, h⟩).elim
            case congrArg h =>
              have h_pos := h_dom_g.arity_pos
              have e_f' : EtaFn ⟨g.expr_to_eta, hn_f.comp'r.to_eta⟩ [(mk α hn_α).to_eta] := by
                refine .tm₁ (_heq := ?_) h_dom_g.to_eta
                
                sorry
              sorry
            
            /-cases h₁ with
            | congrFun h => exact (hn_f.comp'l.to_eta ⟨_, h⟩).elim-/
    /-cases h_e'_mem with
    | inl heq' =>
      cases heq'
      simp [expr_to_eta] at hrt
      expose_names
      have heq_e'₁ : e' = (e'.eta_to_expr hn_mem).expr_to_eta := by dcc_simp
      have heq_e'₂ : e' = (f.comp' _g).expr_to_eta := by
        rw [heq_e'₁, heq]
      cases heq_e'₂
      have h_size := h.size_zero
      have heq' := hrt.size_zero (by grind)
      grind
    | inr h =>
      cases h with
      | inl heq' =>
        
        sorry
      | inr heq' =>
        sorry-/
  --generalize h_ar_eq : e''.arity = n
  -- simp arity to be e''.arity.succ
  -- generalize (arity e'') = n
  -- induction n
  -- split on f
  /-induction n generalizing f e' e'' with
  | zero => rfl
  | succ n ih =>-/
  sorry-/

/-def Hole.app_ar_dec
  {f    : @GenericExpr τ_c}
  {hn_f : IsNorm RedAff f}
  {e_f  : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩]}
  (h    : Hole ⟨α.expr_to_eta, hn_α.to_eta⟩ lv ⟨hole₁, hn_hole₁⟩)
  (hrt  : RedAffNorm (DCC? (#(expr_to_eta f) hole₁)) ⟨e', hn_e'⟩) : GenericExpr.arity e' ≤ arity ⟨f, hn_f⟩ := by
  have h_dec := e_f.decreasing
  cases e_f with
  | tm₁ h_dom =>
    cases h_dom
    case curr₂ =>
      expose_names
      have hrt' := hrt.push_head .curr
      match hrt' with
      | ⟨hr, hn⟩ =>
        match hr.cases_head with
        | .inl h =>
          cases h
          grind
        | .inr ⟨_, h₁, h₂⟩ =>
          have h_dec := h₁.decreasing
          sorry
    any_goals (simp_all [arity, GenericExpr.arity, NormExpr.raw])
    case sndc | fstc =>
      expose_names
      cases h with
      | pure hn => exact (hn .coup).elim
      | coup h_dom h₁ hrt' h₂ =>
        have heq := ((hrt.push_head (by constructor)).elim_norm (by assumption))
        have ha := h₁.arr_zero
        have hb := h₂.arr_zero
        grind
    case refl₂ =>
      simp [expr_to_eta] at hrt
      cases hrt.elim_norm (fun ⟨_, h⟩ => by
        cases h with
        | congrFun h =>
          cases h with
          | congrFun h => cases h
          | congrArg h => cases h
        | congrArg h =>
          exact hn_hole₁ ⟨_, h⟩)
      simp [GenericExpr.arity]
    case id =>
      cases (hrt.push_head .id).elim_norm (by assumption)
      have h := h.arr_zero
      grind
    case eql₂ =>
      simp [expr_to_eta] at hrt
      simp [expr_to_eta] at h
      cases h with
      | pure hn => exact (hn .bang).elim
      | bang h =>
        have h := (hrt.push_head .eql).elim_norm (fun ⟨_, h⟩ => by
          cases h with
          | eqr' h | eql' h =>
            expose_names
            exact hn_hole ⟨_, h⟩)
        cases h
        grind
    case unmap =>
      expose_names
      simp [expr_to_eta] at h
      cases h with
      | pure hn => exact (hn .bang).elim
      | bang h =>
        have h := hrt.push_head .unmap
        expose_names
        have h := h_1.app_ar_dec h (e_f := .tm₁ a (_heq := by grind))
        grind
    case unbox =>
      expose_names
      cases h with
      | pure hn => exact (hn .bang).elim
      | bang h =>
        have heq' := (hrt.push_head .unbox).elim_norm (by assumption)
        have h := h.arr_zero
        grind-/

namespace EtaFn

inductive ArgTy : (e_f : EtaFn (τ_c := τ_c) f doms)
  → {idx : Fin doms.length}
  → (args : Vector (@EtaExpr.Norm τ_c) (Fin.toNat idx)) → @EtaExpr.Norm τ_c → Type u
  | mk {e_f : EtaFn f doms} {idx : Fin doms.length}
    {args : Vector (@EtaExpr.Norm τ_c) (Fin.toNat idx)} :
    (hr : RedAffNorm ((args.map NormExpr.raw).foldl .app (to_eta_arr_same ▸ e_f.to_eta.vdoms)[↑ idx].raw) τ)
    → ArgTy e_f args τ
deriving DecidableEq

@[grind]
def get_arg_ty (e_f : EtaFn f doms) {idx : Fin e_f.arity}
  (args : Vector (@EtaExpr.Norm τ_c) (Fin.toNat idx)) : ((t : @EtaExpr.Norm τ_c) × ArgTy e_f args t) := by
  cases e_f; exact ⟨_, .mk (aff_sound rfl)⟩

def ArgTy.complete {e_f : EtaFn (τ_c := τ_c) f doms}
  {idx : Fin e_f.arity} {args : Vector (@EtaExpr.Norm τ_c) idx}
  (h : ArgTy (idx := idx) e_f args τ) : e_f.get_arg_ty args = ⟨τ, h⟩ :=
  match h with
  | .mk hrt => by
    rename_i τ₁
    unfold get_arg_ty
    cases e_f
    dsimp
    cases hrt.out_eq
    dsimp [red_aff]
    simp [hrt.eq]

instance ArgTy.instEtaRel {e_f : EtaFn f doms} {idx : Fin e_f.arity} : EtaRel
  (α := Vector (@EtaExpr.Norm τ_c) idx) (β := EtaExpr.Norm) (ArgTy e_f (idx := idx)) (m := Id)  where
  run := get_arg_ty (idx := idx) e_f
  complete := ArgTy.complete (idx := idx) (e_f := e_f) (doms := doms)

inductive Holes : (e_f : EtaFn (τ_c := τ_c) f doms)
  → (level : ℕ)
  → (holes : List (@EtaExpr.Norm τ_c)) → Type u
  | tm₁ {e_f : EtaFn f [α]} : (heq : NormExpr.to_eta α = α') → Hole α' level hole_e
    → Holes e_f level [hole_e]
deriving DecidableEq

@[dcc_size]
def Holes.length {f : @NormExpr τ_c RedAff} {doms : List (@NormExpr τ_c RedAff)}
  {e_f : EtaFn f doms} {holes : List (@EtaExpr.Norm τ_c)}
  (h : Holes e_f level holes) : holes.length = e_f.arity := by
  cases h; grind

@[inline, grind]
def Holes.v_elems {f : @NormExpr τ_c RedAff} {doms : List (@NormExpr τ_c RedAff)}
  {e_f : EtaFn f doms} {holes : List (@EtaExpr.Norm τ_c)}
  (h : Holes e_f level holes) : Vector (@EtaExpr.Norm τ_c) e_f.arity :=
  ⟨⟨holes⟩, h.length⟩

@[grind]
def Holes.app {f : @NormExpr τ_c RedAff} {doms : List (@NormExpr τ_c RedAff)}
  {e_f : EtaFn f doms} {holes : List (@EtaExpr.Norm τ_c)}
  (_h : Holes e_f level holes) : @EtaExpr τ_c :=
  ((holes.map NormExpr.raw).foldl GenericExpr.app f.to_eta.raw)

@[grind]
def Holes.app_reduce {e_f : EtaFn f doms} (_h : Holes e_f level holes) : ((e' : EtaExpr.Norm) ×
  (RedAffNorm ((holes.map NormExpr.raw).foldl GenericExpr.app f.to_eta.raw) e')) :=
  ⟨_, aff_sound rfl⟩


@[grind]
def Holes.Reduces {e_f : EtaFn (τ_c := τ_c) f doms} (_h : Holes e_f level holes) (B : EtaExpr.Norm (τ_c := τ_c)) : Type u :=
  (RedAffNorm ((holes.map NormExpr.raw).foldl GenericExpr.app f.to_eta.raw) B)

@[grind]
def Holes.fold {e_f : EtaFn (τ_c := τ_c) f doms} (on_f : @EtaExpr.Norm τ_c) (_h : Holes e_f level holes) : @EtaExpr.Norm τ_c :=
  let ⟨⟨τ₁, hn_τ⟩, h_arg⟩ := e_f.get_arg_ty (idx := ⟨0, e_f.arity_pos⟩) ⟨#[], by simp⟩
  red_aff <| (holes.map NormExpr.raw).foldl GenericExpr.app on_f.raw

@[grind]
def holes (e_f : EtaFn (τ_c := τ_c) f doms) (level : ℕ)
  : Option ((holes : List (@EtaExpr.Norm τ_c)) × Holes e_f level holes) := by
  cases e_f with
  | tm₁ h_dom =>
    rename_i α
    match α.to_eta.mk_hole level with
    | .some ⟨_, h⟩ => exact .some ⟨_, .tm₁ rfl h⟩
    | .none => exact .none

@[dcc_force_reduce, aesop safe apply (rule_sets := [DccForceReduce])]
def Holes.complete (h : Holes (τ_c := τ_c) e_f level hole_elems) : holes e_f level = .some ⟨hole_elems, h⟩ := by
  cases h with
  | tm₁ heq₁ h_hole =>
    rename_i e_f
    cases e_f with
    | tm₁ dom =>
      cases heq₁
      simp [holes, h_hole.complete]

@[dcc_force_reduce, aesop safe apply (rule_sets := [DccForceReduce])]
def Holes.unique (h₁ : Holes (τ_c := τ_c) e_f level hole_elems₁) (h₂ : Holes e_f level hole_elems₂) : hole_elems₁ = hole_elems₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all

def Holes.hole_mem_tm {f : @NormExpr τ_c RedAff} {doms : List (@NormExpr τ_c RedAff)} {e_f : EtaFn f doms}
  (h : Holes (τ_c := τ_c) e_f lv hole_tms) (i : Fin e_f.arity) : h.v_elems[i].raw.hole_mem_tm := by
  cases h with
  | tm₁ heq =>
    cases heq
    rename_i e_f hole h_hole
    simp [v_elems, h_hole.hole_mem_tm]

def Holes.points_norm {e_f : EtaFn f doms} {hole_elems : List (@EtaExpr.Norm τ_c)}
  (h : Holes e_f level hole_elems)
  (idx    : Fin e_f.arity)
  (b_idx  : Fin h.v_elems[idx].raw.point_arity) : IsNorm RedAff h.v_elems[idx].raw.points[b_idx] := by
  cases h with
  | tm₁ heq h_hole =>
    rename_i hole_e e_f
    cases e_f with
    | tm₁ =>
      match idx with
      | ⟨0, h_lt⟩ => exact h_hole.points_norm b_idx
      | ⟨n + 1, _⟩ => grind

def Holes.contains_hole₁ (h : Holes (τ_c := τ_c) e_f lv [hole₁]) : contains_hole hole₁.raw := by
  cases h with
  | tm₁ heq h => exact h.contains_hole

def Holes.arr_zero (h : Holes e_f lv [hole₁]) : NormExpr.arity hole₁ = 0 := by
  cases h with
  | tm₁ heq h =>
    induction h with
    | pure =>
      grind
    | bang =>
      grind
    | coup => grind

/-def Holes.app_ar_dec {e_f : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩]}
  (h : Holes (τ_c := τ_c) e_f lv [⟨hole₁, hn_hole₁⟩])
  (hrt : RedAffNorm (DCC? (#(expr_to_eta f) hole₁)) e') : arity e' ≤ arity ⟨f, hn_f⟩ := by
  cases e_f with
  | tm₁ h_dom =>
    cases h_dom
    case refl₁ | eql₁ =>
      cases hrt.elim_norm (fun ⟨_, h⟩ => by
        cases h with
        | congrFun h => cases h
        | congrArg h =>
          exact hn_hole₁ ⟨_, h⟩)
      simp [expr_to_eta, raw, arity, GenericExpr.arity]
    case refl₂ =>
      simp [expr_to_eta] at hrt
      cases hrt.elim_norm (fun ⟨_, h⟩ => by
        cases h with
        | congrFun h =>
          cases h with
          | congrFun h => cases h
          | congrArg h => cases h
        | congrArg h =>
          exact hn_hole₁ ⟨_, h⟩)
      simp [raw, arity, GenericExpr.arity]
    case id =>
      cases (hrt.push_head .id).elim_norm (by assumption)
      simp [raw, arity]
      have h := h.arr_zero
      grind
    case eql₂ =>
      simp [expr_to_eta] at hrt
      cases h with
      | tm₁ heq h =>
        simp [NormExpr.to_eta, expr_to_eta] at heq
        cases heq
        cases h with
        | pure hn => exact (hn .bang).elim
        | bang h =>
          have h := (hrt.push_head .eql).elim_norm (fun ⟨_, h⟩ => by
            cases h with
            | eqr' h | eql' h =>
              expose_names
              exact hn_hole ⟨_, h⟩)
          cases h
          grind
    case unmap =>
      expose_names
      simp [arity, raw, GenericExpr.arity] at _heq
      cases h with
      | tm₁ heq h =>
        simp [NormExpr.to_eta, expr_to_eta] at heq
        cases heq
        cases h with
        | pure hn => exact (hn .bang).elim
        | bang h =>
          have h := (hrt.push_head .unmap).congrFun hrn
          
          sorry-/

/-set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
def to_from_eta {f : @GenericExpr (@EtaConst τ_c)} {hn₂ : ¬ f.contains_hole} {hn_f : IsNorm RedAff f} {hn₃ : IsNorm (@RedAff τ_c) (f.eta_to_expr hn₂)}
  (h₁ : EtaFn ⟨f, hn_f⟩ doms₁) (h₂ : EtaFn ⟨(expr_to_eta (eta_to_expr f hn₂)), (IsNorm.to_eta hn₃)⟩ doms₂) : doms₂ = doms₁ := by
  have h := to_eta_right_inv hn₂
  have heq : h₁ ≍ h₂ := by
    cases h₁ with
    | tm₁ =>
      cases h₂ with
      | tm₁ =>
        have h_expr : (mk f hn_f) = (mk (f.eta_to_expr hn₂).expr_to_eta (IsNorm.to_eta hn₃)) :=
          NormExpr.ext (by
            simp [raw, h])
        expose_names
        rw [← h_expr] at h_dom_1
        have heq := h_dom.unique h_dom_1
        expose_names
        cases heq
        simp [h_dom.eq h_dom_1]
        sorry-/

end EtaFn

inductive EtaTm : (f : @NormExpr τ_c RedAff) → List (@NormExpr τ_c RedAff) → Type u
  | fn : EtaFn f doms → EtaTm f doms
  | pi : EtaTm ⟨DCC? (Π(f_α, f_β) x_α), hn⟩ []

@[grind]
def view_eta_tm (f : @NormExpr τ_c RedAff) : Option ((doms : List (@NormExpr τ_c RedAff)) × EtaTm f doms) :=
  match f.view_eta_fn with
  | .some ⟨_, h⟩ => .some ⟨_, .fn h⟩
  | .none =>
    match f with
    | ⟨DCC? (Π(_f_α, _f_β) _x_α), _hn⟩ => .some ⟨_, .pi⟩
    | _ => .none

def EtaTm.complete {f : @NormExpr τ_c RedAff} (h : EtaTm f doms) : view_eta_tm f = .some ⟨doms, h⟩ := by
  cases h with
  | fn h => simp [view_eta_tm, h.complete]
  | pi =>
    expose_names
    have hn₃ := EtaFn.none_complete
      (f := ⟨((f_α.pi f_β).app x_α), hn⟩)
      (fun e_f => by
        cases e_f with
        | tm₁ h => cases h)
    unfold view_eta_tm
    simp [hn₃]

def EtaTm.to_eta {f : @NormExpr τ_c RedAff} (h : EtaTm f doms) : EtaTm ⟨expr_to_eta f.raw, f.is_norm.to_eta⟩ (doms.map (·.to_eta)) := by
  cases h with
  | fn h => exact .fn h.to_eta
  | pi => exact .pi

def EtaTm.from_eta {f : @EtaExpr.Norm τ_c} (hn_mem : ¬ f.raw.contains_hole) {doms : List (@EtaExpr.Norm τ_c)}
  (e : EtaTm f doms) : EtaTm (f.from_eta hn_mem) (by
    cases e with
    | fn h =>
      cases h with
      | tm₁ h =>
        expose_names
        have h := h.no_holes (by grind)
        exact [α.from_eta h]
    | pi => exact []) := by
  cases e with
  | fn h => exact .fn (h.from_eta (by dcc_simp_all))
  | pi => exact .pi

def view_eta_tm_none_sound {f : @NormExpr τ_c RedAff} (h : view_eta_tm f = .none) : ∀ {doms}, EtaTm f doms → False := by
  intro _ h
  have h := h.complete
  grind

def EtaTm.none_complete {f : @NormExpr τ_c RedAff} (h : ∀ {doms}, EtaTm f doms → False) : view_eta_tm f = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨doms, e_f⟩
  exact (h e_f).elim

def EtaFn.holes_same {f : @NormExpr τ_c RedAff} (e_f₁ : EtaFn f doms) (e_f₂ : EtaFn g doms)
  (e_h₁ : e_f₁.Holes level holes₁) (e_h₂ : e_f₂.Holes level holes₂) : holes₁ = holes₂ := by
  cases e_h₁ with
  | tm₁ heqa h₁ =>
    cases e_h₂ with
    | tm₁ heqb h₂ =>
      expose_names
      rw [← heqa] at h₁
      rw [← heqb] at h₂
      simp [h₁.hole_same h₂]

end NormExpr
