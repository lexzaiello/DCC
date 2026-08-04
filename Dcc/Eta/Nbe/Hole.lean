import Dcc.Eta.Ast
import Dcc.Eta.View
import Dcc.Eta.Reflect
import Dcc.Ast.Points
import Dcc.Eta.Nbe.Domain
import Mathlib.Data.List.Defs

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

namespace NormExpr

def from_eta {f : @GenericExpr (@EtaConst τ_c)} {hn : GenericExpr.IsNorm GenericExpr.RedAff f} (hn_hole : ¬ f.contains_hole) : @NormExpr τ_c GenericExpr.RedAff :=
  ⟨f.eta_to_expr hn_hole, hn.from_eta hn_hole⟩

def from_eta' (f : @NormExpr (@EtaConst τ_c) GenericExpr.RedAff) (hn : ¬ GenericExpr.contains_hole f.raw) : @NormExpr τ_c GenericExpr.RedAff :=
  from_eta hn (hn := f.is_norm)

/-
An η-reducible function is in normal form, has an arity of 1 or 2, and has known domain
-/
open GenericExpr

inductive EtaFn : (f : @NormExpr τ_c RedAff) → List (@NormExpr τ_c RedAff) → Type u
  | tm₁  : {f : @NormExpr τ_c RedAff} → {_heq : arity f = 1} → (h_dom : Domain f α)    → EtaFn f [α]
  | tm₂  : {f : @NormExpr τ_c RedAff} → {_heq : arity f = 2} → (h_dom : Domain₂ f α β) → EtaFn f [α, β]

def EtaFn.to_eta {f : @GenericExpr τ_c} {hn : IsNorm RedAff f} (e : EtaFn ⟨f, hn⟩ doms) : EtaFn (mk f hn).to_eta (doms.map (·.to_eta)) := by
  cases e with
  | tm₁ h_dom => expose_names; exact .tm₁ h_dom.to_eta (_heq := arity_eta _heq)
  | tm₂ h_dom => expose_names; exact .tm₂ h_dom.to_eta (_heq := arity_eta _heq)

def EtaFn.from_eta {f : @GenericExpr (@EtaConst τ_c)} {hn : IsNorm RedAff f} (hn_mem : ¬ f.contains_hole) {doms : List (@EtaExpr.Norm τ_c)}
  (e : EtaFn ⟨f, hn⟩ doms)
  (hn_doms : List.Forall (¬ ·.raw.contains_hole) doms)
  : EtaFn ⟨f.eta_to_expr hn_mem, hn.from_eta hn_mem⟩ (doms.attach.map (fun ⟨x, h⟩ => x.from_eta' (by sorry))) := by
  simp
  cases e with
  | tm₁ =>
    expose_names
    simp at hn_doms
    exact .tm₁ (by
      simp
      sorry) (_heq :=
      arity_from_eta' (by
        dcc_simp
        exact _heq))
  | tm₂ =>
    expose_names
    simp at hn_doms
    
    sorry

@[dcc_size]
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
  | .tm₂ h => by grind

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
def EtaFn.head_dom (e_f : EtaFn f doms) : ((τ : @NormExpr τ_c RedAff) × (Domain f τ)) :=
  match e_f with
  | .tm₁ h_dom => ⟨_, h_dom⟩
  | .tm₂ h_dom => ⟨_, h_dom.to_domain⟩

@[grind]
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
  else .none

def EtaFn.complete {f : @NormExpr τ_c RedAff} {doms : List (@NormExpr τ_c RedAff)} (h : EtaFn f doms) : view_eta_fn f = .some ⟨doms, h⟩ := by
  induction h with
  | tm₂ h_dom | tm₁ h_dom => simp_all [view_eta_fn, h_dom.complete]

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
  | tm₂ =>
    cases h₂ with
    | tm₂ =>
      expose_names
      cases h_dom.eq h_dom_1; rfl

open GenericExpr

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
deriving DecidableEq

def Hole.contains_hole (h : Hole (τ_c := τ_c) α lv hole_e) : hole_e.raw.contains_hole := by
  induction h <;> grind

def Hole.hole_mem_tm (h : Hole (τ_c := τ_c) α lv hole_e) : hole_e.raw.hole_mem_tm := by
  induction h <;> grind

def Hole.sigl_hole_mem_tm (h : Hole (τ_c := τ_c) α lv ⟨(DCC? (⟦β⟧(a, b))), hn⟩) : a.hole_mem_tm := by
  cases h with
  | coup _ ha _ _ => exact ha.hole_mem_tm

def Hole.sigl_hole_mem_tm_box (h : Hole (τ_c := τ_c) α lv ⟨(DCC? &(⟦β⟧(a, b))), hn⟩) : a.hole_mem_tm := by
  cases h with
  | bang h =>
    exact h.sigl_hole_mem_tm

def Hole.sigr_hole_mem_tm (h : Hole (τ_c := τ_c) α lv ⟨(DCC? (⟦β⟧(a, b))), hn⟩) : b.hole_mem_tm := by
  cases h with
  | coup _ _ _ ha => exact ha.hole_mem_tm

def Hole.sigr_hole_mem_tm_box (h : Hole (τ_c := τ_c) α lv ⟨(DCC? &(⟦β⟧(a, b))), hn⟩) : b.hole_mem_tm := by
  cases h with
  | bang h =>
    exact h.sigr_hole_mem_tm

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
def Hole.coup_points_neq (h : Hole ⟨(DCC? Coup(β)), hn⟩ level ⟨(DCC? ⟦β⟧(a, b)), hn_hole⟩) : a ≠ b := fun heq => by
  cases h with
  | coup h_dom h_hole₁ hrt h_hole₂ =>
    cases heq
    exact h_hole₁.level_neq h_hole₂ (by grind) (by grind)

def Hole.bang_coup_points_neq (h : Hole ⟨(DCC? !(Coup(β))), hn⟩ level ⟨(DCC? &(⟦β⟧(a, b))), hn_hole⟩) : a ≠ b := fun heq => by
  cases h with
  | bang h =>
    have h := h.coup_points_neq
    grind

@[dcc_size]
def Hole.size_zero (h : Hole α level hole_e) : hole_e.size = 0 := by
  induction h <;> grind

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

@[dcc_reduce]
def Hole.unique {e e₁ e₂ : @EtaExpr.Norm τ_c} (h₁ : Hole e level e₁) (h₂ : Hole e level e₂) : e₁ = e₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  grind

namespace EtaFn

inductive ArgTy : (e_f : EtaFn (τ_c := τ_c) f doms)
  → {idx : Fin (arity f.to_eta)}
  → (args : Vector (@EtaExpr.Norm τ_c) (Fin.toNat idx)) → @EtaExpr.Norm τ_c → Type u
  | mk {e_f : EtaFn f doms} {idx : Fin (arity f.to_eta)}
    {args : Vector (@EtaExpr.Norm τ_c) (Fin.toNat idx)} :
    (hr : RedAffNorm ((args.map NormExpr.raw).foldl .app e_f.to_eta.vdoms[↑ idx].raw) τ)
    → ArgTy e_f args τ
deriving DecidableEq

@[grind]
def get_arg_ty (e_f : EtaFn f doms) {idx : Fin (arity f.to_eta)}
  (args : Vector (@EtaExpr.Norm τ_c) (Fin.toNat idx)) : ((t : @EtaExpr.Norm τ_c) × ArgTy e_f args t) := by
  cases e_f <;> exact ⟨_, .mk (aff_sound rfl)⟩

def ArgTy.complete {e_f : EtaFn (τ_c := τ_c) f doms}
  {idx : Fin (arity f.to_eta)} {args : Vector (@EtaExpr.Norm τ_c) idx}
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

instance ArgTy.instEtaRel {e_f : EtaFn f doms} {idx : Fin (arity f.to_eta)} : EtaRel
  (α := Vector (@EtaExpr.Norm τ_c) idx) (β := EtaExpr.Norm) (ArgTy e_f (idx := idx)) (m := Id)  where
  run := get_arg_ty (idx := idx) e_f
  complete := ArgTy.complete (idx := idx) (e_f := e_f) (doms := doms)

inductive Holes : (e_f : EtaFn (τ_c := @EtaConst τ_c) f doms)
  → (level : ℕ)
  → (holes : List (@EtaExpr.Norm τ_c)) → Type u
  | tm₁ {e_f : EtaFn f [α]} : Hole α level hole_e
    → Holes e_f level [hole_e]
  | tm₂ {e_f : EtaFn f [α, ⟨β₀, h_n_β⟩]} : Hole α (level + 2) ⟨hole₁, hn_hole₁⟩
    → RedAffNorm (DCC? (β₀ hole₁)) β
    → Hole β (level + 1) hole₂
    → Holes e_f level [⟨hole₁, hn_hole₁⟩, hole₂]
deriving DecidableEq

@[dcc_size]
def Holes.length {f : @EtaExpr.Norm τ_c} {doms : List (@EtaExpr.Norm τ_c)}
  {e_f : EtaFn f doms} {holes : List (@EtaExpr.Norm τ_c)}
  (h : Holes e_f level holes) : holes.length = (arity f) := by
  have h_size := e_f.length
  cases h <;> grind

@[inline, grind]
def Holes.v_elems {f : @EtaExpr.Norm τ_c} {doms : List (@EtaExpr.Norm τ_c)}
  {e_f : EtaFn f doms} {holes : List (@EtaExpr.Norm τ_c)}
  (h : Holes e_f level holes) : Vector (@EtaExpr.Norm τ_c) (arity f) :=
  ⟨⟨holes⟩, h.length⟩

@[grind]
def Holes.app {f : @EtaExpr.Norm τ_c} {doms : List (@EtaExpr.Norm τ_c)}
  {e_f : EtaFn f doms} {holes : List (@EtaExpr.Norm τ_c)}
  (_h : Holes e_f level holes) : @EtaExpr τ_c :=
  ((holes.map NormExpr.raw).foldl GenericExpr.app f.raw)

@[grind]
def Holes.app_reduce {e_f : EtaFn f doms} (_h : Holes e_f level holes) : ((e' : EtaExpr.Norm) ×
  (RedAffNorm ((holes.map NormExpr.raw).foldl GenericExpr.app f.raw) e')) :=
  ⟨_, aff_sound rfl⟩


@[grind]
def Holes.Reduces {e_f : EtaFn (τ_c := (@EtaConst τ_c)) f doms} (_h : Holes e_f level holes) (B : EtaExpr.Norm (τ_c := τ_c)) : Type u :=
  (RedAffNorm ((holes.map NormExpr.raw).foldl GenericExpr.app f.raw) B)

@[grind]
def Holes.fold {e_f : EtaFn (τ_c := (@EtaConst τ_c)) f doms} (on_f : @EtaExpr.Norm τ_c) (_h : Holes e_f level holes) : @EtaExpr.Norm τ_c :=
  let ⟨⟨τ₁, hn_τ⟩, h_arg⟩ := e_f.get_arg_ty (idx := ⟨0, e_f.to_eta.arity_pos⟩) ⟨#[], by simp⟩
  red_aff <| (holes.map NormExpr.raw).foldl GenericExpr.app on_f.raw

@[grind]
def holes (e_f : EtaFn (τ_c := @EtaConst τ_c) f doms) (level : ℕ)
  : Option ((holes : List (@EtaExpr.Norm τ_c)) × Holes e_f level holes) := by
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

@[dcc_force_reduce, aesop safe apply (rule_sets := [DccForceReduce])]
def Holes.unique (h₁ : Holes (τ_c := τ_c) e_f level hole_elems₁) (h₂ : Holes e_f level hole_elems₂) : hole_elems₁ = hole_elems₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all

def Holes.hole_mem_tm {f : @EtaExpr.Norm τ_c} {doms : List (@EtaExpr.Norm τ_c)} {e_f : EtaFn f doms}
  (h : Holes (τ_c := τ_c) e_f lv hole_tms) (i : Fin (arity f)) : h.v_elems[i].raw.hole_mem_tm := by
  cases h with
  | tm₁ =>
    rename_i e_f hole h_hole
    simp [v_elems, h_hole.hole_mem_tm]
  | tm₂ =>
    rename_i e_f _ h_hole₁ h_hole₂
    cases e_f with
    | tm₂ =>
      simp [v_elems]
      rename_i _heq _
      match i with
      | ⟨0, h⟩ => simp_all [h_hole₁.hole_mem_tm]
      | ⟨1, h⟩ => simp_all [h_hole₂.hole_mem_tm]
      | ⟨n + 2, h⟩ => grind

def Holes.points_norm {e_f : EtaFn f doms} {hole_elems : List (@EtaExpr.Norm τ_c)}
  (h : Holes e_f level hole_elems)
  (idx    : Fin (arity f))
  (b_idx  : Fin h.v_elems[idx].raw.point_arity) : IsNorm RedAff h.v_elems[idx].raw.points[b_idx] := by
  cases h with
  | tm₁ h_hole =>
    rename_i hole_e e_f
    cases e_f with
    | tm₁ =>
      match idx with
      | ⟨0, h_lt⟩ => exact h_hole.points_norm b_idx
      | ⟨n + 1, _⟩ => grind
  | tm₂ h_hole₁ _ h_hole₂ =>
    match idx with
    | ⟨1, h_lt⟩ => exact h_hole₂.points_norm b_idx
    | ⟨0, h_lt⟩ => exact h_hole₁.points_norm b_idx
    | ⟨n + 2, _⟩ => grind

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
    have h_ar : ((f_α.pi f_β).app x_α).arity = 0 := by
      grind
    simp [view_eta_tm, view_eta_fn, arity, raw, h_ar]

def view_eta_tm_none_sound {f : @NormExpr τ_c RedAff} (h : view_eta_tm f = .none) : ∀ {doms}, EtaTm f doms → False := by
  intro _ h
  have h := h.complete
  grind

def EtaTm.none_complete {f : @NormExpr τ_c RedAff} (h : ∀ {doms}, EtaTm f doms → False) : view_eta_tm f = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨doms, e_f⟩
  exact (h e_f).elim

end NormExpr
