import Dcc.Ast.Points
import Dcc.Aff.Red

variable {τ_c : Type u}

namespace GenericExpr

inductive ViewEta : GenericExpr τ_c → Type u
  | pi_type : ViewEta (DCC? (Π(f_α, f_β) env))
  | pi      : ViewEta (DCC? Π(f_α, f_β))
  | pi_comp : ViewEta (DCC? (Π(f_α, f_β) ∘ g))
  | coup    : ViewEta (DCC? Coup(β))
  | bang    : ViewEta (DCC? !(β))
  | eq      : ViewEta (DCC? x = y)
deriving DecidableEq

@[grind, dcc_rel]
def view_eta? (e : GenericExpr τ_c) : Option (ViewEta e) :=
  match e with
  | (DCC? (Π(_f_α, _f_β) _env))  => .some (.pi_type)
  | (DCC? Π(_f_α, _f_β))         => .some .pi
  | (DCC? (Π(_f_α, _f_β) ∘ _g)) => .some .pi_comp
  | (DCC? Coup(_β))              => .some .coup
  | (DCC? !(_β))                 => .some .bang
  | (DCC? _x = _y)               => .some .eq
  | _ => .none

@[grind ., grind =_]
theorem ViewEta.complete (h : ViewEta e) : view_eta? e = .some h := by
  cases h <;> simp [view_eta?]

@[grind =, grind =_]
theorem ViewEta.complete_none (h : ViewEta e → False) : view_eta? e = .none := by
  unfold view_eta?
  split <;> (
    first
    | exact (h (by constructor)).elim
    | grind)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_eta?_none_sound (h : view_eta? e = .none) : ViewEta e → False := fun h => by
  simp_all [h.complete]

inductive ViewCoupBang : GenericExpr τ_c → Type u
  | coup    : ViewCoupBang (DCC? Coup(β))
  | bang    : ViewCoupBang (DCC? !(Coup(β)))
deriving DecidableEq

@[grind, dcc_rel]
def view_coup_bang? (e : GenericExpr τ_c) : Option (ViewCoupBang e) :=
  match e with
  | (DCC? Coup(_β)) => .some .coup
  | (DCC? !(Coup(_α)))    => .some .bang
  | _ => .none

@[grind =_, grind .]
theorem ViewCoupBang.complete (h : ViewCoupBang e) : view_coup_bang? e = .some h := by
  cases h <;> simp [view_coup_bang?]

@[grind =, grind =_]
theorem ViewCoupBang.complete_none (h : ViewCoupBang e → False) : view_coup_bang? e = .none := by
  unfold view_coup_bang?
  split <;> (
    first
    | exact (h (by constructor)).elim
    | grind)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_coup_bang?_none_sound (h : view_coup_bang? e = .none) : ViewCoupBang e → False := fun h => by
  simp_all [h.complete]

inductive ViewBangCoup : GenericExpr τ_c → Type u
  | coup    : ViewBangCoup (DCC? Coup(β))
  | bang    : ViewBangCoup (DCC? !(α))
deriving DecidableEq

@[grind, dcc_rel]
def view_bang_coup? (e : GenericExpr τ_c) : Option (ViewBangCoup e) :=
  match e with
  | (DCC? Coup(_β)) => .some .coup
  | (DCC? !(_α))    => .some .bang
  | _ => .none

@[grind =_, grind .]
theorem ViewBangCoup.complete (h : ViewBangCoup e) : view_bang_coup? e = .some h := by
  cases h <;> simp [view_bang_coup?]

@[grind =, grind =_]
theorem ViewBangCoup.complete_none (h : ViewBangCoup e → False) : view_bang_coup? e = .none := by
  unfold view_bang_coup?
  split <;> (
    first
    | exact (h (by constructor)).elim
    | grind)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_bang_coup?_none_sound (h : view_bang_coup? e = .none) : ViewBangCoup e → False := fun h => by
  simp_all [h.complete]

inductive Hole : (α : GenericExpr τ_c) → (lv : ℕ) → (hole_e : GenericExpr τ_c) → Type u
  | pure : (ViewBangCoup α → False)
    → Hole α lv (.hole lv)
  | coup : (hrt : RedAffNorm (DCC? Dom(β)) ⟨α, hn_α⟩)
    → Hole α (lv + 1) hole₁
    → RedAffNorm (DCC? (β hole₁)) ⟨τ_snd, hn_τ_snd⟩
    → Hole τ_snd lv hole₂
    → Hole (DCC? Coup(β)) lv (DCC? ⟦hole₁⟧(hole₁, hole₂))
  | bang : Hole α lv hole₁ → Hole (DCC? !(α)) lv (DCC? &(hole₁))
deriving DecidableEq

@[dcc_size]
def Hole.size_zero (h : Hole α level hole_e) : hole_e.size = 0 := by
  induction h <;> grind

def Hole.is_norm (e_h : Hole α level hole_e) : IsNorm RedAff hole_e := fun ⟨_, h⟩ => by
  have ha := e_h.size_zero
  have hb := h.decreasing
  grind

/-
Since hole lvs are initialized with the maximum hole, the preimage does not contain the hole
Use this to initialize hole in Canonicalize.
-/

@[grind]
def mk_hole (τ : @GenericExpr τ_c) (lv : ℕ) : ((hole_e : @GenericExpr τ_c) × Hole τ lv hole_e) :=
  if h_coup_some : τ.view_bang_coup?.isSome then
    match τ, τ.view_bang_coup?.get h_coup_some with
    | DCC? Coup(β), .coup =>
      have h_dec₀ : size (DCC? Dom(β)) < size (DCC? Coup(β)) := by grind
      have h_dec₁ := decreasing? _ (reduce RedAff (DCC? Dom(β))).snd.down
      let ⟨hole₁, h_hole₁⟩ := (reduce RedAff (DCC? Dom(β))).fst.mk_hole (lv + 1)
      have h_size_eq := h_hole₁.size_zero
      have h_dec₁ : (β.app hole₁).red_aff.size ≤ (β.app hole₁).size := by
        grind
      have h_dec₂ : (reduce RedAff (β.app hole₁)).fst.size < β.coup.size := by grind
      let ⟨hole₂, h_hole₂⟩ := (reduce RedAff (DCC? (β hole₁))).fst.mk_hole lv
      ⟨_, .coup ⟨(reduce RedAff (DCC? Dom(β))).snd.down, reduce_norm rfl⟩ h_hole₁ ⟨(reduce RedAff (DCC? (β hole₁))).snd.down, reduce_norm rfl⟩ h_hole₂⟩
    | DCC? !(α), .bang =>
      have h_dec₃ : α.size < (DCC? !(α)).size := by grind
      ⟨_, .bang (α.mk_hole lv).snd⟩
  else
    ⟨_, .pure (τ.view_bang_coup?_none_sound (by simp_all))⟩
termination_by τ.size

@[aesop safe apply (rule_sets := [DccSize]), aesop safe destruct (rule_sets := [DccForceReduce])]
def Hole.complete (h : Hole α lv hole_e) : mk_hole α lv = ⟨hole_e, h⟩ := by
  induction h with
  | pure hn =>
    unfold mk_hole
    simp [GenericExpr.ViewBangCoup.complete_none hn]
  | bang h_hole heq =>
    unfold mk_hole
    simp [GenericExpr.view_bang_coup?, heq]
    grind
  | coup h_dom h_hole₁ hr₁ h_hole₂ heq₁ heq₂ =>
    unfold mk_hole
    have heq₁a := (Sigma.ext_iff.mp heq₁).left
    have heq₂a := (Sigma.ext_iff.mp heq₂).left
    have heq₁b := (Sigma.ext_iff.mp heq₁).right
    have heq₂b := (Sigma.ext_iff.mp heq₂).right
    simp at heq₁a
    simp at heq₂a
    simp at heq₁b
    simp at heq₂b
    have hc := h_dom.complete_fst
    have hd := hr₁.complete_fst
    simp [view_bang_coup?]
    cases hc
    cases hd
    cases heq₁a
    cases heq₂a
    constructor
    · constructor <;> rfl
    · congr!
      · simp [(h_dom.out_eq ▸ h_dom).eq]
        grind
      · grind
      · simp [(hr₁.out_eq ▸ hr₁).eq]
        grind
      · grind

@[dcc_force_reduce]
def Hole.complete_fst (h : Hole α lv hole_e) : hole_e = (mk_hole α lv).fst := by
  dcc_aesop' [force_reduce]

@[dcc_force_reduce, aesop unsafe 50% destruct (rule_sets := [DccForceReduce])]
def Hole.complete_snd (h : Hole α lv (mk_hole α lv).fst) : h = (mk_hole α lv).snd := by
  have h := h.complete
  have h := Sigma.ext_iff.mp h
  cases h.right
  rfl

@[dcc_force_reduce]
def Hole.unique (h₁ : Hole A lv hole₁) (h₂ : Hole A lv hole₂): hole₁ = hole₂ := by
  dcc_aesop' [force_reduce]

theorem Hole.min_hole (h : Hole α lv hole₁) : GenericExpr.min_hole hole₁ = lv := by
  induction h <;> grind

theorem Hole.max_hole (h : Hole α lv hole₁) : lv ≤ GenericExpr.max_hole hole₁ := by
  induction h <;> grind

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
      cases h.left; cases h.right
      exact ih₁ h_hole₂ (by grind) rfl
    | bang =>
      rename_i ih₁ ih₂ _ _ h_hole₂
      exact ih₁ (by assumption) (by grind) rfl

def Hole.coup_points_neq (h : Hole A level (DCC? ⟦β⟧(a, b))) : a ≠ b := fun heq => by
  cases h with
  | coup h_dom h_hole₁ hrt h_hole₂ =>
    cases heq
    exact h_hole₁.level_neq h_hole₂ (by grind) (by grind)

@[grind ., grind! .]
theorem min_hole_le_max_hole : min_hole e ≤ max_hole e := by
  induction e <;> grind

@[grind ., grind →]
theorem RedAff.max_hole_preserved (h : RedAff A B) : max_hole B ≤ max_hole A := by
  induction h <;> grind

@[grind ., grind →]
theorem RedAffReflTrans.max_hole_preserved (h : RedAffReflTrans A B) : B.max_hole ≤ A.max_hole :=
  match h.cases_head with
  | .inl h => by grind
  | .inr ⟨_, h₁, h₂⟩ => by
    have h_dec := h₁.decreasing
    have h_dec₂ := h₁.max_hole_preserved
    have h_dec₃ := max_hole_preserved h₂
    grind
termination_by A.size

@[aesop safe forward (rule_sets := [DccSize])]
def RedAffNorm.max_hole_preserved (h : RedAffNorm A ⟨B, hn_B⟩) : max_hole B ≤ max_hole A := by
  match h with
  | ⟨hr, hn⟩ =>
    match hr.cases_head with
    | .inl h =>
      cases h
      grind
    | .inr ⟨_, h₁, h₂⟩ =>
      have h_dec := h₁.decreasing
      have ha := h₁.max_hole_preserved
      have hb := max_hole_preserved ⟨h₂, hn⟩
      grind
termination_by A.size

end GenericExpr
