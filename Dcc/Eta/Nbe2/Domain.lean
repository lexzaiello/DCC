import Dcc.Eta.Nbe2.Hole
import Dcc.Eta.Nbe2.RedSpine

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

inductive Domain : GenericExpr τ_c → GenericExpr τ_c → Type u
  | mk : RedAffNorm (DCC? Dom(x)) ⟨τ, hn_τ⟩ → Domain x τ
deriving Repr

@[grind ., grind →]
theorem RedAff.dom_decreasing (h : RedAff (DCC? Dom(x)) τ) (hneq : ∀ ⦃y⦄, τ ≠ (DCC? Dom(y))) : τ.size < x.size := by
  cases h
  any_goals (grind)

theorem RedAff.IsHead.spine_dom_decreasing (hr : RedAff (DCC? (f x)) B) (hn : hr.IsHead) (h_dom : RedAff (DCC? Dom(f)) τ) : τ.size < f.size := by
  cases hn <;> grind

theorem RedAff.IsHead.spine_dom_decreasing' (hr : RedAff (DCC? (f x)) B) (hn : hr.IsHead) (h_dom : Domain f τ) : τ.size < f.size :=
  match h_dom with
  | ⟨⟨hr', hn'⟩⟩ =>
    match hr'.cases_head with
    | .inl h => by
      cases h
      cases hn
      any_goals (exact (hn' ⟨_, (by constructor)⟩).elim)
    | .inr ⟨_, h₁, h₂⟩ => by
      have h := hn.spine_dom_decreasing hr h₁
      have h_dec' := h₁.decreasing
      grind

theorem RedSpinePlus.dom_decreasing (hr : RedSpinePlus (DCC? (f x)) B) (h_dom : Domain f τ) : τ.size < f.size :=
  match hr with
  | .single hr hn => hn.spine_dom_decreasing' hr h_dom
  | .head hr hn _hrt => hn.spine_dom_decreasing' hr h_dom

theorem RedSpineNorm.dom_decreasing (hr : RedSpineNorm (DCC? (f x)) B) (h_dom : Domain f τ) : τ.size < f.size :=
  match hr with
  | ⟨hr, _⟩ => hr.dom_decreasing h_dom

def Domain.decreasing_neq (h : Domain x τ) (hneq : ∀ ⦃y⦄, τ ≠ (DCC? Dom(y))) : τ.size < x.size :=
  match h with
  | ⟨⟨hr, hn⟩⟩ => by
    match hr.cases_head with
    | .inl h => grind
    | .inr ⟨_, h₁, h₂⟩ => grind

def Domain.is_norm (h : Domain α τ) : IsNorm RedAff τ :=
  match h with
  | ⟨_, hn⟩ => hn

@[grind, dcc_force_reduce, aesop unsafe norm (rule_sets := [DccForceReduce])]
def domain (e : GenericExpr τ_c) : ((τ : GenericExpr τ_c) × Domain e τ) :=
  ⟨_, ⟨aff_sound' (DCC? Dom(e))⟩⟩

@[dcc_force_reduce, aesop unsafe 50% forward (rule_sets := [DccForceReduce])]
def Domain.complete (h : Domain e τ) : domain e = ⟨τ, h⟩ :=
  match h with
  | ⟨hr⟩ => by
    have h := (hr.out_eq ▸ hr).eq
    simp [domain]
    grind

@[dcc_force_reduce, aesop unsafe 50% apply (rule_sets := [DccForceReduce])]
def Domain.complete_fst (h : Domain e τ) : (domain e).fst = τ := by
  have h := h.complete
  grind

@[dcc_force_reduce, aesop unsafe 50% forward (rule_sets := [DccForceReduce])]
def Domain.complete_snd (h : Domain e e.domain.fst) : h = e.domain.snd := by
  dcc_aesop' [force_reduce]

@[dcc_force_reduce, aesop safe apply (rule_sets := [DccForceReduce])]
def Domain.complete_snd' (h : Domain e A) : h ≍ e.domain.snd := by
  cases h.complete_fst
  simp [h.complete_snd]

theorem Domain.max_hole_preserved (h : Domain x A) : A.max_hole ≤ x.max_hole :=
  match h with
  | ⟨⟨hr, _hn⟩⟩ => hr.max_hole_preserved

@[inline, dcc_force_reduce, aesop unsafe 50% destruct (rule_sets := [DccForceReduce])]
def domain_fst_sound (h : (domain x).fst = A) : Domain x A :=
  ⟨reduce_sound_fst h, reduce_norm_fst h⟩

@[aesop unsafe 50% destruct (rule_sets := [DccForceReduce])]
def Domain.unique (h₁ : Domain x A) (h₂ : Domain x B) : A = B := by
  dcc_aesop' [force_reduce]

@[aesop unsafe 50% destruct (rule_sets := [DccForceReduce])]
def Domain.eq (h₁ h₂ : Domain x A) : h₁ = h₂ :=
  match h₁ with
  | ⟨hrt₁, hn₁⟩ =>
    match h₂ with
    | ⟨hrt₂, hn₂⟩ => by
      grind

def Domain.red (h : Domain x A) : RedAffReflTrans (DCC? Dom(x)) A :=
  match h with
  | ⟨hr, _⟩ => hr

instance : Subsingleton (Domain x A) := ⟨fun x y => by dcc_aesop' [force_reduce]⟩

def Domain.eq' (h : Domain x A) : x.domain.fst = A := by
  have h := h.complete_fst
  grind

def Domain.map : Domain (DCC? !<x>) x.domain.fst.bang :=
  have h_dom' := (domain_fst_sound (x := x) rfl).red
  have hn     := (domain_fst_sound (x := x) rfl).is_norm
  ⟨.trans (.single .mapτ₀) (aff_mk_point' (n := 0) h_dom'), fun ⟨_, .bang₀ h⟩ => hn ⟨_, h⟩⟩

def Domain.fmap : Domain (DCC? $<x>) x.domain.fst.bang :=
  have h_dom' := (domain_fst_sound (x := x) rfl).red
  have hn     := (domain_fst_sound (x := x) rfl).is_norm
  ⟨.trans (.single .fmapτ₀) (aff_mk_point' (n := 0) h_dom'), fun ⟨_, .bang₀ h⟩ => hn ⟨_, h⟩⟩

def Domain.unbox : Domain (DCC? *(A)) (reduce RedAff A).fst.bang :=
  have hn := reduce_norm (A := A) rfl
  ⟨.trans (.single .unboxτ₀) (aff_mk_point' (n := 0) (reduce RedAff A).snd.down), fun ⟨_, .bang₀ h⟩ => hn ⟨_, h⟩⟩

set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
def reduce_congr_point {x : GenericExpr τ} (h : point_arity x = 1 := by grind) (hlt : 0 < point_arity x := by grind) : (reduce RedAff x).fst = x.set_points (x.points.set (Fin.mk 0 hlt) (reduce RedAff x.points[0]).fst) := by
  have hrt_point := reduce_sound (r := RedAff) (A := x.points[0]) rfl
  have hn_point  := reduce_norm (r := RedAff) (A := x.points[0]) rfl
  have hrt := aff_mk_point' (n := 0) (e := x) (x := x.points[0]) (y := (reduce RedAff x.points[0]).fst) hrt_point
  have hn' := mk_inner_norm (e := (x.set_points (x.points.set (Fin.mk 0 hlt) (reduce RedAff x.points[0]).fst (reduce_congr_point._proof_1 h))))
    (by
      have h := congr_point_arr (e := x) (p := (Fin.mk 0 hlt)) (p' := (reduce RedAff x.points[0]).fst)
      grind)
    (hrn := by
      unfold List.Forall
      unfold point_arity at h
      simp at h
      split at h
      any_goals (grind))
  have heq' := reduce_complete_fst hrt hn'
  unfold point_arity at h
  simp at h
  split at h
  any_goals (grind)

def Domain.eval : Domain (DCC? Eval(A, B, x)) (DCC? Coup(#((reduce RedAff B).fst))) := by
  have h_dom : Domain (DCC? Eval(A, B, x)) _ := ⟨.trans (.single .evalcτ₀) (reduce_sound rfl), reduce_norm rfl⟩
  have heq := reduce_congr_point (x := B.coup) ▸ h_dom
  dcc_simp at heq
  exact heq

def Domain.curr₁ : Domain (DCC? (Λ(A, B, x) y)) (reduce RedAff (DCC? (Uncoup(Dom(x)) y))).fst :=
  ⟨.trans (.single .currτ₁) (reduce_sound rfl), reduce_norm rfl⟩

def Domain.curr'₁ : Domain (DCC? (!Λ(A, B, x) &(y))) (reduce RedAff (DCC? (Uncoup(Unbang(Dom(x))) y))).fst.bang := by
  have h_dom : Domain (DCC? (!Λ(A, B, x) &(y))) _ := ⟨.trans (.single .curr'τ₁) (reduce_sound rfl), reduce_norm rfl⟩
  have heq := reduce_congr_point (x := (x.dom.unbang.uncoup.app y).bang) ▸ h_dom
  dcc_simp at heq
  exact heq

def Domain.eql₁ : Domain (DCC? (Eql(B) &(y))) (reduce RedAff (DCC? (B y))).fst.bang := by
  have h_dom : Domain (DCC? (Eql(B) &(y))) _ := ⟨.trans (.single (by constructor)) (reduce_sound rfl), reduce_norm rfl⟩
  have heq := reduce_congr_point (x := (B.app y).bang) ▸ h_dom
  dcc_simp at heq
  exact heq

def Domain.pair : Domain (DCC? ⟦B⟧⟨x, y⟩) x.domain.fst.bang := by
  have h_dom : Domain (DCC? (⟦B⟧⟨x, y⟩)) _ := ⟨.trans (.single (by constructor)) (reduce_sound rfl), reduce_norm rfl⟩
  have heq := reduce_congr_point (x := x.dom.bang) ▸ h_dom
  dcc_simp at heq
  change (B.pair x y).Domain (reduce RedAff x.dom).fst.bang at heq
  have h : Domain x (reduce RedAff x.dom).fst := x.domain.snd
  exact h.complete_fst.symm ▸ heq

def Domain.sigma : Domain (DCC? Σ(B, C)) C.domain.fst :=
  ⟨.trans (.single (by constructor)) (reduce_sound rfl), reduce_norm rfl⟩

def Domain.comp : Domain (DCC? f ∘ g) g.domain.fst :=
  ⟨.trans (.single (by constructor)) (reduce_sound rfl), reduce_norm rfl⟩

def Domain.elim_comp (h_dom : Domain (DCC? f ∘ g) A) : Domain g A := by
  have h_dom' := Domain.comp (f := f) (g := g)
  cases h_dom.unique h_dom'
  exact g.domain.snd

def Domain.fst : Domain (DCC? Fst(B)) (DCC? Coup(#((reduce RedAff B).fst))) :=
  ⟨.trans (.single .fstcτ₀) (aff_mk_point' (n := 0) (reduce_sound rfl)), fun ⟨_, .coup₀ h⟩ => (reduce_norm rfl) ⟨_, h⟩⟩

def Domain.snd : Domain (DCC? Snd(B)) (DCC? Coup(#((reduce RedAff B).fst))) :=
  ⟨.trans (.single .sndcτ₀) (aff_mk_point' (n := 0) (reduce_sound rfl)), fun ⟨_, .coup₀ h⟩ => (reduce_norm rfl) ⟨_, h⟩⟩

def Domain.id : Domain (DCC? Id(A)) (reduce RedAff A).fst :=
  ⟨.trans (.single .idτ₀) (reduce_sound rfl), reduce_norm rfl⟩

def Domain.quot : Domain (DCC? `(B, x)) (reduce RedAff B).fst :=
  ⟨.trans (.single .quotτ₀) (reduce_sound rfl), reduce_norm rfl⟩

/-def Domain.unbox : Domain (DCC? *(A)) (DCC? !(#((reduce RedAff A).fst))) :=
  ⟨.trans (.single .unboxτ₀) (aff_mk_point' (n := 0) (reduce_sound rfl)), fun ⟨_, .coup₀ h⟩ => (reduce_norm rfl) ⟨_, h⟩⟩-/

end GenericExpr
