import Dcc.Judge3
import Dcc.Metatheory.Decidability3

universe u
variable {τ_c : Type u} [DecidableEq τ_c]

namespace GenericExpr

def Arrow.unique (h₁ : Arrow (τ := τ_c) A₁ B₁ u₁ τ) (h₂ : Arrow A₂ B₂ u₂ τ) : (A₁ = A₂) ×' (B₁ = B₂) ×' (u₁ = u₂) := by
  have heq₁ := h₁.read_complete
  have heq₂ := h₂.read_complete
  have heq' := heq₁.symm.trans heq₂
  exact ⟨by grind, by aesop, by aesop⟩

theorem set_points_eq_iff : e = set_points e p' ↔ p' = e.points := ⟨fun heq => by
  cases e <;> grind, fun h => by rw [h]; symm; exact set_points_self_noop⟩

def sort_norm (m : Level) : IsNorm (RedAff (τ := τ_c)) (DCC? (Sort m)) := fun ⟨_, h⟩ => nomatch h

def Reduces.congrFun' (h : Reduces f f') (hr : Reduces (DCC? (f' x)) B) : Reduces (DCC? (f x)) B :=
  match h, hr with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ => by
    exact ⟨.trans (GenericExpr.congrFun' hr₁) hr₂, hn₂⟩

def Reduces.congrArg' (h : Reduces x x') (hr : Reduces (DCC? (f x')) B) : Reduces (DCC? (f x)) B :=
  match h, hr with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ => by
    exact ⟨.trans (GenericExpr.congrArg' hr₁) hr₂, hn₂⟩

def Reduces.congrFun (hr : Reduces (DCC? (f x)) B) (h : Reduces f f') : Reduces (DCC? (f' x)) B :=
  match h, hr with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ => by
    have heq  : (reduce RedAff (DCC? (f x))).fst = B  := reduce_complete_fst hr₂ hn₂
    have heq₂ : (reduce RedAff (DCC? (f' x))).fst = B := by
      have ⟨_, h₁, h₂⟩ := hr₂.conf (GenericExpr.congrFun' hr₁)
      cases hn₂.unique_refl h₁
      exact reduce_complete_fst (by assumption) (by assumption)
    exact ⟨heq₂ ▸ (reduce RedAff (DCC? (f' x))).snd.down, by assumption⟩

def Reduces.congrArg (hr : Reduces (DCC? (f x)) B) (h : Reduces x x') : Reduces (DCC? (f x')) B :=
  match h, hr with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ => by
    have heq  : (reduce RedAff (DCC? (f x))).fst = B  := reduce_complete_fst hr₂ hn₂
    have heq₂ : (reduce RedAff (DCC? (f x'))).fst = B := by
      have ⟨_, h₁, h₂⟩ := hr₂.conf (GenericExpr.congrArg' hr₁)
      cases hn₂.unique_refl h₁
      exact reduce_complete_fst (by assumption) (by assumption)
    exact ⟨heq₂ ▸ (reduce RedAff (DCC? (f x'))).snd.down, by assumption⟩

def Reduces.decreasing {A B : GenericExpr τ_c} (hr : Reduces A B) (hneq : A ≠ B) : B.size < A.size :=
  match hr with
  | ⟨hr, hn⟩ => by
    match hr.cases_head with
    | .inl h => grind
    | .inr ⟨_, hr₁, hrt₁⟩ =>
      have h_dec₁ := hr.decreasing?
      have h_dec₂ := hr₁.decreasing
      grind

def Reduces.trans (hr₁ : Reduces (τ_c := τ_c) A B) (hr₂ : Reduces B C) : Reduces A C := by
  cases hr₂.elim_norm hr₁.is_norm
  assumption

def elim_reduce_norm_fst (h : IsNorm RedAff A) : (reduce RedAff A).fst = A := by
  apply norm_unique (r := RedAff) (m := Relation.ReflTransGen)
  · exact reduce_sound rfl
  · exact reduce_norm rfl
  · exact .refl
  · assumption

def elim_reduce_norm (h : IsNorm RedAff A) : (reduce RedAff A) = ⟨A, ⟨.refl⟩⟩ := by
  exact reduce_complete (A := A) (B := A) .refl h

def reduce_sort : (reduce (RedAff (τ := τ_c)) (DCC? (Sort u))).fst = (DCC? (Sort u)) := elim_reduce_norm_fst (fun ⟨_, h⟩ => nomatch h)

def mk_norm₁ (heq : point_arity (τ_c := τ_c) e = 1) (hn : IsNorm RedAff (points e)[0]) : IsNorm RedAff e := by
  intro ⟨_, h⟩
  induction h
  any_goals (grind only [point_arity])
  case point =>
    expose_names
    rw [heq] at h
    match n with
    | 0 =>
      exact hn ⟨_, h_1⟩

def congr_reduce₁ (heq : point_arity (τ_c := τ_c) e = 1) (heq₂ : B = e.set_points (e.points.set 0 (reduce RedAff e.points[0]).fst) := by rfl) : (reduce RedAff e).fst = B := by
  rw [heq₂]
  apply norm_unique (r := RedAff) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl)
  · exact aff_mk_point' (n := 0) (e := e) (reduce_sound rfl)
  · have hlt := (congr_point_arr (e := e) (p := ⟨0, by grind⟩) (p' := (reduce RedAff e.points[0]).fst)).symm.trans heq
    have heq := get_set_point (e := e) (p := ⟨0, by grind⟩) (p' := (reduce RedAff e.points[0]).fst)
    change (e.set_points (e.points.set 0 (reduce RedAff e.points[0]).fst _)).points[0] = _ at heq
    exact mk_norm₁ hlt (by rw [heq]; exact reduce_norm rfl)

def mk_norm₂ (heq : point_arity (τ_c := τ_c) e = 2) (hn₁ : IsNorm RedAff (points e)[0]) (hn₂ : IsNorm RedAff (points e)[1]) : IsNorm RedAff e := by
  intro ⟨_, h⟩
  induction h
  any_goals (grind only [point_arity])
  case point =>
    expose_names
    rw [heq] at h
    match n with
    | 0 =>
      exact hn₁ ⟨_, by assumption⟩
    | 1 =>
      exact hn₂ ⟨_, by assumption⟩

def congr_reduce₂ (heq : point_arity (τ_c := τ_c) e = 2) (heq₂ : B = e.set_points ⟨#[(reduce RedAff e.points[0]).fst, (reduce RedAff e.points[1]).fst], by grind⟩) : (reduce RedAff e).fst = B := by
  rw [heq₂]
  apply norm_unique (r := RedAff) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl)
  · have h := congr_point_lt (n := 1) (e := e) (h := by grind) (p' := (reduce RedAff e.points[0]).fst) (hn := by grind)
    refine .trans (aff_mk_point' (n := 0) (e := e) (reduce_sound rfl)) ?_
    · rw [set_points_eq_set_points₂]
      rw [set_points_assoc e (m := 0) (n := 1) (by grind) (by grind)]
      apply aff_mk_point'
      · exact reduce_sound rfl
      · exact get_unset_point (by grind)
  · apply mk_norm₂
    · rw [set_points_points]
      exact reduce_norm rfl
    · rw [set_points_points]
      exact reduce_norm rfl
    · simp [congr_point_arr' (e := e)]; exact heq

def mk_norm₃ (heq : point_arity (τ_c := τ_c) e = 3) (hn₁ : IsNorm RedAff (points e)[0]) (hn₂ : IsNorm RedAff (points e)[1]) (hn₃ : IsNorm RedAff (points e)[2]) : IsNorm RedAff e := by
  intro ⟨_, h⟩
  induction h
  any_goals (grind only [point_arity])
  case point =>
    expose_names
    rw [heq] at h
    match n with
    | 0 =>
      exact hn₁ ⟨_, by assumption⟩
    | 1 =>
      exact hn₂ ⟨_, by assumption⟩
    | 2 =>
      exact hn₃ ⟨_, by assumption⟩

def mk_norm₄ (heq : point_arity (τ_c := τ_c) e = 4) (hn₁ : IsNorm RedAff (points e)[0]) (hn₂ : IsNorm RedAff (points e)[1]) (hn₃ : IsNorm RedAff (points e)[2]) (hn₄ : IsNorm RedAff (points e)[3]) : IsNorm RedAff e := by
  intro ⟨_, h⟩
  induction h
  any_goals (grind only [point_arity])
  case point =>
    expose_names
    rw [heq] at h
    match n with
    | 0 =>
      exact hn₁ ⟨_, by assumption⟩
    | 1 =>
      exact hn₂ ⟨_, by assumption⟩
    | 2 =>
      exact hn₃ ⟨_, by assumption⟩
    | 3 =>
      exact hn₄ ⟨_, by assumption⟩

def congr_reduce₃ (heq : point_arity (τ_c := τ_c) e = 3) (heq₂ : B = e.set_points ⟨#[(reduce RedAff e.points[0]).fst, (reduce RedAff e.points[1]).fst, (reduce RedAff e.points[2]).fst], by grind⟩) : (reduce RedAff e).fst = B := by
  rw [heq₂]
  apply norm_unique (r := RedAff) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl)
  · have h := congr_point_lt (n := 1) (e := e) (h := by grind) (p' := (reduce RedAff e.points[0]).fst) (hn := by grind)
    refine .trans (aff_mk_point' (n := 0) (e := e) (reduce_sound rfl)) (.trans (aff_mk_point' (n := 1) (y := (reduce RedAff e.points[1]).fst) (hn := ?_) (heq := ?_) ?_
      (x := (e.set_points (e.points.set 0 (reduce RedAff e.points[0]).fst)).points.get ⟨1, ?_⟩)) ?_)
    · have h := congr_point_arr (e := e) (p := ⟨0, by grind⟩) (p' := (reduce RedAff e.points[0]).fst)
      rw [← h]
      grind
    · simp [get_unset_point (m := 0) (n := 1) (by grind)]
      exact reduce_sound rfl
    · have h := congr_point_arr (e := e) (p := ⟨0, by grind⟩) (p' := (reduce RedAff e.points[0]).fst)
      grind
    · rfl
    · rw [set_points_eq_set_points₃]
      have heq : (e.set_points (((e.points.set 0 (reduce RedAff e.points[0]).fst (by grind)).set 1 (reduce RedAff e.points[1]).fst (by grind)).set 2 (reduce RedAff e.points[2]).fst (by grind))) = (e.set_points ((e.points.set 0 (reduce RedAff e.points[0]).fst (by grind)).set 1 (reduce RedAff e.points[1]).fst (by grind))).set_points ((e.set_points ((e.points.set 0 (reduce RedAff e.points[0]).fst (by grind)).set 1 (reduce RedAff e.points[1]).fst (by grind))).points.set 2 (reduce RedAff e.points[2]).fst (by
        have h := congr_point_arr' (p := ((e.points.set 0 (reduce RedAff e.points[0]).fst (by grind)).set 1 (reduce RedAff e.points[1]).fst (by grind)).toArray) (h := ((e.points.set 0 (reduce RedAff e.points[0]).fst (by grind)).set 1 (reduce RedAff e.points[1]).fst (by grind)).size_toArray)
        rw [h]
        grind)) := by
          cases e
          any_goals (simp [set_points, points])
      rw [heq]
      rw [← set_points_assoc]
      · refine aff_mk_point' (y := (reduce RedAff e.points[2]).fst) (heq := ?_) (hn := ?_) (reduce_sound rfl)
        · cases e
          any_goals (simp [set_points, points]; rfl)
  · apply mk_norm₃
    · rw [set_points_points]
      exact reduce_norm rfl
    · rw [set_points_points]
      exact reduce_norm rfl
    · rw [set_points_points]
      exact reduce_norm rfl
    · simp [congr_point_arr' (e := e)]; exact heq

set_option maxHeartbeats 100000000000 in
omit [DecidableEq τ_c] in
theorem congr_reduce₄ (heq : point_arity (τ_c := τ_c) e = 4) (heq₂ : B = e.set_points ⟨#[(reduce RedAff e.points[0]).fst, (reduce RedAff e.points[1]).fst, (reduce RedAff e.points[2]).fst, (reduce RedAff e.points[3]).fst], by grind⟩) : (reduce RedAff e).fst = B := by
  rw [heq₂]
  apply norm_unique (r := RedAff) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl)
  · have h := congr_point_lt (n := 1) (e := e) (h := by grind) (p' := (reduce RedAff e.points[0]).fst) (hn := by grind)
    apply Relation.ReflTransGen.trans
    · refine (.trans (aff_mk_point' (n := 0) (e := e) (reduce_sound rfl)) (aff_mk_point' (n := 1) (y := (reduce RedAff e.points[1]).fst) (hn := ?_) (heq := ?_) ?_
      (x := (e.set_points (e.points.set 0 (reduce RedAff e.points[0]).fst)).points.get ⟨1, ?_⟩)))
      have h := congr_point_arr (e := e) (p := ⟨0, by grind⟩) (p' := (reduce RedAff e.points[0]).fst)
      · rw [← h]
        grind
      · simp [get_unset_point (m := 0) (n := 1) (by grind)]
        exact reduce_sound rfl
      · have h := congr_point_arr (e := e) (p := ⟨0, by grind⟩) (p' := (reduce RedAff e.points[0]).fst)
        grind
      · rfl
    · rw [set_points_eq_set_points₄]
      apply Relation.ReflTransGen.trans
      · refine aff_mk_point' (n := 2) (hn := ?_) (heq := ?_) ?_ (x := e.points[2]) (y := (reduce RedAff e.points[2]).fst)
        · exact reduce_sound rfl
        · cases e
          any_goals (grind)
        · cases e
          any_goals (simp [set_points, points]; rfl)
      · apply Relation.ReflTransGen.trans
        · refine aff_mk_point' (n := 3) (hn := ?_) (heq := ?_) ?_ (x := e.points[3]) (y := (reduce RedAff e.points[3]).fst)
          · exact reduce_sound rfl
          · cases e
            any_goals (grind)
          · cases e
            any_goals (simp [set_points, points]; rfl)
        · cases e
          any_goals (simp [set_points, points]; exact Relation.ReflTransGen.refl)
  · apply mk_norm₄
    · rw [set_points_points]
      exact reduce_norm rfl
    · rw [set_points_points]
      exact reduce_norm rfl
    · rw [set_points_points]
      exact reduce_norm rfl
    · rw [set_points_points]
      exact reduce_norm rfl
    · simp [congr_point_arr' (e := e)]; exact heq

theorem set_points_inj : set_points e p₁ = set_points e p₂ ↔ p₁ = p₂ := ⟨
    fun heq => by
      cases e <;> grind
  , fun heq => by
    cases e <;> grind⟩

def Reduces.get_point {e : GenericExpr τ_c} (hr : Reduces e B) {p' : Vector (GenericExpr τ_c) (point_arity e)} (m : ℕ) (heq : B = e.set_points p') (hlt : m < point_arity e) : Reduces (e.points.get ⟨m, hlt⟩) p'[m] := by
  rw [heq] at hr
  match cases_point_arity' e with
  | .inl ⟨h⟩ => grind
  | .inr (.inl ⟨h⟩) =>
    have heq := congr_reduce₁ (e := e) h rfl
    have heq' := hr.unique ⟨reduce_sound_fst heq, reduce_norm_fst heq⟩
    rw [h] at hlt
    match m with
    | 0 =>
      have h := set_points_inj.mp heq'
      rw [h]
      have heq : (e.points.set 0 (reduce RedAff e.points[0]).fst (by grind))[0] = (reduce RedAff e.points[0]).fst := by
        simp [points]
      rw [heq]
      exact ⟨reduce_sound rfl, reduce_norm rfl⟩
  | .inr (.inr (.inl ⟨h⟩)) =>
    have heq := congr_reduce₂ (e := e) h rfl
    have heq' := hr.unique ⟨reduce_sound_fst heq, reduce_norm_fst heq⟩
    rw [h] at hlt
    match m with
    | 0 | 1 =>
      have h := set_points_inj.mp heq'
      rw [h]
      simp
      exact ⟨reduce_sound rfl, reduce_norm rfl⟩
  | .inr (.inr (.inr (.inl ⟨h⟩))) =>
    have heq := congr_reduce₃ (e := e) h rfl
    have heq' := hr.unique ⟨reduce_sound_fst heq, reduce_norm_fst heq⟩
    rw [h] at hlt
    match m with
    | 0 | 1 | 2 =>
      have h := set_points_inj.mp heq'
      rw [h]
      simp
      exact ⟨reduce_sound rfl, reduce_norm rfl⟩
  | .inr (.inr (.inr (.inr ⟨h⟩))) =>
    have heq := congr_reduce₄ (e := e) h rfl
    have heq' := hr.unique ⟨reduce_sound_fst heq, reduce_norm_fst heq⟩
    rw [h] at hlt
    match m with
    | 0 | 1 | 2 | 3=>
      have h := set_points_inj.mp heq'
      rw [h]
      simp
      exact ⟨reduce_sound rfl, reduce_norm rfl⟩

def Reduces.point₁ (h : Reduces (τ_c := τ_c) e e'') (heq : point_arity e = 1 := by rfl) (heq₂ : e.set_points (e.points.set 0 (reduce RedAff e.points[0]).fst) = e') : e'' = e' := by
  apply Reduces.unique
  · exact h
  · exact ⟨reduce_sound_fst (congr_reduce₁ heq heq₂.symm), reduce_norm_fst (congr_reduce₁ heq heq₂.symm)⟩

/-def Reduces.congr₁ (heq : point_arity A = 1) (h : Reduces A e) : B = e.set_points (e.points.set 0 (reduce RedAff e.points[0]).fst) := by
  sorry-/

open Dsl in
def mk_norm_pi (hn₁ : IsNorm RedAff B) (hn₂ : IsNorm RedAff C) (hn₃ : IsNorm RedAff env) : IsNorm RedAff (DCC? ((Π B C) env)) := fun ⟨_, h⟩ =>
  match h with
  | .congrFun h =>
    mk_norm₂ rfl hn₁ hn₂ ⟨_, h⟩
  | .congrArg h => hn₃ ⟨_, h⟩

def Reduces.pi_eq (hr : Reduces (τ_c := τ_c) (open Dsl in (DCC? ((Π B C) env))) e') : e' = (open Dsl in (DCC? ((Π #((reduce RedAff B).fst) #((reduce RedAff C).fst)) #((reduce RedAff env).fst)))) :=
  hr.unique ⟨.trans (.trans (GenericExpr.congrFun' (aff_mk_point' (n := 0) (reduce_sound rfl))) (GenericExpr.congrFun' (aff_mk_point' (n := 1) (reduce_sound rfl)))) (GenericExpr.congrArg' (reduce_sound rfl)), mk_norm_pi (reduce_norm rfl) (reduce_norm rfl) (reduce_norm rfl)⟩

def Reduces.norm_env {B C : GenericExpr τ_c} (hn₁ : IsNorm RedAff B) (hn₂ : IsNorm RedAff C) (hr : Reduces (open Dsl in (DCC? ((Π B C) env))) e') :
  Σ' (env' : GenericExpr τ_c) (_hr : Reduces env env'), e' = (open Dsl in (DCC? ((Π B C) env'))) :=
  have heq₁ : (reduce RedAff B).fst = B := by
    apply norm_unique (r := RedAff) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl) .refl
    assumption
  have heq₂ : (reduce RedAff C).fst = C := by
    apply norm_unique (r := RedAff) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl) .refl
    assumption
  ⟨(reduce RedAff env).fst, ⟨reduce_sound rfl, reduce_norm rfl⟩, heq₁ ▸ heq₂ ▸ Reduces.pi_eq hr⟩

namespace Judge

def id_preservation_head (h : Judge (τ_c := τ_c) (DCC? ((Id A) x)) τ) : Judge x τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | id =>
      expose_names
      replace a_3 := (a_3.push_head (.congrFun .quot)).push_head .quot
      replace a := a.push_head .id
      cases a_3.elim_norm a_4.is_norm
      cases (a.elim_norml a_4.is_norm).elim_norm a_2.is_norm
      assumption

def comp_preservation_head (h : Judge (τ_c := τ_c) (DCC? ((∘ f g) x)) τ) : Judge (DCC? (f (g x))) τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | comp =>
      expose_names
      cases a_6.pi_eq
      have heq₁ : (reduce (RedAff (τ := τ_c)) (GenericExpr.sort m).id).fst = (GenericExpr.sort m).id :=
        elim_reduce_norm_fst (A := (GenericExpr.sort m).id) (fun ⟨_, .point 0 hn h⟩ => nomatch h)
      have heq₂ : (reduce RedAff ((GenericExpr.sort m).quot (C.comp g))).fst = ((GenericExpr.sort m).quot ((reduce RedAff C).fst.comp (reduce RedAff g).fst)) := by
        apply congr_reduce₂ (heq := by rfl)
        simp [points, reduce_sort, set_points]
        · symm
          apply congr_reduce₂ (heq := by rfl)
          simp [set_points, points]
      rw [heq₁] at a
      rw [heq₂] at a_3
      have a_3' := (a_3.push_head (.congrFun .quot)).push_head .comp
      unfold comp.f.type at a_4
      replace a := a.push_head .id
      have heq : (reduce RedAff A).fst = A := elim_reduce_norm_fst (a_1.is_norm a_5.is_norm).fst
      have hn_B : IsNorm RedAff B := (a_1.is_norm a_5.is_norm).snd
      have ar := a.elim_norml (reduce_norm_fst rfl)
      cases a_1 with
      | simple =>
        apply Judge.app
        · assumption
        · exact ⟨⟨.single .id, hn_B⟩, ⟨.refl, hn_B⟩⟩
        · apply Judge.app
          · exact a_5
          · exact (DefEq.trans ⟨⟨.single .id, (reduce_norm_fst heq)⟩, ⟨.refl, reduce_norm_fst heq⟩⟩ (heq ▸ a))
          · exact a_2
          · exact ⟨.trans (.single (.congrFun .quot)) (.single .quot), hn_B⟩
        · refine Reduces.pop_head (.congrFun .quot) ?_
          · have a_3'' :  ((reduce RedAff C).fst.app ((reduce RedAff ((reduce RedAff g).fst.app x)).fst)).Reduces τ :=
              a_3'.congrArg ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩
            exact Reduces.congrFun' ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ (Reduces.congrArg' (Reduces.congrFun'
                                    ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩) a_3'')

mutual

def fst_preservation_head (h : Judge (τ_c := τ_c) (DCC? ((Fst B) (,B₂ x y))) τ) : Judge x τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | fstc =>
      expose_names
      have heq₁ : (reduce RedAff B.coup).fst = (reduce RedAff B).fst.coup := congr_reduce₁ (e := B.coup) rfl
      have heq₂ : (reduce (RedAff (τ := τ_c)) (GenericExpr.sort (max m n)).id).fst = (GenericExpr.sort (max m n)).id :=
        elim_reduce_norm_fst (fun ⟨_, .point 0 hn h⟩ => nomatch h)
      have heq₃ : (reduce RedAff A).fst = A := elim_reduce_norm_fst (a_1.is_norm a_4.is_norm).fst
      have heq₄ : (reduce RedAff ((GenericExpr.sort (max m n)).quot (B.coup.quot A))).fst = ((GenericExpr.sort (max m n)).quot ((reduce RedAff B).fst.coup.quot A)) := by
        apply congr_reduce₂ (heq := by rfl)
        simp [points, reduce_sort, set_points]
        · symm
          apply congr_reduce₂ (heq := by rfl)
          simp [set_points, points, heq₃]
          · symm
            apply congr_reduce₁ (heq := by rfl)
      cases heq₁ ▸ heq₂ ▸ heq₃ ▸ heq₄ ▸ a_5.pi_eq
      replace a_3 := heq₃ ▸ a_3
      replace a_3 := (a_3.push_head (.congrFun .quot)).push_head .quot
      cases a_2 with
      | mk =>
        expose_names
        have a' := a.push_head .id
        have a'' := a'.elim_norml (fun ⟨_, .point 0 hn h⟩ => by
          simp [points, Vector.get] at h
          cases h.elim_norm (reduce_norm rfl))
        cases a''.elim_norm a_10.is_norm
        cases a_3.elim_norm (reduce_norm_fst heq₃)
        have h := arr_is_norm (reduce_norm_fst heq₃) (sort_norm n) m
        have hr_B₂ : Reduces B₂ (reduce RedAff B).fst := by
          have h := a_10.get_point 0 (p' := #v[(reduce RedAff B).fst]) (by simp [set_points]; rfl) (by grind)
          simp [points, Vector.get] at h
          exact h
        have h := a_8.congrFun hr_B₂
        have ht'₁ := a_6.preservation_star hr_B₂
        have ht'₂ := a_4.preservation_star ⟨reduce_sound rfl, reduce_norm rfl⟩
        cases ht'₁.unique ht'₂
        cases (a_1.unique a_2).fst
        cases (a_1.unique a_2).snd.fst
        cases (a_1.unique a_2).snd.snd
        exact a_7

def snd_preservation_head (h : Judge (τ_c := τ_c) (DCC? ((Snd B) (,B₂ x y))) τ) : Judge y τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | sndc =>
      expose_names
      have heq₁ : (reduce RedAff B.coup).fst = (reduce RedAff B).fst.coup := congr_reduce₁ (e := B.coup) rfl
      have heq₂ : (reduce (RedAff (τ := τ_c)) (GenericExpr.sort (max m n)).id).fst = (GenericExpr.sort (max m n)).id :=
        elim_reduce_norm_fst (fun ⟨_, .point 0 hn h⟩ => nomatch h)
      have heq₃ : (reduce RedAff A).fst = A := elim_reduce_norm_fst (a_1.is_norm a_4.is_norm).fst
      cases heq₁ ▸ heq₂ ▸ a_5.pi_eq
      cases a_2 with
      | mk =>
        expose_names
        have h := (a.push_head .id).elim_norml (mk_norm₁ (by grind) (by
          simp [points]
          exact reduce_norm_fst rfl))
        cases h.elim_norm a_10.is_norm
        replace a_10 := a_10.get_point 0 (p' := #v[(reduce RedAff B).fst]) (by simp [set_points]; rfl) (by grind)
        simp [points, Vector.get] at a_10
        have h := a_8.congrFun a_10
        have ht'₁ := a_6.preservation_star a_10
        have ht'₂ := a_4.preservation_star ⟨reduce_sound rfl, reduce_norm rfl⟩
        cases ht'₁.unique ht'₂
        cases (a_1.unique a_2).fst
        cases (a_1.unique a_2).snd.fst
        cases (a_1.unique a_2).snd.snd
        have heq_fst : (reduce RedAff ((GenericExpr.sort (max m n)).quot (B.comp B.fstc))).fst = ((GenericExpr.sort (max m n)).quot ((reduce RedAff B).fst.comp (reduce RedAff B).fst.fstc)) := by
          apply congr_reduce₂ (heq := by rfl)
          simp [points, reduce_sort, set_points]
          · symm
            apply congr_reduce₂ (heq := by rfl)
            simp [set_points, points]
            · symm
              apply congr_reduce₁ (heq := by rfl)
        rw [heq_fst] at a_3
        replace a_3 := ((a_3.push_head (.congrFun .quot)).push_head .comp).push_head (.congrArg .fstc)
        cases h.unique a_3
        exact a_9

def preservation_sigma_head (h : Judge (τ_c := τ_c) (open Dsl in (DCC? ((Σ B C) x))) τ) : Judge (open Dsl in (DCC? (Σ (C x)))) τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | sigma =>
      expose_names
      have ⟨hn_δ, hn_sort⟩ := a_1.is_norm a_5.is_norm
      cases a_8.elim_norm (arr_is_norm hn_δ (fun ⟨_, h⟩ => nomatch h) o)
      cases ((a_3.push_head (.congrFun .quot)).push_head .quot).elim_norm (fun ⟨_, h⟩ => nomatch h)
      cases a_4 with
      | canon =>
        cases ((a.push_head .id).elim_normr a_2.is_norm).elim_norm hn_δ
        have h_B' := preservation_star a_5 a_6
        have hn : IsNorm RedAff ((B'.pi (x_α.curr B' (B'.coup.quot (GenericExpr.sort n))))) :=
          mk_norm₂ rfl a_6.is_norm (mk_norm₃ rfl
            (by
              simp [points]
              exact hn_δ)
            (by
              simp [points]
              exact a_6.is_norm)
            (by
              simp [points]
              refine mk_norm₂ rfl ?_ ?_
              · simp [points]
                refine mk_norm₁ rfl ?_
                simp [points]
                exact a_6.is_norm
              · simp [points]
                intro ⟨_, h⟩
                nomatch h))
        match heq_τ : τ_B, heq : a_1 with
        | _, .simple =>
          apply Judge.coup (.app (by assumption) ⟨⟨.single .id, hn_δ⟩, ⟨.refl, hn_δ⟩⟩ a_2 (Reduces.pop_head (.congrFun .quot) ⟨GenericExpr.congrArg' (f := ((B'.pi (x_α.curr B' (B'.coup.quot (GenericExpr.sort n)))))) (reduce_sound rfl), fun ⟨_, h⟩ =>
            match h with
            | .congrFun h => hn ⟨_, h⟩
            | .congrArg h => (reduce_norm rfl) ⟨_, h⟩⟩)) (by sorry) sorry

def preservation (h : Judge (τ_c := τ_c) e τ) (hr : RedAff e e') : Judge e' τ := by
  
  sorry

def preservation_star (h : Judge (τ_c := τ_c) e τ) (hr : Reduces e e') : Judge e' τ := by
  sorry

end

end Judge

end GenericExpr
