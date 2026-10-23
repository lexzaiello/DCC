import Dcc.Judge3
import Dcc.Metatheory.Decidability3

namespace Expr

open ElimNorm
open PushHead
open PopHead

def Arrow.unique (h₁ : Arrow A₁ B₁ τ) (h₂ : Arrow A₂ B₂ τ) : (A₁ = A₂) ×' (B₁ = B₂) := by
  have heq₁ := h₁.read_complete
  have heq₂ := h₂.read_complete
  have heq' := heq₁.symm.trans heq₂
  exact ⟨by grind, by aesop⟩

def elim_reduce_norm_fst (hn : IsNorm Red A) : (reduce Red A).fst = A := complete_fst ⟨.refl, ⟨hn⟩⟩

/-def reduce₁ (hp : Points e [x]) (hp' : WithPoints e [x] hp [(reduce Red x).fst] rfl e') : (reduce Red e).fst = (reduce Red e').fst :=
  match heq : step? x with
  | .some ⟨x', h⟩ =>
    reduce_self (.point₁ hp h (by sorry))
  | .none => by
    have hn_red₁ : ¬ x.HasRed := step_none_no_red (by assumption)
    have hp' := (elim_reduce_norm_fst (no_red_norm (by assumption))) ▸ hp'
    cases with_points_id hp'
    rfl
termination_by x.size

def reduce_congr : (reduce Red (DCC (f x))).fst = (reduce Red (((reduce Red f).fst).app ((reduce Red x).fst))).fst :=
  match heq₀ : (DCC (f x)).step_head? with
  | .some ⟨e', h⟩ => by
    cases h
    case id =>
      expose_names
      have hrt_point₁ := (reduce Red α.id).snd.raw
      have hrt_point₂ := (reduce Red x).snd.raw
      
  | .none =>
    have hn : ∀ (e' : Expr) (a : Red.Head (f.app x) e'), False := fun _ h => by
      have heq := complete h
      simp [Run.run, pure] at heq
      grind
    match heq₂ : step? x with
    | .some ⟨x', h⟩ =>
      have heq_x := reduce_self h
      have h_dec := decreasing h
      have heq' := reduce_congr (f := f) (x := x')
      complete_fst ⟨.trans (.single (.congr_arg (by assumption) h)) (heq_x ▸ (heq' ▸ (reduce Red (f.app x')).snd.raw)), ⟨heq_x ▸ heq' ▸ (reduce Red (f.app x')).snd.is_norm⟩⟩
    | .none =>
      have hn_red₁ : ¬ x.HasRed := step_none_no_red (by assumption)
      have heq_hn₁ : (reduce Red x).fst = x := elim_reduce_norm_fst (no_red_norm (by assumption))
      match heq₃ : step? f with
      | .some ⟨f', h⟩ =>
        have heq_f := reduce_self h
        have h_dec := decreasing h
        have heq' := reduce_congr (f := f') (x := x)
        complete_fst ⟨.trans (.single (.congr_fun (by assumption) hn_red₁ h)) (heq_f ▸ (heq' ▸ (reduce Red (f'.app x)).snd.raw)), ⟨heq_f ▸ heq' ▸ (reduce Red (f'.app x)).snd.is_norm⟩⟩
      | .none =>
        have hn_red₁ : ¬ f.HasRed := step_none_no_red (by assumption)
        have heq_hn₂ : (reduce Red f).fst = f := elim_reduce_norm_fst (no_red_norm (by assumption))
        heq_hn₁.symm ▸ heq_hn₂.symm ▸ complete_fst (reduce Red (f.app x)).snd
termination_by f.size + x.size-/

open Dsl in
def quot₂ : (reduce Red (DCC ((`B₁ (`B₂ x)) y z))).fst = (reduce Red x).fst :=
  match heq₁ : z.step? with
  | .some ⟨z', h⟩ =>
    have h_dec := decreasing h
    have heq_inner := quot₂ (B₁ := B₁) (B₂ := B₂) (x := x) (y := y) (z := z')
    complete_fst ⟨.trans (.plus (.single (Red.congr_arg (fun _ h => nomatch h) h))) (heq_inner ▸ (reduce Red _).snd.raw), ⟨(reduce Red x).snd.is_norm⟩⟩
  | .none =>
    have hn_red₁ : ¬ z.HasRed := step_none_no_red (by assumption)
    complete_fst ⟨.trans (.plus (.single (Red.congr_fun (fun _ h => nomatch h) hn_red₁ (.head .quot)))) (.trans (.plus (.single (.head .quot))) (reduce Red x).snd.raw), ⟨(reduce Red x).snd.is_norm⟩⟩
  termination_by y.size + z.size

open Dsl in
def reduce_quot : (reduce Red (DCC (`B x))).fst = (DCC (`#((reduce Red B).fst) #((reduce Red x).fst))) :=
  match heq₁ : B.step? with
  | .some ⟨B', h⟩ =>
    have h_dec := decreasing h
    have heq := reduce_quot (B := B') (x := x)
    have heq₁ : (reduce Red B).fst = (reduce Red B').fst := complete_fst (pop_head h (reduce Red B').snd)
    have hrt' := (reduce Red (B'.quot x)).snd
    heq₁ ▸ complete_fst (pop_head (Red.point₂₁ .quot h .quot) (by
      rw [heq] at hrt'
      exact hrt'))
  | .none =>
    have hn_red₁ : ¬ B.HasRed := step_none_no_red (by assumption)
    have heq₁ : (reduce Red B).fst = B := elim_reduce_norm_fst (no_red_norm (by assumption))
    match heq₂ : x.step? with
    | .some ⟨x', h⟩ =>
      have h_dec := decreasing h
      have heq := heq₁ ▸ reduce_quot (B := B) (x := x')
      have heq₂ : (reduce Red x).fst = (reduce Red x').fst := complete_fst (pop_head h (reduce Red x').snd)
      have hrt' := (reduce Red (B.quot x')).snd
      heq₂ ▸ heq₁.symm ▸ (complete_fst (pop_head (.point₂₂ .quot h hn_red₁ .quot) (by
        rw [heq] at hrt'
        exact hrt')))
    | .none =>
      have hn_red₂ : ¬ x.HasRed := step_none_no_red (by assumption)
      have heq₂ : (reduce Red x).fst = x := elim_reduce_norm_fst (no_red_norm (by assumption))
      heq₁.symm ▸ heq₂.symm ▸ complete_fst ⟨.refl, ⟨mk_norm₂ (hp := .quot) (no_red_norm (by assumption)) (no_red_norm (by assumption))⟩⟩
termination_by B.size + x.size

open Dsl in
def reduce_sigma : (reduce Red (DCC ((Σ B C) x))).fst = (DCC ((Σ #((reduce Red B).fst) #((reduce Red C).fst)) #((reduce Red x).fst))) :=
  match heq₁ : x.step? with
  | .some ⟨x', h⟩ =>
    have h_dec := decreasing h
    have heq := reduce_sigma (B := B) (C := C) (x := x')
    have hrt := heq ▸ (reduce Red (DCC ((Σ B C) x'))).snd
    have heq_C : (reduce Red x).fst = (reduce Red x').fst := complete_fst (pop_head h (reduce Red x').snd)
    complete_fst ⟨.trans (.plus (.single (.congr_arg (fun _ h => nomatch h) h))) (heq_C ▸ hrt.raw), ⟨heq_C ▸ hrt.is_norm⟩⟩
  | .none =>
    have hn_red₁ : ¬ x.HasRed := step_none_no_red (by assumption)
    match heq₂ : B.step? with
    | .some ⟨B', h₂⟩ =>
      have h_dec := decreasing h₂
      have heq := reduce_sigma (B := B') (C := C) (x := x)
      have hrt := heq ▸ (reduce Red (DCC ((Σ B' C) x))).snd
      have heq_C : (reduce Red B).fst = (reduce Red B').fst := complete_fst (pop_head h₂ (reduce Red B').snd)
      complete_fst ⟨.trans (.plus (.single (.congr_fun (fun _ h => nomatch h) (by assumption) (.point₂₁ .sigma h₂ .sigma)))) (heq_C ▸ hrt.raw), ⟨heq_C ▸ hrt.is_norm⟩⟩
    | .none =>
      have hn_red₂ : ¬ B.HasRed := step_none_no_red (by assumption)
      match heq₃ : C.step? with
      | .some ⟨C', h₃⟩ =>
        have h_dec := decreasing h₃
        have heq := reduce_sigma (B := B) (C := C') (x := x)
        have hrt := heq ▸ (reduce Red (DCC ((Σ B C') x))).snd
        have heq_C : (reduce Red C).fst = (reduce Red C').fst := complete_fst (pop_head h₃ (reduce Red C').snd)
        complete_fst ⟨.trans (.plus (.single (.congr_fun (fun _ h => nomatch h) (by assumption) (.point₂₂ .sigma h₃ (by assumption) .sigma)))) (heq_C ▸ hrt.raw), ⟨heq_C ▸ hrt.is_norm⟩⟩
      | .none =>
        have hn_red₃ : ¬ C.HasRed := step_none_no_red (by assumption)
        have heq₁ : (reduce Red B).fst = B := complete_fst ⟨.refl, ⟨no_red_norm (by assumption)⟩⟩
        have heq₂ : (reduce Red C).fst = C := complete_fst ⟨.refl, ⟨no_red_norm (by assumption)⟩⟩
        have heq₃ : (reduce Red x).fst = x := complete_fst ⟨.refl, ⟨no_red_norm (by assumption)⟩⟩
        heq₁.symm ▸ heq₂.symm ▸ heq₃.symm ▸ complete_fst ⟨.refl,
          ⟨mk_norm_congr (fun _ h => nomatch h) (mk_norm₂ (hp := .sigma) (no_red_norm (by assumption)) (no_red_norm (by assumption))) (no_red_norm (by assumption))⟩⟩
termination_by B.size + C.size + x.size

def sort_norm (m : Level) : IsNorm Red (DCC (Sort m)) := fun _ h => nomatch h

def id_preservation_head (h : Judge (DCC ((Id A) x)) τ) : Judge x τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | id =>
      expose_names
      cases elim_norm a_2.is_norm ((a.push_head (.head .quot)).elim_norml a_4.is_norm)
      cases elim_norm a_4.is_norm ((quot₂ ▸ complete_fst a_3) ▸ (reduce Red α).snd)
      exact a_2

def fst_preservation_head (h : Judge (DCC ((Fst B) (,B₂ x y))) τ) : Judge x τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | fstc =>
      expose_names
      have ⟨hn₁, hn₂⟩ := a_1.is_norm a_4.is_norm
      cases elim_norm a_2.is_norm <| (a.push_head (.head .quot)).elim_norml (mk_norm_congr (fun _ h => nomatch h)
        (mk_norm₂ (hp := .sigma) (mk_norm₂ (hp := .quot) mk_norm_top hn₁) (mk_norm₂ mk_norm_top a_5.is_norm))
        mk_norm_tintro)
      cases elim_norm hn₁ ((quot₂ ▸ complete_fst a_3) ▸ (reduce Red A).snd)
      cases a_2 with
      | mk =>
        expose_names
        have heq₁ : (reduce Red (top.quot A)).fst = top.quot A := elim_reduce_norm_fst (mk_norm₂ mk_norm_top a_8.is_norm)
        have heq_top : (reduce Red .top).fst = .top := elim_reduce_norm_fst mk_norm_top
        have heq₂ := reduce_quot (B := .top) (x := B₂)
        have heq₂ : (reduce Red (top.quot B₂)).fst = top.quot (reduce Red B₂).fst := by
          rw [heq_top] at heq₂
          exact heq₂
        have heq := (elim_reduce_norm_fst mk_norm_tintro) ▸ heq₂ ▸ heq₁ ▸ reduce_sigma ▸ complete_fst a_11
        cases heq
        exact a_7

def snd_preservation_head (h : Judge (DCC ((Snd B) (,B₂ x y))) τ) : Judge y τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | sndc =>
      expose_names
      have ⟨hn₁, hn₂⟩ := a_1.is_norm a_4.is_norm
      cases elim_reduce_norm_fst mk_norm_tintro ▸ elim_reduce_norm_fst mk_norm_top ▸ reduce_quot ▸ elim_reduce_norm_fst (mk_norm₂ (hp := .quot) mk_norm_top hn₁) ▸ reduce_sigma ▸ complete_fst ((a.push_head (.head .quot)).elim_normr a_2.is_norm)
      cases complete_fst a_5
      cases a_2 with
      | mk =>
        expose_names
        have ⟨hn₃, hn₄⟩ := a_2.is_norm a_6.is_norm
        have heq_top : (reduce Red .top).fst = .top := elim_reduce_norm_fst mk_norm_top
        have heq₂ := reduce_quot (B := .top) (x := B₂)
        have heq₂ : (reduce Red (top.quot B₂)).fst = top.quot (reduce Red B₂).fst := by
          rw [heq_top] at heq₂
          exact heq₂
        have heq := elim_reduce_norm_fst hn₃ ▸ elim_reduce_norm_fst mk_norm_top ▸ reduce_quot ▸ (elim_reduce_norm_fst mk_norm_tintro) ▸ heq₂ ▸ reduce_sigma ▸ complete_fst a_10
        simp at heq
        obtain ⟨heql, heqr⟩ := heq
        cases heql
        have h := push_head a_3 (by sorry)
        sorry

mutual

def preservation (h : Judge e τ) (hr : Red e e') : Judge e' τ := by
  
  sorry

def preservation_star (h : Judge e τ) (hr : e →ᵦ e') : Judge e' τ := by
  sorry

end

/-def Reduces.congrFun' (h : f →ᵦ f') (hr : (f' x) →ᵦ B) : (f x) →ᵦ B :=
  match h, hr with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ => by
    exact ⟨.trans (Expr.congrFun' hr₁) hr₂, hn₂⟩

def Reduces.congrArg' (h : Reduces x x') (hr : Reduces (DCC (f x')) B) : Reduces (DCC (f x)) B :=
  match h, hr with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ => by
    exact ⟨.trans (Expr.congrArg' hr₁) hr₂, hn₂⟩

def Reduces.congrFun (hr : Reduces (DCC (f x)) B) (h : Reduces f f') : Reduces (DCC (f' x)) B :=
  match h, hr with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ => by
    have heq  : (reduce RedAff (DCC (f x))).fst = B  := reduce_complete_fst hr₂ hn₂
    have heq₂ : (reduce RedAff (DCC (f' x))).fst = B := by
      have ⟨_, h₁, h₂⟩ := hr₂.conf (Expr.congrFun' hr₁)
      cases hn₂.unique_refl h₁
      exact reduce_complete_fst (by assumption) (by assumption)
    exact ⟨heq₂ ▸ (reduce RedAff (DCC (f' x))).snd.down, by assumption⟩

def Reduces.congrArg (hr : Reduces (DCC (f x)) B) (h : Reduces x x') : Reduces (DCC (f x')) B :=
  match h, hr with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ => by
    have heq  : (reduce RedAff (DCC (f x))).fst = B  := reduce_complete_fst hr₂ hn₂
    have heq₂ : (reduce RedAff (DCC (f x'))).fst = B := by
      have ⟨_, h₁, h₂⟩ := hr₂.conf (Expr.congrArg' hr₁)
      cases hn₂.unique_refl h₁
      exact reduce_complete_fst (by assumption) (by assumption)
    exact ⟨heq₂ ▸ (reduce RedAff (DCC (f x'))).snd.down, by assumption⟩-/

def reduce_sort : (reduce Red (DCC (Sort u))).fst = (DCC (Sort u)) :=
  have h := (reduce Red (DCC (Sort u))).snd
  (elim_norm (fun _ h => by nomatch h) h).symm

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

def Reduces.get_point {e : Expr τ_c} (hr : Reduces e B) {p' : Vector (Expr τ_c) (point_arity e)} (m : ℕ) (heq : B = e.set_points p') (hlt : m < point_arity e) : Reduces (e.points.get ⟨m, hlt⟩) p'[m] := by
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
def mk_norm_pi (hn₁ : IsNorm RedAff B) (hn₂ : IsNorm RedAff C) (hn₃ : IsNorm RedAff env) : IsNorm RedAff (DCC ((Π B C) env)) := fun ⟨_, h⟩ =>
  match h with
  | .congrFun h =>
    mk_norm₂ rfl hn₁ hn₂ ⟨_, h⟩
  | .congrArg h => hn₃ ⟨_, h⟩

def Reduces.pi_eq (hr : Reduces (τ_c := τ_c) (open Dsl in (DCC ((Π B C) env))) e') : e' = (open Dsl in (DCC ((Π #((reduce RedAff B).fst) #((reduce RedAff C).fst)) #((reduce RedAff env).fst)))) :=
  hr.unique ⟨.trans (.trans (Expr.congrFun' (aff_mk_point' (n := 0) (reduce_sound rfl))) (Expr.congrFun' (aff_mk_point' (n := 1) (reduce_sound rfl)))) (Expr.congrArg' (reduce_sound rfl)), mk_norm_pi (reduce_norm rfl) (reduce_norm rfl) (reduce_norm rfl)⟩

def Reduces.norm_env {B C : Expr τ_c} (hn₁ : IsNorm RedAff B) (hn₂ : IsNorm RedAff C) (hr : Reduces (open Dsl in (DCC ((Π B C) env))) e') :
  Σ' (env' : Expr τ_c) (_hr : Reduces env env'), e' = (open Dsl in (DCC ((Π B C) env'))) :=
  have heq₁ : (reduce RedAff B).fst = B := by
    apply norm_unique (r := RedAff) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl) .refl
    assumption
  have heq₂ : (reduce RedAff C).fst = C := by
    apply norm_unique (r := RedAff) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl) .refl
    assumption
  ⟨(reduce RedAff env).fst, ⟨reduce_sound rfl, reduce_norm rfl⟩, heq₁ ▸ heq₂ ▸ Reduces.pi_eq hr⟩

namespace Judge

def id_preservation_head (h : Judge (τ_c := τ_c) (DCC ((Id A) x)) τ) : Judge x τ := by
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

def comp_preservation_head (h : Judge (τ_c := τ_c) (DCC ((∘ f g) x)) τ) : Judge (DCC (f (g x))) τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | comp =>
      expose_names
      cases a_6.pi_eq
      have heq₁ : (reduce (RedAff (τ := τ_c)) (Expr.sort m).id).fst = (Expr.sort m).id :=
        elim_reduce_norm_fst (A := (Expr.sort m).id) (fun ⟨_, .point 0 hn h⟩ => nomatch h)
      have heq₂ : (reduce RedAff ((Expr.sort m).quot (C.comp g))).fst = ((Expr.sort m).quot ((reduce RedAff C).fst.comp (reduce RedAff g).fst)) := by
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

def fst_preservation_head (h : Judge (τ_c := τ_c) (DCC ((Fst B) (,B₂ x y))) τ) : Judge x τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | fstc =>
      expose_names
      have heq₁ : (reduce RedAff B.coup).fst = (reduce RedAff B).fst.coup := congr_reduce₁ (e := B.coup) rfl
      have heq₂ : (reduce (RedAff (τ := τ_c)) (Expr.sort (max m n)).id).fst = (Expr.sort (max m n)).id :=
        elim_reduce_norm_fst (fun ⟨_, .point 0 hn h⟩ => nomatch h)
      have heq₃ : (reduce RedAff A).fst = A := elim_reduce_norm_fst (a_1.is_norm a_4.is_norm).fst
      have heq₄ : (reduce RedAff ((Expr.sort (max m n)).quot (B.coup.quot A))).fst = ((Expr.sort (max m n)).quot ((reduce RedAff B).fst.coup.quot A)) := by
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

def snd_preservation_head (h : Judge (τ_c := τ_c) (DCC ((Snd B) (,B₂ x y))) τ) : Judge y τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | sndc =>
      expose_names
      have heq₁ : (reduce RedAff B.coup).fst = (reduce RedAff B).fst.coup := congr_reduce₁ (e := B.coup) rfl
      have heq₂ : (reduce (RedAff (τ := τ_c)) (Expr.sort (max m n)).id).fst = (Expr.sort (max m n)).id :=
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
        have heq_fst : (reduce RedAff ((Expr.sort (max m n)).quot (B.comp B.fstc))).fst = ((Expr.sort (max m n)).quot ((reduce RedAff B).fst.comp (reduce RedAff B).fst.fstc)) := by
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

def preservation_sigma_head (h : Judge (τ_c := τ_c) (open Dsl in (DCC ((Σ B C) x))) τ) : Judge (open Dsl in (DCC (Σ (C x)))) τ := by
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
        have hn : IsNorm RedAff ((B'.pi (x_α.curr B' (B'.coup.quot (Expr.sort n))))) :=
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
          apply Judge.coup (.app (by assumption) ⟨⟨.single .id, hn_δ⟩, ⟨.refl, hn_δ⟩⟩ a_2 (Reduces.pop_head (.congrFun .quot) ⟨Expr.congrArg' (f := ((B'.pi (x_α.curr B' (B'.coup.quot (Expr.sort n)))))) (reduce_sound rfl), fun ⟨_, h⟩ =>
            match h with
            | .congrFun h => hn ⟨_, h⟩
            | .congrArg h => (reduce_norm rfl) ⟨_, h⟩⟩)) (by sorry) sorry

def preservation (h : Judge (τ_c := τ_c) e τ) (hr : RedAff e e') : Judge e' τ := by
  
  sorry

def preservation_star (h : Judge (τ_c := τ_c) e τ) (hr : Reduces e e') : Judge e' τ := by
  sorry

end

end Judge

end Expr
