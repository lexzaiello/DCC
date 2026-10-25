import Dcc.Judge3
import Dcc.Metatheory.Decidability3

namespace Expr

def Arrow.unique (h₁ : Arrow A₁ B₁ τ) (h₂ : Arrow A₂ B₂ τ) : (A₁ = A₂) ×' (B₁ = B₂) := by
  have heq₁ := h₁.read_complete
  have heq₂ := h₂.read_complete
  have heq' := heq₁.symm.trans heq₂
  exact ⟨by grind, by aesop⟩

theorem set_points_eq_iff : e = set_points e p' ↔ p' = e.points := ⟨fun heq => by
  cases e <;> grind, fun h => by rw [h]; symm; exact set_points_self_noop⟩

def sort_norm (m : Level) : IsNorm Red (DCC? (Sort m)) := fun ⟨_, h⟩ => nomatch h

def RedNorm.congrFun' (h : RedNorm f f') (hr : RedNorm (DCC? (f' x)) B) : RedNorm (DCC? (f x)) B :=
  match h, hr with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ => by
    exact ⟨.trans (Expr.congrFun' hr₁) hr₂, hn₂⟩

def RedNorm.congrArg' (h : RedNorm x x') (hr : RedNorm (DCC? (f x')) B) : RedNorm (DCC? (f x)) B :=
  match h, hr with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ => by
    exact ⟨.trans (Expr.congrArg' hr₁) hr₂, hn₂⟩

/-def RedNorm.congrFun (hr : RedNorm (DCC? (f x)) B) (h : RedNorm f f') : RedNorm (DCC? (f' x)) B :=
  match h, hr with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ => by
    have heq  : (reduce Red (DCC? (f x))).fst = B  := reduce_complete_fst hr₂ hn₂
    have heq₂ : (reduce Red (DCC? (f' x))).fst = B := by
      have ⟨_, h₁, h₂⟩ := hr₂.conf (Expr.congrFun' hr₁)
      cases hn₂.unique_refl h₁
      exact reduce_complete_fst (by assumption) (by assumption)
    exact ⟨heq₂ ▸ (reduce Red (DCC? (f' x))).snd.down, by assumption⟩

def RedNorm.congrArg (hr : RedNorm (DCC? (f x)) B) (h : RedNorm x x') : RedNorm (DCC? (f x')) B :=
  match h, hr with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, hn₂⟩ => by
    have heq  : (reduce Red (DCC? (f x))).fst = B  := reduce_complete_fst hr₂ hn₂
    have heq₂ : (reduce Red (DCC? (f x'))).fst = B := by
      have ⟨_, h₁, h₂⟩ := hr₂.conf (Expr.congrArg' hr₁)
      cases hn₂.unique_refl h₁
      exact reduce_complete_fst (by assumption) (by assumption)
    exact ⟨heq₂ ▸ (reduce Red (DCC? (f x'))).snd.down, by assumption⟩-/

def RedNorm.decreasing {A B : Expr} (hr : RedNorm A B) (hneq : A ≠ B) : B.size < A.size :=
  match hr with
  | ⟨hr, hn⟩ => by
    match hr.cases_head with
    | .inl h => grind
    | .inr ⟨_, hr₁, hrt₁⟩ =>
      have h_dec₁ := hr.decreasing?
      have h_dec₂ := hr₁.decreasing
      grind

def RedNorm.trans (hr₁ : RedNorm A B) (hr₂ : RedNorm B C) : RedNorm A C := by
  cases hr₂.elim_norm hr₁.is_norm
  assumption

def elim_reduce_norm_fst (h : IsNorm Red A) : (reduce Red A).fst = A := by
  apply norm_unique (r := Red) (m := Relation.ReflTransGen)
  · exact reduce_sound rfl
  · exact reduce_norm rfl
  · exact .refl
  · assumption

def elim_reduce_norm (h : IsNorm Red A) : (reduce Red A) = ⟨A, ⟨.refl⟩⟩ := by
  exact reduce_complete (A := A) (B := A) .refl h

def reduce_sort : (reduce Red (DCC? (Sort u))).fst = (DCC? (Sort u)) := elim_reduce_norm_fst (fun ⟨_, h⟩ => nomatch h)

def mk_norm₁ (heq : point_arity e = 1) (hn : IsNorm Red (points e)[0]) : IsNorm Red e := by
  intro ⟨_, h⟩
  induction h
  any_goals (grind only [point_arity])
  case point =>
    expose_names
    rw [heq] at h
    match n with
    | 0 =>
      exact hn ⟨_, h_1⟩

def congr_reduce₁ (heq : point_arity e = 1) (heq₂ : B = e.set_points (e.points.set 0 (reduce Red e.points[0]).fst) := by rfl) : (reduce Red e).fst = B := by
  rw [heq₂]
  apply norm_unique (r := Red) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl)
  · exact aff_mk_point' (n := 0) (e := e) (reduce_sound rfl)
  · have hlt := (congr_point_arr (e := e) (p := ⟨0, by grind⟩) (p' := (reduce Red e.points[0]).fst)).symm.trans heq
    have heq := get_set_point (e := e) (p := ⟨0, by grind⟩) (p' := (reduce Red e.points[0]).fst)
    change (e.set_points (e.points.set 0 (reduce Red e.points[0]).fst _)).points[0] = _ at heq
    exact mk_norm₁ hlt (by rw [heq]; exact reduce_norm rfl)

def mk_norm₂ (heq : point_arity e = 2) (hn₁ : IsNorm Red (points e)[0]) (hn₂ : IsNorm Red (points e)[1]) : IsNorm Red e := by
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

theorem congr_reduce₂ (heq : point_arity e = 2) (heq₂ : B = e.set_points ⟨#[(reduce Red e.points[0]).fst, (reduce Red e.points[1]).fst], by grind⟩) : (reduce Red e).fst = B := by
  cases heq : e
  all_goals (rw [heq₂])
  any_goals (
    focus
    try (
      apply norm_unique (r := Red) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl)
      · have h := congr_point_lt (n := 1) (e := e) (h := by grind) (p' := (reduce Red e.points[0]).fst) (hn := by grind)
        apply Relation.ReflTransGen.trans (aff_mk_point' (n := 0) (reduce_sound rfl))
        conv =>
           left
           simp [set_points, points]
           rfl
        cases heq
        exact aff_mk_point' (n := 1) (reduce_sound rfl)
      · cases heq
        simp [set_points, points]
        apply mk_norm₂
        · exact reduce_norm rfl
        · exact reduce_norm rfl
        · grind)
    done)
  any_goals (
    cases heq
    grind [point_arity])

def mk_norm₃ (heq : point_arity e = 3) (hn₁ : IsNorm Red (points e)[0]) (hn₂ : IsNorm Red (points e)[1]) (hn₃ : IsNorm Red (points e)[2]) : IsNorm Red e := by
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

def mk_norm₄ (heq : point_arity e = 4) (hn₁ : IsNorm Red (points e)[0]) (hn₂ : IsNorm Red (points e)[1]) (hn₃ : IsNorm Red (points e)[2]) (hn₄ : IsNorm Red (points e)[3]) : IsNorm Red e := by
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

theorem congr_reduce₃ (heq : point_arity e = 3) (heq₂ : B = e.set_points ⟨#[(reduce Red e.points[0]).fst, (reduce Red e.points[1]).fst, (reduce Red e.points[2]).fst], by grind⟩) : (reduce Red e).fst = B := by
  cases heq : e
  all_goals (rw [heq₂])
  any_goals (
    cases heq
    grind [point_arity])
  any_goals (
    apply norm_unique (r := Red) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl)
    · have h := congr_point_lt (n := 1) (e := e) (h := by grind) (p' := (reduce Red e.points[0]).fst) (hn := by grind)
      apply Relation.ReflTransGen.trans (aff_mk_point' (n := 0) (reduce_sound rfl))
      conv =>
         left
         simp [set_points, points]
         rfl
      cases heq
      exact .trans (aff_mk_point' (n := 1) (reduce_sound rfl)) (aff_mk_point' (n := 2) (reduce_sound rfl))
    · cases heq
      simp [set_points, points]
      apply mk_norm₃
      · exact reduce_norm rfl
      · exact reduce_norm rfl
      · exact reduce_norm rfl
      · simp [point_arity])

theorem congr_reduce₄ (heq : point_arity e = 4) (heq₂ : B = e.set_points ⟨#[(reduce Red e.points[0]).fst, (reduce Red e.points[1]).fst, (reduce Red e.points[2]).fst, (reduce Red e.points[3]).fst], by grind⟩) : (reduce Red e).fst = B := by
  cases heq : e
  all_goals (rw [heq₂])
  any_goals (
    cases heq
    grind [point_arity])
  any_goals (
    apply norm_unique (r := Red) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl)
    · have h := congr_point_lt (n := 1) (e := e) (h := by grind) (p' := (reduce Red e.points[0]).fst) (hn := by grind)
      apply Relation.ReflTransGen.trans (aff_mk_point' (n := 0) (reduce_sound rfl))
      conv =>
         left
         simp [set_points, points]
         rfl
      cases heq
      exact .trans (.trans (aff_mk_point' (n := 1) (reduce_sound rfl)) (aff_mk_point' (n := 2) (reduce_sound rfl)))
        (aff_mk_point' (n := 3) (reduce_sound rfl))
    · cases heq
      simp [set_points, points]
      apply mk_norm₄
      · exact reduce_norm rfl
      · exact reduce_norm rfl
      · exact reduce_norm rfl
      · exact reduce_norm rfl
      · simp [point_arity])

/-theorem congr_reduce_app (hn : step_head? (DCC (f x)) = .none) : (reduce Red (DCC (f x))).fst = ((reduce Red f).fst.app (reduce Red x).fst) := by
  conv =>
    left
    simp [reduce, Rel.run]
    rfl
  unfold step?
  split
  case h_1 heq =>
    split at heq
    · grind
    · simp [cases_point_arity', point_arity] at heq
      expose_names
      sorry
  case h_2 =>
    expose_names
    -/

theorem set_points_inj : set_points e p₁ = set_points e p₂ ↔ p₁ = p₂ := ⟨
    fun heq => by
      cases e <;> grind
  , fun heq => by
    cases e <;> grind⟩

def RedNorm.get_point {e B : Expr} (hr : RedNorm e B) {p' : Vector Expr (point_arity e)} (m : ℕ) (heq : B = e.set_points p') (hlt : m < point_arity e) : RedNorm (e.points.get ⟨m, hlt⟩) p'[m] := by
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
      have heq : (e.points.set 0 (reduce Red e.points[0]).fst (by grind))[0] = (reduce Red e.points[0]).fst := by
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

def RedNorm.point₁ (h : RedNorm e e'') (heq : point_arity e = 1 := by rfl) (heq₂ : e.set_points (e.points.set 0 (reduce Red e.points[0]).fst) = e') : e'' = e' := by
  apply RedNorm.unique
  · exact h
  · exact ⟨reduce_sound_fst (congr_reduce₁ heq heq₂.symm), reduce_norm_fst (congr_reduce₁ heq heq₂.symm)⟩

/-def RedNorm.congr₁ (heq : point_arity A = 1) (h : RedNorm A e) : B = e.set_points (e.points.set 0 (reduce Red e.points[0]).fst) := by
  sorry-/

def RedNorm.pi_eq (hr : RedNorm (open Dsl in (DCC? ((Π B C) env))) e') : e' = (open Dsl in (DCC? ((Π #((reduce Red B).fst) #((reduce Red C).fst)) #((reduce Red env).fst)))) :=
  hr.unique ⟨.trans (.trans (Expr.congrFun' (aff_mk_point' (n := 0) (reduce_sound rfl))) (Expr.congrFun' (aff_mk_point' (n := 1) (reduce_sound rfl)))) (Expr.congrArg' (reduce_sound rfl)), pi_is_norm (reduce_norm rfl) (reduce_norm rfl) (reduce_norm rfl)⟩

def RedNorm.norm_env {B C : Expr} (hn₁ : IsNorm Red B) (hn₂ : IsNorm Red C) (hr : RedNorm (open Dsl in (DCC? ((Π B C) env))) e') :
  Σ' (env' : Expr) (_hr : RedNorm env env'), e' = (open Dsl in (DCC? ((Π B C) env'))) :=
  have heq₁ : (reduce Red B).fst = B := by
    apply norm_unique (r := Red) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl) .refl
    assumption
  have heq₂ : (reduce Red C).fst = C := by
    apply norm_unique (r := Red) (m := Relation.ReflTransGen) (reduce_sound rfl) (reduce_norm rfl) .refl
    assumption
  ⟨(reduce Red env).fst, ⟨reduce_sound rfl, reduce_norm rfl⟩, heq₁ ▸ heq₂ ▸ RedNorm.pi_eq hr⟩

namespace Judge

def id_preservation_head (h : Judge (DCC? ((Id A) x)) τ) : Judge x τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | id =>
      expose_names
      replace a_3 := (a_3.push_head (.congrFun .quot)).push_head .quot
      replace a := a.push_head .quot
      cases a_3.elim_norm a_4.is_norm
      cases (a.elim_norml a_4.is_norm).elim_norm a_2.is_norm
      assumption

def fst_preservation_head (h : Judge (DCC? ((Fst B) (,B₂ x y))) τ) : Judge x τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | fstc =>
      expose_names
      cases a_2 with
      | mk =>
        expose_names
        cases a_11.elim_norm (sigma_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_8.is_norm) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_7.is_norm) (fun ⟨_, h⟩ => nomatch h))
        replace a := a.push_head .quot
        have ⟨hn_A, _⟩ := a_1.is_norm (Judge.is_norm (by assumption))
        have a' := a.elim_norml (sigma_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) hn_A) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_5.is_norm) (fun ⟨_, h⟩ => nomatch h))
        have ⟨hn_A_1, _⟩ := a_2.is_norm (Judge.is_norm (by assumption))
        cases a'.elim_norm (sigma_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) hn_A_1) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_7.is_norm) (fun ⟨_, h⟩ => nomatch h))
        replace a_3 := (a_3.push_head (.congrFun .quot)).push_head .quot
        exact a_3.elim_norm hn_A ▸ a_8

def snd_preservation_head (h : Judge (DCC? ((Snd B) (,B₂ x y))) τ) : Judge y τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | sndc =>
      cases a_2 with
      | mk =>
        expose_names
        cases a_11.elim_norm (sigma_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_8.is_norm) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_7.is_norm) (fun ⟨_, h⟩ => nomatch h))
        replace a := a.push_head .quot
        have ⟨hn_A, _⟩ := a_1.is_norm (Judge.is_norm (by assumption))
        have a' := a.elim_norml (sigma_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) hn_A) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_4.is_norm) (fun ⟨_, h⟩ => nomatch h))
        have ⟨hn_A_1, _⟩ := a_5.is_norm (Judge.is_norm (by assumption))
        cases a'.elim_norm (sigma_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) hn_A_1) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_7.is_norm) (fun ⟨_, h⟩ => nomatch h))
        replace a_3 := ((a_3.push_head (.congrFun .quot)).push_head .comp).push_head (.congrArg .fstc)
        exact a_9.unique a_3 ▸ a_10

def comp_preservation_head (h : Judge (DCC? ((∘ f g) x)) τ) : Judge (DCC? (f (g x))) τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | comp =>
      expose_names
      replace a_3 := (a_3.push_head (.congrFun .quot)).push_head .comp
      have ⟨hn_A, hn_B⟩ := a_1.is_norm a_5.is_norm
      cases ((a.push_head .quot).elim_norml hn_A).elim_norm a_2.is_norm
      refine Judge.app a_4 ⟨⟨.single .quot, hn_B⟩, ⟨.refl, hn_B⟩⟩ ?_ ⟨.trans (.trans (.single (.congrFun .quot)) (congrArg' (congrFun' a_6.1))) a_3.1, a_3.is_norm⟩
      · cases a_1 with
        | simple =>
          expose_names
          apply Judge.app
          · exact a_5
          · exact ⟨⟨.trans (.single .quot) a_1.1, a_1.2⟩, ⟨.refl, a_1.is_norm⟩⟩
          · exact a_2
          · exact ⟨.trans (.single (.congrFun .quot)) (.trans (.single .quot) a_7.1), a_7.2⟩

def unbox_preservation_head (h : Judge (DCC ((* A) (& x))) τ) : Judge x τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | unbox =>
      expose_names
      cases ((a_3.push_head (.congrFun .quot)).push_head .quot).elim_norm a_4.is_norm
      cases ((a.push_head .quot).elim_norml (bang_is_norm a_4.is_norm)).elim_norm a_2.is_norm
      cases a_2 with
      | box h => exact h

def curr_preservation_head (h : Judge (DCC ((Λ A B x) y z)) τ) : Judge (DCC (x (,B y z))) τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | app =>
      expose_names
      cases a_4 with
      | curr =>
        expose_names
        replace a_6 := a_6.push_head (.congrFun .quot)
        have h := a_6.pi_eq
        have heq₁ := elim_reduce_norm_fst a_10.is_norm
        unfold curr.x.type at a_11
        have hn_x_type := a_11.is_norm
        have hn_curr : IsNorm Red (DCC (Λ A' B' C)) := curr_is_norm a_8.is_norm a_10.is_norm
          (fun ⟨_, h⟩ => hn_x_type ⟨_, .congrFun (.point 1 (by grind) (.point 1 (by point_arity) h))⟩)
        have heq₂ := elim_reduce_norm_fst hn_curr
        simp [heq₁, heq₂] at h
        cases h.left.left
        cases h.left.right
        cases h.right
        clear h
        replace a := a.elim_normr a_2.is_norm
        cases ((a_1.push_head .quot).elim_norml a_8.is_norm).elim_norm a_5.is_norm
        replace a_3 := a_3.push_head .curr
        apply Judge.app
        · exact a_11
        · exact ⟨⟨.single .quot, sigma_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_8.is_norm) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_10.is_norm) (fun ⟨_, h⟩ => nomatch h)⟩, .refl, sigma_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_8.is_norm) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_10.is_norm) (fun ⟨_, h⟩ => nomatch h)⟩
        · apply Judge.mk
          · exact a_5
          · exact a_9
          · exact a_4
          · exact a_10
          · exact ⟨.trans (congrArg' (reduce_sound rfl)) a.1, a.2⟩
          · exact a_2
          · exact ⟨.refl, sigma_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_8.is_norm) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_10.is_norm) (fun ⟨_, h⟩ => nomatch h)⟩
        · exact ⟨.trans (.single (.congrFun .quot)) (.trans (congrArg' (aff_mk_point' (n := 0) a_10.1 (by simp [point_arity]))) (.trans
            (by
              simp [set_points, points]
              have h := aff_mk_point' (n := 1) (reduce_sound rfl) (e := (f_α.mkc y z)) (x := y) (by simp [point_arity])
              simp [set_points, points] at h
              exact congrArg' h)
            a_3.1)), a_3.2⟩

def fmap_preservation_head (h : Judge (DCC (($<> x) (& y))) τ) : Judge (DCC (& (x y))) τ := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | fmap =>
      expose_names
      cases ((a.push_head .quot).elim_norml (bang_is_norm a_1.is_norm)).elim_norm a_2.is_norm
      replace a_3 := (a_3.push_head (.congrFun .quot)).push_head .map
      cases a_2 with
      | box h =>
        have heq_red_bang := a_3.complete_fst
        have heq' := heq_red_bang.symm.trans (congr_reduce₁ (e := (f_B'.app y).bang) (by simp [point_arity]))
        cases heq'
        apply Judge.box
        · apply Judge.app
          · assumption
          · exact ⟨a_1, ⟨.refl, a_1.2⟩⟩
          · exact h
          · exact ⟨.trans (congrFun' a_4.1) (reduce_sound rfl), reduce_norm rfl⟩

mutual

def preservation (h : Judge e τ) (hr : Red e e') : Judge e' τ := by
  sorry

def preservation_star (h : Judge e τ) (hr : RedNorm e e') : Judge e' τ := by
  sorry

end

end Judge

end Expr
