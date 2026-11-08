import Dcc.Ast
import Dcc.Ast.Points
import Dcc.Red.RelationProp
import Mathlib.Tactic.IntervalCases

namespace Expr

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def eta_size (e : Expr) : ℕ :=
  open Dsl in match e with
  | DCC (∘ x y) => x.eta_size * 2 + y.eta_size + 1
  | DCC ∗ => 1
  | DCC 𝟙 => 1
  | DCC 𝟘 => 1
  | DCC (= A x y) => (A.eta_size + x.eta_size + y.eta_size) + 1
  | DCC (? m) => m.eta_size.succ
  | DCC 𝟙₂ => 1
  | DCC 𝟘₂ => 1
  | DCC 𝟚 => 1
  | DCC (𝟚.Rec motive x y) => motive.eta_size + x.eta_size + y.eta_size + 1
  | DCC (𝟘.Rec motive) => motive.eta_size + 1
  | DCC (Eql α)  => α.eta_size + 2
  | DCC (=' α)  => α.eta_size + 2
  | DCC (refl α) => α.eta_size + 1
  | DCC Sort _m => 1
  | DCC (Σ α β) => α.eta_size + β.eta_size + 1
  | DCC (Σ' α β) => α.eta_size + β.eta_size + 1
  | DCC (`β x) => β.eta_size + x.eta_size + 1
  | DCC (,β x y) => β.eta_size + x.eta_size + y.eta_size + 1
  | DCC (Id α)      => α.eta_size + 1
  | DCC (Fst β)    => β.eta_size + 1
  | DCC (Snd β)    => β.eta_size + 1
  | DCC (Swap B C)    => B.eta_size + C.eta_size + 2
  | DCC (Π α β) => α.eta_size + β.eta_size + 1
  | DCC (⟨,⟩β a b)   => 3 * (β.eta_size + a.eta_size + a.eta_size + b.eta_size + 3)
  | DCC (!Λ α β x) => (α.eta_size * 2) + (6 * (β.eta_size + 1)) + (x.eta_size * 2) + 5
  | DCC (Λ α β x) => α.eta_size + β.eta_size + x.eta_size + 2
  | DCC (Eval α β x) => α.eta_size + β.eta_size + x.eta_size + 1
  | DCC (!x)   => x.eta_size + 1
  | DCC (*x)   => x.eta_size + 1
  | DCC (&x)   => (x.eta_size * 5) + 1
  | DCC (!<> x)   => x.eta_size + 2
  | DCC ($<> x)   => (x.eta_size * 5) + 1
  | DCC (f x) => f.eta_size + x.eta_size
  | .hole _ => 1

@[grind .]
theorem eta_size_pos : 0 < eta_size e := by
  induction e <;> grind

@[grind .]
theorem point_eta_size_lt : eta_size ((Expr.points e).get n) < eta_size e := by
  induction e
  any_goals (
    fin_cases n <;>(simp [points, Vector.get, eta_size]; grind))
  any_goals (simp [points, Vector.get, eta_size])

@[grind .]
theorem point_eta_size_lt' : eta_size ((Expr.points e).get ⟨n, h⟩) < eta_size e := point_eta_size_lt (n := ⟨n, h⟩)

theorem set_point_eta_size_lt (h : n < point_arity e) (heq : Fin.mk n h = n₀) (hlt : p'.eta_size < (e.points.get (Fin.mk n h)).eta_size) : eta_size (set_points e ((Expr.points e).set n p' h)) < e.eta_size := by
  induction e
  any_goals (
    simp [point_arity] at h
    fin_cases n₀ <;> (
      cases heq
      simp [points, set_points, eta_size]
      simp [points, Vector.get] at hlt
      grind))
  any_goals (
    cases heq
    simp [point_arity] at h)

open Dsl in
inductive RedEta : Expr → Expr → Prop
  | comp_quot : RedEta (DCC (∘ (`B x) y)) (DCC (`B x))
  | id        : RedEta (DCC (∘ (Id x) y)) y
  | comp      : RedEta (DCC (∘ (∘ x y) z)) (DCC (∘ x (∘ y z)))
  | congrFun  : RedEta f f' → RedEta (DCC? (f x)) (DCC? (f' x))
  | congrArg  : RedEta x x' → RedEta (DCC? (f x)) (DCC? (f x'))
  | point     : (n : ℕ) → (h : n < point_arity e) → RedEta ((points e).get ⟨n, h⟩) p' → RedEta e (e.set_points ((points e).set n p'))

open Dsl in
inductive RedEta' : Expr → Expr → Type
  | comp_quot : RedEta' (DCC (∘ (`B x) y)) (DCC (`B x))
  | id        : RedEta' (DCC (∘ (Id x) y)) y
  | comp      : RedEta' (DCC (∘ (∘ x y) z)) (DCC (∘ x (∘ y z)))
  | congrFun  : RedEta' f f' → RedEta' (DCC? (f x)) (DCC? (f' x))
  | congrArg  : RedEta' x x' → RedEta' (DCC? (f x)) (DCC? (f x'))
  | point     : (n : ℕ) → (h : n < point_arity e) → RedEta' ((points e).get ⟨n, h⟩) p' → RedEta' e (e.set_points ((points e).set n p'))

def step_eta_head? (e : Expr) : Option (Σ (e' : Expr), PULift.{1, 0} (RedEta e e')) :=
  open Dsl in match e with
  | (DCC (∘ (`B x) y))
  | (DCC (∘ (Id x) y))
  | (DCC (∘ (∘ x y) z)) => .some ⟨_, ⟨by constructor⟩⟩
  | _ => .none

def step_eta_head'? (e : Expr) : Option (Σ (e' : Expr), RedEta' e e') :=
  open Dsl in match e with
  | (DCC (∘ (`B x) y))
  | (DCC (∘ (Id x) y))
  | (DCC (∘ (∘ x y) z)) => .some ⟨_, by constructor⟩
  | _ => .none

@[dcc_force_reduce, dcc_force_aff, aesop unsafe norm (rule_sets := [DccForceReduce])]
def step_eta? (e : Expr) : Option ((e' : Expr) × (PULift.{1, 0} (RedEta e e'))) :=
  open Dsl in match step_eta_head? e with
  | .some h => .some h
  | .none =>
    match e.cases_point_arity' with
    | .inl ⟨heq⟩ =>
      match e with
      | DCC? (f x) =>
        match f.step_eta?, x.step_eta? with
        | .some ⟨f', ⟨h₁⟩⟩, _ => .some ⟨(DCC? (f' x)), ⟨.congrFun h₁⟩⟩
        | _, .some ⟨x', ⟨h₁⟩⟩ => .some ⟨(DCC? (f x')), ⟨.congrArg h₁⟩⟩
        | _, _ => .none
      | _ => .none
    | .inr (.inl ⟨heq⟩) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step_eta? with
      | .some ⟨_, ⟨h₁⟩⟩ =>
        .some ⟨_, ⟨.point 0 (by simp [heq]) h₁⟩⟩
      | .none => .none
    | .inr (.inr (.inl ⟨heq⟩)) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step_eta?, (e.points.get ⟨1, by simp [heq]⟩).step_eta? with
      | .some ⟨_, ⟨h₁⟩⟩, _ =>
        .some ⟨_, ⟨.point 0 (by simp [heq]) h₁⟩⟩
      | _, .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.point 1 (by simp [heq]) h₂⟩⟩
      | _, _ => .none
    | .inr (.inr (.inr (.inl ⟨heq⟩))) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step_eta?, (e.points.get ⟨1, by simp [heq]⟩).step_eta? with
      | .some ⟨_, ⟨h₁⟩⟩, _ =>
        .some ⟨_, ⟨.point 0 (by simp [heq]) h₁⟩⟩
      | _, .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.point 1 (by simp [heq]) h₂⟩⟩
      | _, _ =>
        match (e.points.get ⟨2, by simp [heq]⟩).step_eta? with
        | .some ⟨_, ⟨h₃⟩⟩ =>
          .some ⟨_, ⟨.point 2 (by simp [heq]) h₃⟩⟩
        | .none => .none
    | .inr (.inr (.inr (.inr ⟨heq⟩))) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step_eta?, (e.points.get ⟨1, by simp [heq]⟩).step_eta? with
      | .some ⟨_, ⟨h₁⟩⟩, _ =>
        .some ⟨_, ⟨.point 0 (by simp [heq]) h₁⟩⟩
      | _, .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.point 1 (by simp [heq]) h₂⟩⟩
      | _, _ =>
        match (e.points.get ⟨2, by simp [heq]⟩).step_eta?, (e.points.get ⟨3, by simp [heq]⟩).step_eta? with
        | .some ⟨_, ⟨h₃⟩⟩, _ =>
          .some ⟨_, ⟨.point 2 (by simp [heq]) h₃⟩⟩
        | _, .some ⟨_, ⟨h₄⟩⟩ =>
          .some ⟨_, ⟨.point 3 (by simp [heq]) h₄⟩⟩
        | _, _ => .none
termination_by (e.eta_size, sizeOf e)
decreasing_by
  any_goals (grind)

@[dcc_force_reduce, dcc_force_aff, aesop unsafe norm (rule_sets := [DccForceReduce])]
def step_eta'? (e : Expr) : Option ((e' : Expr) × (RedEta' e e')) :=
  open Dsl in match step_eta_head'? e with
  | .some h => .some h
  | .none =>
    match e.cases_point_arity' with
    | .inl ⟨heq⟩ =>
      match e with
      | DCC? (f x) =>
        match f.step_eta'?, x.step_eta'? with
        | .some ⟨f', h₁⟩, _ => .some ⟨(DCC? (f' x)), .congrFun h₁⟩
        | _, .some ⟨x', h₁⟩ => .some ⟨(DCC? (f x')), .congrArg h₁⟩
        | _, _ => .none
      | _ => .none
    | .inr (.inl ⟨heq⟩) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step_eta'? with
      | .some ⟨_, h₁⟩ =>
        .some ⟨_, .point 0 (by simp [heq]) h₁⟩
      | .none => .none
    | .inr (.inr (.inl ⟨heq⟩)) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step_eta'?, (e.points.get ⟨1, by simp [heq]⟩).step_eta'? with
      | .some ⟨_, h₁⟩, _ =>
        .some ⟨_, .point 0 (by simp [heq]) h₁⟩
      | _, .some ⟨_, h₂⟩ =>
        .some ⟨_, .point 1 (by simp [heq]) h₂⟩
      | _, _ => .none
    | .inr (.inr (.inr (.inl ⟨heq⟩))) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step_eta'?, (e.points.get ⟨1, by simp [heq]⟩).step_eta'?, (e.points.get ⟨2, by simp [heq]⟩).step_eta'? with
      | .some ⟨_, h₁⟩, _, _ =>
        .some ⟨_, .point 0 (by simp [heq]) h₁⟩
      | _, .some ⟨_, h₂⟩, _ =>
        .some ⟨_, .point 1 (by simp [heq]) h₂⟩
      | _, _, .some ⟨_, h₃⟩ =>
          .some ⟨_, .point 2 (by simp [heq]) h₃⟩
      | _, _, _ => .none
    | .inr (.inr (.inr (.inr ⟨heq⟩))) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step_eta'?, (e.points.get ⟨1, by simp [heq]⟩).step_eta'?, (e.points.get ⟨2, by simp [heq]⟩).step_eta'?, (e.points.get ⟨3, by simp [heq]⟩).step_eta'? with
      | .some ⟨_, h₁⟩, _, _, _ =>
        .some ⟨_, .point 0 (by simp [heq]) h₁⟩
      | _, .some ⟨_, h₂⟩, _, _ =>
        .some ⟨_, .point 1 (by simp [heq]) h₂⟩
      | _, _, .some ⟨_, h₃⟩, _ =>
        .some ⟨_, .point 2 (by simp [heq]) h₃⟩
      | _, _, _, .some ⟨_, h₄⟩ =>
          .some ⟨_, .point 3 (by simp [heq]) h₄⟩
      | _, _, _, _ => .none
termination_by (e.eta_size, sizeOf e)
decreasing_by
  any_goals (grind)

set_option maxHeartbeats 10000000 in
@[dcc_force_reduce, dcc_force_aff]
instance RedEta.instRedRel : RedRel (α := Expr) RedEta eta_size where
  run := step_eta?
  decreasing := by
    intro x y h
    induction h
    case point =>
      expose_names
      have h := point_eta_size_lt' (n := n) (h := h)
      have h' : p'.eta_size < e.eta_size := by grind
      have h := set_point_eta_size_lt (by assumption) rfl (by assumption)
      simp_all
    any_goals (
      focus
      try dsimp
      try grind
      try simp_all [dcc_rel, dcc_size]
      try grind
      try aesop (rule_sets := [DccRel, DccSize])
      try rfl)

instance RedEta.instCongruent : Congruent RedEta where
  pil_ := fun h => .point 0 (by simp [point_arity]) h
  pir_ := fun h => .point 1 (by simp [point_arity]) h
  sigl_ := fun h => .point 1 (by simp [point_arity]) h
  sigr_ := fun h => .point 2 (by simp [point_arity]) h

theorem eta_point_trans (_hr : RedEta ((points e).get ⟨n, h⟩) p') (hr' : RedEta p' w) : RedEta ((points ((e.set_points ((points e).set n p')))).get ⟨n, by
  have h := congr_point_arr (e := e) (p := ⟨n, h⟩) (p' := p')
  grind⟩) w := by
  have h := get_set_point (e := e) (p := ⟨n, h⟩) (p' := p')
  simp [h]
  assumption

theorem eta_point_trans' (_hr : RedEta ((points e).get ⟨n, h⟩) p') (hr' : Relation.ReflTransGen RedEta p' w) : Relation.ReflTransGen RedEta ((points ((e.set_points ((points e).set n p')))).get ⟨n, by
  have h := congr_point_arr (e := e) (p := ⟨n, h⟩) (p' := p')
  grind⟩) w := by
  have h := get_set_point (e := e) (p := ⟨n, h⟩) (p' := p')
  simp [h]
  assumption

theorem eta_point' (hr : Relation.ReflTransGen RedEta ((points e).get ⟨n, h⟩) p') : Relation.ReflTransGen RedEta e (e.set_points ((points e).set n p')) :=
  match hr.cases_head with
  | .inl h => by
    cases h
    have heq := get_set_point (p := ⟨n, h⟩) (e := e) (p' := e.points.get ⟨n, h⟩)
    have heq' := get_set_point' (p := ⟨n, h⟩) (e := e) rfl
    simp [heq']
    exact Relation.ReflTransGen.refl
  | .inr ⟨_, h₁, h₂⟩ => by
    expose_names
    have h_dec := RedEta.instRedRel.decreasing h₁
    have h_dec₂ := decreasing? _ h₂
    have heq := set_same_point_comp (e := e) (x := w) (p := ⟨n, h⟩) (y := p')
    have hr' := RedEta.point _ _ h₁
    have hr'' := eta_point_trans' h₁ h₂
    have h_dec₃ := decreasing? _ hr''
    have h_dec₂ : (e.set_points (e.points.set n w h)).eta_size < e.eta_size := by
      have h_dec := RedEta.instRedRel.decreasing hr'
      grind
    have hrt' := eta_point' hr''
    have heq' := set_same_point_comp (e := e) (x := w) (p := ⟨n, h⟩) (y := p')
    simp [heq'] at hrt'
    exact Relation.ReflTransGen.trans (.single (.point n h h₁)) hrt'
termination_by e.eta_size

set_option maxHeartbeats 100000000000 in
theorem eta_mk_point' {x y e : Expr} (hr : Relation.ReflTransGen RedEta x y) (hn : n < point_arity e := by point_arity) (heq : (points e)[(Fin.mk n hn)] = x := by first | rfl | grind | (dcc_simp; rfl)) : Relation.ReflTransGen RedEta e (e.set_points ((points e).set n y)) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    unfold point_arity at hn
    split at hn
    any_goals (grind)
  | .inr ⟨_, h₁, h₂⟩ =>
    cases heq
    have h_dec := RedEta.instRedRel.decreasing h₁
    have hr' := eta_point' hr
    exact hr'

theorem aff_mk_point'' {x y e : Expr} (n : ℕ) (hr : RedEta x y := by assumption) (hn : n < point_arity e := by point_arity) (heq : (points e)[(Fin.mk n hn)] = x := by first | rfl | grind | (dcc_simp; rfl)) : Relation.ReflTransGen RedEta e (e.set_points ((points e).set n y)) := eta_mk_point' (.single hr)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
theorem RedEta.conf_point (h₁ : RedEta ((points e).get ⟨n, hn⟩) p') (h₂ : RedEta e C)
  (h : ∀ {C : Expr}, (e.points.get ⟨n, hn⟩).RedEta C → ∃ D, RedEta.instRedRel.ReflTrans p' D ∧ RedEta.instRedRel.ReflTrans C D) :
  ∃ D, RedEta.instRedRel.ReflTrans (e.set_points ((points e).set n p')) D ∧ RedEta.instRedRel.ReflTrans C D := by
  match cases_point_arity e with
  | .inl heq =>
    cases e
    any_goals (grind only [points, point_arity])
  | .inr (.inl heq) =>
    cases e
    any_goals (grind only [points, point_arity])
    any_goals (
      match n with
      | 0 =>
        match h₂ with
        | .point 0 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          exact ⟨_, eta_mk_point' h₁ (n := 0), eta_mk_point' h₂ (n := 0)⟩)
  | .inr (.inr (.inl heq)) =>
    cases e
    case comp =>
      match n with
      | 1 =>
        match h₂ with
        | .point 1 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, eta_mk_point' h₁ (n := 1) (hn := ?_) (heq := ?_), eta_mk_point' h₂ (n := 1) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 0 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 0 (by simp [point_arity]) hr), .single (.point 1 (by simp [point_arity]) h₁)⟩
        | .comp_quot =>
          simp_all [points, set_points, Vector.get]
          exact ⟨_, .single .comp_quot, .refl⟩
        | .id => exact ⟨_, .single .id, .single h₁⟩
        | .comp => exact ⟨_, .single .comp, .single (.point 1 (by grind) (.point 1 (by point_arity) h₁))⟩
      | 0 =>
        match h₂ with
        | .comp_quot =>
          match h₁ with
          | .point 0 hn h =>
            exact ⟨_, .single .comp_quot, .single (.point 0 (by grind) h)⟩
          | .point 1 hn h =>
            exact ⟨_, .single .comp_quot, .single (.point 1 (by grind) h)⟩
        | .id =>
          simp_all [points, set_points, Vector.get]
          match h₁ with
          | .point 0 hn h =>
            exact ⟨_, .single .id, .refl⟩
        | .comp =>
          simp_all [points, set_points, Vector.get]
          match h₁ with
          | .comp =>
             expose_names
             exact ⟨(x_1.comp (y_1.comp (y.comp a_1))), .trans (.single .comp) (.single (.point 1 (by grind) .comp)), (.single (by constructor))⟩
           | .id =>
             exact ⟨_, .refl, .single .id⟩
           | .comp_quot =>
             exact ⟨_, .single .comp_quot, .single .comp_quot⟩
           | .point 0 hn h =>
             exact ⟨_, by
               simp [set_points, points]
               exact .single .comp, .single (.point 0 (by grind) h)⟩
           | .point 1 hn h =>
             simp_all [points, set_points, Vector.get]
             expose_names
             exact ⟨_, by
               change Relation.ReflTransGen RedEta ((a_2.comp p'_1).comp a_1) (a_2.comp (p'_1.comp a_1))
               exact .single .comp, .single (.point 1 (by grind) (.point 0 (by simp [points, Vector.get]; grind) h))⟩
        | .point 0 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, eta_mk_point' h₁ (n := 0) (hn := ?_) (heq := ?_), eta_mk_point' h₂ (n := 0) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 1 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 1 (by simp [point_arity]) hr), .single (.point 0 (by simp [point_arity]) h₁)⟩
    any_goals (grind only [points, point_arity])
    any_goals (
      match n with
      | 0 =>
        match h₂ with
        | .point 0 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, eta_mk_point' h₁ (n := 0) (hn := ?_) (heq := ?_), eta_mk_point' h₂ (n := 0) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 1 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 1 (by simp [point_arity]) hr), .single (.point 0 (by simp [point_arity]) h₁)⟩
      | 1 =>
        match h₂ with
        | .point 1 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, eta_mk_point' h₁ (n := 1) (hn := ?_) (heq := ?_), eta_mk_point' h₂ (n := 1) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 0 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 0 (by simp [point_arity]) hr), .single (.point 1 (by simp [point_arity]) h₁)⟩)
  | .inr (.inr (.inr (.inl heq))) =>
    cases e
    any_goals (grind only [points, point_arity])
    any_goals (
      match n with
      | 0 =>
        match h₂ with
        | .point 0 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, eta_mk_point' h₁ (n := 0) (hn := ?_) (heq := ?_), eta_mk_point' h₂ (n := 0) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 1 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 1 (by simp [point_arity]) hr), .single (.point 0 (by simp [point_arity]) h₁)⟩
        | .point 2 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 2 (by simp [point_arity]) hr), .single (.point 0 (by simp [point_arity]) h₁)⟩
      | 1 =>
        match h₂ with
        | .point 1 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, eta_mk_point' h₁ (n := 1) (hn := ?_) (heq := ?_), eta_mk_point' h₂ (n := 1) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 0 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 0 (by simp [point_arity]) hr), .single (.point 1 (by simp [point_arity]) h₁)⟩
        | .point 2 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 2 (by simp [point_arity]) hr), .single (.point 1 (by simp [point_arity]) h₁)⟩
      | 2 =>
        match h₂ with
        | .point 2 hn hr =>
          have ⟨_, h₁, h₂⟩ := h hr
          refine ⟨_, eta_mk_point' h₁ (n := 2) (hn := ?_) (heq := ?_), eta_mk_point' h₂ (n := 2) (hn := ?_) (heq := ?_)⟩
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
          · simp [point_arity, set_points]
          · simp [set_points, points]; rfl
        | .point 0 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 0 (by simp [point_arity]) hr), .single (.point 2 (by simp [point_arity]) h₁)⟩
        | .point 1 hn hr =>
          simp [points, set_points]
          exact ⟨_, .single (.point 1 (by simp [point_arity]) hr), .single (.point 2 (by simp [point_arity]) h₁)⟩)
  | .inr (.inr (.inr (.inr heq))) =>
    cases e
    any_goals (grind only [points, point_arity])

open Congruent in
theorem RedEta.conf (h₁ : RedEta A B) (h₂ : RedEta A C) : ∃ D, Relation.ReflTransGen RedEta B D ∧ Relation.ReflTransGen RedEta C D := by
  induction h₁ generalizing C
  case point h ih => exact RedEta.conf_point h h₂ ih
  all_goals (cases h₂)
  any_goals (exact ⟨_, .refl, .refl⟩)
  any_goals (
    expose_names
    simp [point_arity] at h
    interval_cases n)
  · simp [points, set_points]
    simp [points, Vector.get] at h_1
    cases h_1
    case point n_1 h hr =>
      expose_names
      simp [point_arity] at h
      interval_cases n_1
      <;> (
        simp [points, Vector.get] at hr
        simp [points, set_points]
        first
        | exact ⟨_, .single (.point 0 (by grind) hr), .single (by constructor)⟩
        | exact ⟨_, .single (.point 1 (by grind) hr), .single (by constructor)⟩)
  · exact ⟨_, .refl, .single (by constructor)⟩
  · match h_1 with
    | .point 0 hn h =>
      simp_all [points, set_points, Vector.get]
      exact ⟨_, .refl, .single (by constructor)⟩
  · simp_all [points, set_points, Vector.get]
    exact ⟨_, .single h_1, .single (by constructor)⟩
  · simp_all [points, set_points, Vector.get]
    match h_1 with
    | .comp =>
      expose_names
      exact ⟨(x_1.comp (y_1.comp (y.comp z))), (.single (by constructor)), .trans (.single .comp) (.single (.point 1 (by grind) .comp))⟩
    | .id =>
      exact ⟨_, .single .id, .refl⟩
    | .comp_quot =>
      exact ⟨_, .single .comp_quot, .single .comp_quot⟩
    | .point 0 hn h =>
      exact ⟨_, .single (.point 0 (by grind) h), by
        simp [set_points, points]
        exact .single .comp⟩
    | .point 1 hn h =>
      simp_all [points, set_points, Vector.get]
      expose_names
      exact ⟨_, .single (.point 1 (by grind) (.point 0 (by simp [points, Vector.get]; grind) h)), by
        change Relation.ReflTransGen RedEta ((x.comp p'_1).comp z) (x.comp (p'_1.comp z))
        exact .single .comp⟩
  · exact ⟨_, .single (.point 1 (by grind) (.point 1 (by simp [points, Vector.get]; grind) h_1)), by
    change Relation.ReflTransGen RedEta ((x.comp y).comp p') (x.comp (y.comp p'))
    exact .single .comp⟩
  · expose_names
    have ⟨_, h₁, h₂⟩ := a_ih h_1
    exact ⟨_, congrFun' h₁, congrFun' h₂⟩
  · expose_names
    exact ⟨_, .single (.congrArg h_1), .single (.congrFun h)⟩
  any_goals (grind [point_arity])
  · expose_names
    exact ⟨_, .single (.congrFun h_1), .single (.congrArg h)⟩
  · expose_names
    have ⟨_, h₁, h₂⟩ := a_ih h_1
    exact ⟨_, congrArg' h₁, congrArg' h₂⟩

theorem RedEta.semi_complete {A B : Expr} (hr : A.RedEta B) : ∃ B', ∃ (h : A.RedEta B'), (step_eta? A) = .some ⟨B', ⟨h⟩⟩ :=
  match hr with
  | .congrFun hr => by
    have ⟨_, hr', heq'⟩ := semi_complete hr
    unfold step_eta?
    simp [step_eta_head?, cases_point_arity', point_arity, heq']
    exact .congrFun hr'
  | .congrArg hr => by
    have ⟨_, hr', heq'⟩ := semi_complete hr
    unfold step_eta?
    simp [step_eta_head?, cases_point_arity', point_arity, heq']
    split
    case h_1 =>
      expose_names
      exact ⟨_, .congrFun h₁, rfl⟩
    case h_2 =>
      expose_names
      exact ⟨_, .congrArg h₁, rfl⟩
    · grind
  | .point n hlt hr => by
    have ⟨_, hr', heq'⟩ := semi_complete hr
    match heq₀ : A.cases_point_arity' with
    | .inl ⟨heq⟩ => grind
    | .inr (.inl ⟨heq⟩) =>
      simp [heq] at hlt
      cases hlt
      unfold step_eta?
      unfold step_eta_head?
      split
      · grind
      case h_2 =>
        expose_names
        simp [heq₀, heq']
        exact .point 0 hlt hr'
    | .inr (.inr (.inl ⟨heq⟩)) =>
      simp [heq] at hlt
      unfold step_eta?
      unfold step_eta_head?
      split
      case h_1 heq'' =>
        split at heq''
        <;> (
          cases heq''
          try (exact ⟨_, by constructor, rfl⟩))
      case h_2 =>
        expose_names
        simp [heq₀]
        interval_cases n
        · simp [heq']
          exact .point 0 (by grind) hr'
        · simp [heq']
          split
          · exact ⟨_, .point 0 (by grind) (by assumption), rfl⟩
          · exact ⟨_, .point 1 (by grind) (by assumption), rfl⟩
          · grind
    | .inr (.inr (.inr (.inl ⟨heq⟩))) =>
      simp [heq] at hlt
      unfold step_eta?
      unfold step_eta_head?
      split
      · grind
      case h_2 =>
        simp [heq₀]
        interval_cases n
        · simp [heq']
          exact .point 0 (by grind) hr'
        · simp [heq']
          split
          · exact ⟨_, .point 0 (by grind) (by assumption), rfl⟩
          · exact ⟨_, .point 1 (by grind) (by assumption), rfl⟩
          · grind
        · simp [heq']
          split
          · exact ⟨_, .point 0 (by grind) (by assumption), rfl⟩
          · exact ⟨_, .point 1 (by grind) (by assumption), rfl⟩
          · exact ⟨_, .point 2 (by grind) (by assumption), rfl⟩
    | .inr (.inr (.inr (.inr ⟨heq⟩))) =>
      simp [heq] at hlt
      unfold step_eta?
      unfold step_eta_head?
      split
      · grind
      case h_2 =>
        simp [heq₀]
        interval_cases n
        · simp [heq']
          exact .point 0 (by grind) hr'
        · simp [heq']
          split
          · exact ⟨_, .point 0 (by grind) (by assumption), rfl⟩
          · exact ⟨_, .point 1 (by grind) (by assumption), rfl⟩
          · grind
        · simp [heq']
          split
          · exact ⟨_, .point 0 (by grind) (by assumption), rfl⟩
          · exact ⟨_, .point 1 (by grind) (by assumption), rfl⟩
          · exact ⟨_, .point 2 (by grind) (by assumption), rfl⟩
        · simp [heq']
          split
          · exact ⟨_, .point 0 (by grind) (by assumption), rfl⟩
          · exact ⟨_, .point 1 (by grind) (by assumption), rfl⟩
          · split
            · exact ⟨_, .point 2 (by grind) (by assumption), rfl⟩
            · exact ⟨_, .point 3 (by grind) (by assumption), rfl⟩
            · grind
  | .id | .comp | .comp_quot => by simp [step_eta?, step_eta_head?]; constructor

instance : Confluent RedEta := ⟨RedEta.conf⟩
instance : SemiComplete RedEta := ⟨RedEta.semi_complete⟩

end Expr
