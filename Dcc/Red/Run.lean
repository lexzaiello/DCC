import Dcc.Red.Rel
import Dcc.Red.RelationProp
import Mathlib.Tactic

namespace Expr

open Dsl

@[dcc_force_reduce, dcc_force_aff, aesop unsafe norm (rule_sets := [DccForceReduce])]
def step_head? (e : Expr) : Option ((e' : Expr) × (PULift.{1, 0} (Red e e'))) :=
  match e with
  | (DCC? ((Σ' _B _C) (& _x))) => .some ⟨_, ⟨.sigma⟩⟩
  | (DCC? ((𝟚.Rec _motive _x _y) _env 𝟙₂)) =>
    .some ⟨_, ⟨.ind_bool_true⟩⟩
  | (DCC? ((𝟚.Rec _motive _x _y) _env 𝟘₂)) =>
    .some ⟨_, ⟨.ind_bool_false⟩⟩
  | DCC? ((!<> _f) (& _x))                                 => .some ⟨_, ⟨.map⟩⟩
  | DCC? (($<> _f) (& _x))                                 => .some ⟨_, ⟨.fmap⟩⟩
  | DCC? ((* _α) (& _x))                                 => .some ⟨_, ⟨.unbox⟩⟩
  | DCC? ((⟨,⟩_β _M _N) (& _x))                        => .some ⟨_, ⟨.pair⟩⟩
  | (DCC? ((Eval _α _β _x) (,__β _y _z)))            => .some ⟨_, ⟨.evalc⟩⟩
  | (DCC? ((Eql _f_α) (& _env) (& _y)))              => .some ⟨_, ⟨.eql⟩⟩
  | (DCC? ((=' _f_α) _x _y _z))              => .some ⟨_, ⟨.eq_mk⟩⟩
  | (DCC? ((`_β _x) _y))                             => .some ⟨_, ⟨.quot⟩⟩
  | (DCC? ((Id _α) _x))                                => .some ⟨_, ⟨.id⟩⟩
  | (DCC? ((Fst _α) (,_γ _a _b)))                     => .some ⟨_, ⟨.fstc⟩⟩
  | (DCC? ((Swap _B _C) (,_B₂ _a _b)))                 => .some ⟨_, ⟨.swap⟩⟩
  | (DCC? ((Snd _α) (,_γ _a _b)))                     => .some ⟨_, ⟨.sndc⟩⟩
  | (DCC? ((∘ _x _y) _z))                              => .some ⟨_, ⟨.comp⟩⟩
  | (DCC? ((!Λ _α _β _x) (& _y) (& _z)))                => .some ⟨_, ⟨.curr'⟩⟩
  | (DCC? ((Λ _α _β _x) _y _z)) => .some ⟨_, ⟨.curr⟩⟩
  | _ => .none

@[dcc_force_reduce, dcc_force_aff, aesop unsafe norm (rule_sets := [DccForceReduce])]
def step_head?' (e : Expr) : Option ((e' : Expr) × Red' e e') :=
  match e with
  | (DCC? ((Σ' _B _C) (& _x))) => .some ⟨_, .sigma⟩
  | (DCC? ((𝟚.Rec _motive _x _y) _env 𝟙₂)) =>
    .some ⟨_, .ind_bool_true⟩
  | (DCC? ((𝟚.Rec _motive _x _y) _env 𝟘₂)) =>
    .some ⟨_, .ind_bool_false⟩
  | DCC? ((!<> _f) (& _x))                                 => .some ⟨_, .map⟩
  | DCC? (($<> _f) (& _x))                                 => .some ⟨_, .fmap⟩
  | DCC? ((* _α) (& _x))                                 => .some ⟨_, .unbox⟩
  | DCC? ((⟨,⟩_β _M _N) (& _x))                        => .some ⟨_, .pair⟩
  | (DCC? ((Eval _α _β _x) (,__β _y _z)))            => .some ⟨_, .evalc⟩
  | (DCC? ((Eql _f_α) (& _env) (& _y)))              => .some ⟨_, .eql⟩
  | (DCC? ((=' _f_α) _x _y _z))              => .some ⟨_, .eq_mk⟩
  | (DCC? ((`_β _x) _y))                             => .some ⟨_, .quot⟩
  | (DCC? ((Id _α) _x))                                => .some ⟨_, .id⟩
  | (DCC? ((Fst _α) (,_γ _a _b)))                     => .some ⟨_, .fstc⟩
  | (DCC? ((Swap _B _C) (,_B₂ _a _b)))                 => .some ⟨_, .swap⟩
  | (DCC? ((Snd _α) (,_γ _a _b)))                     => .some ⟨_, .sndc⟩
  | (DCC? ((∘ _x _y) _z))                              => .some ⟨_, .comp⟩
  | (DCC? ((!Λ _α _β _x) (& _y) (& _z)))                => .some ⟨_, .curr'⟩
  | (DCC? ((Λ _α _β _x) _y _z)) => .some ⟨_, .curr⟩
  | _ => .none

@[dcc_force_reduce, dcc_force_aff, aesop unsafe norm (rule_sets := [DccForceReduce])]
def step? (e : Expr) : Option ((e' : Expr) × (PULift.{1, 0} (Red e e'))) :=
  open Dsl in match step_head? e with
  | .some h => .some h
  | .none =>
    match e.cases_point_arity' with
    | .inl ⟨heq⟩ =>
      match e with
      | DCC? (f x) =>
        match f.step?, x.step? with
        | .some ⟨f', ⟨h₁⟩⟩, _ => .some ⟨(DCC? (f' x)), ⟨.congrFun h₁⟩⟩
        | _, .some ⟨x', ⟨h₁⟩⟩ => .some ⟨(DCC? (f x')), ⟨.congrArg h₁⟩⟩
        | _, _ => .none
      | _ => .none
    | .inr (.inl ⟨heq⟩) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step? with
      | .some ⟨_, ⟨h₁⟩⟩ =>
        .some ⟨_, ⟨.point 0 (by simp [heq]) h₁⟩⟩
      | .none => .none
    | .inr (.inr (.inl ⟨heq⟩)) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step?, (e.points.get ⟨1, by simp [heq]⟩).step? with
      | .some ⟨_, ⟨h₁⟩⟩, _ =>
        .some ⟨_, ⟨.point 0 (by simp [heq]) h₁⟩⟩
      | _, .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.point 1 (by simp [heq]) h₂⟩⟩
      | _, _ => .none
    | .inr (.inr (.inr (.inl ⟨heq⟩))) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step?, (e.points.get ⟨1, by simp [heq]⟩).step? with
      | .some ⟨_, ⟨h₁⟩⟩, _ =>
        .some ⟨_, ⟨.point 0 (by simp [heq]) h₁⟩⟩
      | _, .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.point 1 (by simp [heq]) h₂⟩⟩
      | _, _ =>
        match (e.points.get ⟨2, by simp [heq]⟩).step? with
        | .some ⟨_, ⟨h₃⟩⟩ =>
          .some ⟨_, ⟨.point 2 (by simp [heq]) h₃⟩⟩
        | .none => .none
    | .inr (.inr (.inr (.inr ⟨heq⟩))) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step?, (e.points.get ⟨1, by simp [heq]⟩).step? with
      | .some ⟨_, ⟨h₁⟩⟩, _ =>
        .some ⟨_, ⟨.point 0 (by simp [heq]) h₁⟩⟩
      | _, .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.point 1 (by simp [heq]) h₂⟩⟩
      | _, _ =>
        match (e.points.get ⟨2, by simp [heq]⟩).step?, (e.points.get ⟨3, by simp [heq]⟩).step? with
        | .some ⟨_, ⟨h₃⟩⟩, _ =>
          .some ⟨_, ⟨.point 2 (by simp [heq]) h₃⟩⟩
        | _, .some ⟨_, ⟨h₄⟩⟩ =>
          .some ⟨_, ⟨.point 3 (by simp [heq]) h₄⟩⟩
        | _, _ => .none
termination_by (e.size, sizeOf e)
decreasing_by
  any_goals (grind)

@[dcc_force_reduce, dcc_force_aff, aesop unsafe norm (rule_sets := [DccForceReduce])]
def step?' (e : Expr) : Option ((e' : Expr) × (Red' e e')) :=
  open Dsl in match step_head?' e with
  | .some h => .some h
  | .none =>
    match e.cases_point_arity' with
    | .inl ⟨heq⟩ =>
      match e with
      | DCC? (f x) =>
        match f.step?', x.step?' with
        | .some ⟨f', h₁⟩, _ => .some ⟨(DCC? (f' x)), .congrFun h₁⟩
        | _, .some ⟨x', h₁⟩ => .some ⟨(DCC? (f x')), .congrArg h₁⟩
        | _, _ => .none
      | _ => .none
    | .inr (.inl ⟨heq⟩) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step?' with
      | .some ⟨_, h₁⟩ =>
        .some ⟨_, .point 0 (by simp [heq]) h₁⟩
      | .none => .none
    | .inr (.inr (.inl ⟨heq⟩)) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step?', (e.points.get ⟨1, by simp [heq]⟩).step?' with
      | .some ⟨_, h₁⟩, _ =>
        .some ⟨_, .point 0 (by simp [heq]) h₁⟩
      | _, .some ⟨_, h₂⟩ =>
        .some ⟨_, .point 1 (by simp [heq]) h₂⟩
      | _, _ => .none
    | .inr (.inr (.inr (.inl ⟨heq⟩))) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step?', (e.points.get ⟨1, by simp [heq]⟩).step?', (e.points.get ⟨2, by simp [heq]⟩).step?' with
      | .some ⟨_, h₁⟩, _, _ =>
        .some ⟨_, .point 0 (by simp [heq]) h₁⟩
      | _, .some ⟨_, h₂⟩, _ =>
        .some ⟨_, .point 1 (by simp [heq]) h₂⟩
      | _, _, .some ⟨_, h₃⟩ =>
          .some ⟨_, .point 2 (by simp [heq]) h₃⟩
      | _, _, _ => .none
    | .inr (.inr (.inr (.inr ⟨heq⟩))) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step?', (e.points.get ⟨1, by simp [heq]⟩).step?', (e.points.get ⟨2, by simp [heq]⟩).step?', (e.points.get ⟨3, by simp [heq]⟩).step?' with
      | .some ⟨_, h₁⟩, _, _, _ =>
        .some ⟨_, .point 0 (by simp [heq]) h₁⟩
      | _, .some ⟨_, h₂⟩, _, _ =>
        .some ⟨_, .point 1 (by simp [heq]) h₂⟩
      | _, _, .some ⟨_, h₃⟩, _ =>
        .some ⟨_, .point 2 (by simp [heq]) h₃⟩
      | _, _, _, .some ⟨_, h₄⟩ =>
          .some ⟨_, .point 3 (by simp [heq]) h₄⟩
      | _, _, _, _ => .none
termination_by (e.size, sizeOf e)
decreasing_by
  any_goals (grind)

set_option maxHeartbeats 10000000 in
theorem Red.has_step?' (h : Red A B) : ∃ C h, step?' A = .some ⟨C, h⟩ := by
  induction h
  case congrFun =>
    unfold step?'
    split
    · grind
    · expose_names
      simp [cases_point_arity', point_arity]
      have ⟨C, h, heq⟩ := a_ih
      simp [heq]
  case congrArg =>
    unfold step?'
    split
    · grind
    · expose_names
      simp [cases_point_arity', point_arity]
      have ⟨C, h, heq⟩ := a_ih
      simp [heq]
      split <;> grind
  case point =>
    expose_names
    cases e
    all_goals (
      dsimp [point_arity] at h
      interval_cases n)
    any_goals (
      have ⟨C, h, heq⟩ := a_ih
      unfold step?'
      simp [step_head?', cases_point_arity', point_arity]
      split
      any_goals (grind)
      any_goals (
        simp_all [points, Vector.get]
        try (grind)))
  any_goals (simp [step?', step_head?'])

theorem Red.step?'_some (h : Red A B) : (step?' A).isSome := by
  have ⟨C, h, heq⟩ := h.has_step?'
  grind

set_option maxHeartbeats 10000000 in
@[dcc_force_reduce, dcc_force_aff]
instance Red.instRedRel : RedRel (α := Expr) Red size where
  run := step?
  decreasing := by
    intro x y h
    induction h
    case point =>
      expose_names
      have h := point_size_lt' (n := n) (h := h)
      have h' : p'.size < e.size := by grind
      have h := set_point_size_lt (by assumption) rfl (by assumption)
      simp_all
    any_goals (
      focus
      try dsimp
      try grind
      try simp_all [dcc_rel, dcc_size]
      try grind
      try aesop (rule_sets := [DccRel, DccSize])
      try rfl)

theorem red_aff_sn : ∀ (e : Expr), Acc (fun b a => Red a b) e :=
  Red.instRedRel.sn

theorem red_aff_trans_sn [DecidableEq τ] : ∀ (e : Expr), Acc (fun b a => Relation.TransGen Red a b) e :=
  Red.instRedRel.to_trans.sn

theorem congrFun' {f x f' : Expr} (hr : Relation.ReflTransGen Red f f') : Relation.ReflTransGen Red (DCC? (f x)) (DCC? (f' x)) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := Red.instRedRel.decreasing h₁
    exact .trans (.single (.congrFun h₁)) (congrFun' h₂)
termination_by size f

theorem swap₀' {x x' : Expr} (hr : Relation.ReflTransGen Red x x') : Relation.ReflTransGen Red (DCC? (Swap x _y)) (DCC? (Swap x' _y)) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := Red.instRedRel.decreasing h₁
    exact .trans (.single (.point 0 (by grind) h₁)) (swap₀' (by assumption))
termination_by x.size

theorem swap₁' {x x' : Expr} (hr : Relation.ReflTransGen Red x x') : Relation.ReflTransGen Red (DCC? (Swap _x x)) (DCC? (Swap _x x')) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := Red.instRedRel.decreasing h₁
    exact .trans (.single (.point 1 (by grind) h₁)) (swap₁' (by assumption))
termination_by x.size

theorem congrArg' {x x' : Expr} (hr : Relation.ReflTransGen Red x x') : Relation.ReflTransGen Red (DCC? (f x)) (DCC? (f x')) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := Red.instRedRel.decreasing h₁
    exact .trans (.single (.congrArg h₁)) (congrArg' h₂)
termination_by size x

theorem point' (hr : Relation.ReflTransGen Red ((points e).get ⟨n, h⟩) p') : Relation.ReflTransGen Red e (e.set_points ((points e).set n p')) :=
  match hr.cases_head with
  | .inl h => by
    cases h
    have heq := get_set_point (p := ⟨n, h⟩) (e := e) (p' := e.points.get ⟨n, h⟩)
    have heq' := get_set_point' (p := ⟨n, h⟩) (e := e) rfl
    simp [heq']
    exact Relation.ReflTransGen.refl
  | .inr ⟨_, h₁, h₂⟩ => by
    expose_names
    have h_dec := Red.instRedRel.decreasing h₁
    have h_dec₂ := decreasing? _ h₂
    have heq := set_same_point_comp (e := e) (x := w) (p := ⟨n, h⟩) (y := p')
    have hr' := Red.point _ _ h₁
    have hr'' := point_trans' h₁ h₂
    have h_dec₃ := decreasing? _ hr''
    have h_dec₂ : (e.set_points (e.points.set n w h)).size < e.size := by
      have h_dec := Red.instRedRel.decreasing hr'
      grind
    have hrt' := point' hr''
    have heq' := set_same_point_comp (e := e) (x := w) (p := ⟨n, h⟩) (y := p')
    simp [heq'] at hrt'
    exact Relation.ReflTransGen.trans (.single (.point n h h₁)) hrt'
termination_by e.size

set_option maxHeartbeats 100000000000 in
theorem aff_mk_point' {x y e : Expr} (hr : Relation.ReflTransGen Red x y) (hn : n < point_arity e := by point_arity) (heq : (points e)[(Fin.mk n hn)] = x := by first | rfl | grind | (dcc_simp; rfl)) : Relation.ReflTransGen Red e (e.set_points ((points e).set n y)) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    unfold point_arity at hn
    split at hn
    any_goals (grind)
  | .inr ⟨_, h₁, h₂⟩ =>
    cases heq
    have h_dec := Red.instRedRel.decreasing h₁
    have hr' := point' hr
    exact hr'

theorem aff_mk_point'' {x y e : Expr} (n : ℕ) (hr : Red x y := by assumption) (hn : n < point_arity e := by point_arity) (heq : (points e)[(Fin.mk n hn)] = x := by first | rfl | grind | (dcc_simp; rfl)) : Relation.ReflTransGen Red e (e.set_points ((points e).set n y)) := aff_mk_point' (.single hr)

end Expr
