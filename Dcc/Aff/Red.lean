import Dcc.Attrs
import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Size
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

namespace GenericExpr

/-
Preservation proof:
- can make these more type-directed
-/

@[aesop safe (rule_sets := [DccForceStep]) [constructors], aesop unsafe 50% (rule_sets := [DccForceStep]) [cases]]
inductive RedAff.{u} {τ : Type u} : GenericExpr τ → GenericExpr τ → Prop
/-
Core reductions:
-/
  | eql      : RedAff (DCC[τ] (Eql(f_α) &(env) &(x))) (DCC[τ] x = x)
  | map      : RedAff (DCC[τ] (!<f> &(x))) (DCC[τ] !((f x)))
  | fmap     : RedAff (DCC[τ] ($<f> &(x))) (DCC[τ] &((f x)))
  | unmap    : RedAff (DCC[τ] (*<f> &(x))) (DCC[τ] (f x))
  | pair     : RedAff (DCC[τ] (⟦β⟧⟨M, N⟩ &(x))) (DCC[τ] ⟦(β x)⟧((M x), (N x (M x))))
  | evalc    : RedAff (DCC[τ] (Eval(_α, _β, x) ⟦__β⟧(y, z))) (DCC[τ] (x y z))
  | quot     : RedAff (DCC[τ] (`(β, x) y)) x
  | id       : RedAff (DCC[τ] (Id(α) x)) x
  | fstc     : RedAff (DCC[τ] (Fst(_α) ⟦β⟧(a, b))) a
  | sndc     : RedAff (DCC[τ] (Snd(_α) ⟦β⟧(a, b))) b
  | comp'    : RedAff (DCC[τ] ((x ∘' y) z)) (DCC[τ] (x (y z)))
  | comp     : RedAff (DCC[τ] ((x ∘ y) z)) (DCC[τ] (x (y z)))
  | comp₂    : RedAff (DCC[τ] ((x ∘∘ y) z)) (DCC[τ] (x (y z)))
  | curr     : RedAff (DCC[τ] (Λ(α, β, x) y z)) (DCC[τ] (x ⟦β⟧(y, z)))
  | curr'    : RedAff (DCC[τ] (!Λ(α, β, x) &(y) &(z))) (DCC[τ] (x &(⟦β⟧(y, z))))
  | sigma    : RedAff (DCC[τ] (Σ(f_α, f_β) env)) (DCC[τ] (Coup((f_β env))))
/-
Inner congruences:
-/
-- `(B, x)
  | quot₀    : RedAff B B' → RedAff (DCC[τ] `(B, x)) (DCC[τ] `(B', x))
  | quot₁    : RedAff x x' → RedAff (DCC[τ] `(B, x)) (DCC[τ] `(B, x'))
-- Σ(B, C)
  | sigma₀   : RedAff B B' → RedAff (DCC[τ] Σ(B, C)) (DCC[τ] Σ(B', C))
  | sigma₁   : RedAff C C' → RedAff (DCC[τ] Σ(B, C)) (DCC[τ] Σ(B, C'))
-- Π(B, C)
  | pi₀      : RedAff B B' → RedAff (DCC[τ] Π(B, C)) (DCC[τ] Π(B', C))
  | pi₁      : RedAff C C' → RedAff (DCC[τ] Π(B, C)) (DCC[τ] Π(B, C'))
  -- x = y
  | eq₀      : RedAff x x' → RedAff (DCC[τ] (x = y)) (DCC[τ] (x' = y))
  | eq₁      : RedAff y y' → RedAff (DCC[τ] (x = y)) (DCC[τ] (x = y'))
  -- Eql(B)
  | eql₀     : RedAff B B' → RedAff (DCC[τ] Eql(B)) (DCC[τ] Eql(B'))
  -- refl(B)
  | refl₀    : RedAff B B' → RedAff (DCC[τ] refl(B)) (DCC[τ] refl(B'))
  -- Id(A)
  | id₀      : RedAff A A' → RedAff (DCC[τ] Id(A)) (DCC[τ] Id(A'))
  -- Fstc(B)
  | fstc₀    : RedAff B B' → RedAff (DCC[τ] Fst(B)) (DCC[τ] Fst(B'))
  -- Sndc(B)
  | sndc₀    : RedAff B B' → RedAff (DCC[τ] Snd(B)) (DCC[τ] Snd(B'))
  -- !(x)
  | bang₀    : RedAff x x' → RedAff (DCC[τ] !(x)) (DCC[τ] !(x'))
  -- &(x)
  | box₀     : RedAff x x' → RedAff (DCC[τ] &(x)) (DCC[τ] &(x'))
  -- !<x>
  | map₀     : RedAff f f' → RedAff (DCC? !<f>) (DCC? !<f'>)
  -- $<x>
  | fmap₀    : RedAff f f' → RedAff (DCC? $<f>) (DCC? $<f'>)
  -- *<x>
  | unmap₀   : RedAff f f' → RedAff (DCC? *<f>) (DCC? *<f'>)
  -- Λ(A, B, x)
  | curr₀    : RedAff A A' → RedAff (DCC[τ] (Λ(A, B, x))) (DCC[τ] (Λ(A', B, x)))
  | curr₁    : RedAff B B' → RedAff (DCC[τ] (Λ(A, B, x))) (DCC[τ] (Λ(A, B', x)))
  | curr₂    : RedAff x x' → RedAff (DCC[τ] (Λ(A, B, x))) (DCC[τ] (Λ(A, B, x')))
  -- Eval(A, B, x)
  | eval₀    : RedAff A A' → RedAff (DCC[τ] (Eval(A, B, x))) (DCC[τ] (Eval(A', B, x)))
  | eval₁    : RedAff B B' → RedAff (DCC[τ] (Eval(A, B, x))) (DCC[τ] (Eval(A, B', x)))
  | eval₂    : RedAff x x' → RedAff (DCC[τ] (Eval(A, B, x))) (DCC[τ] (Eval(A, B, x')))
  -- !Λ(A, B, x)
  | curr'₀   : RedAff A A' → RedAff (DCC[τ] (!Λ(A, B, x))) (DCC[τ] (!Λ(A', B, x)))
  | curr'₁   : RedAff B B' → RedAff (DCC[τ] (!Λ(A, B, x))) (DCC[τ] (!Λ(A, B', x)))
  | curr'₂   : RedAff x x' → RedAff (DCC[τ] (!Λ(A, B, x))) (DCC[τ] (!Λ(A, B, x')))
  -- ⟦B⟧(x, y)
  | sig₀     : RedAff B B' → RedAff (DCC[τ] ⟦B⟧(x, y)) (DCC[τ] ⟦B'⟧(x, y))
  | sig₁     : RedAff x x' → RedAff (DCC[τ] ⟦β⟧(x, y)) (DCC[τ] ⟦β⟧(x', y))
  | sig₂     : RedAff y y' → RedAff (DCC[τ] ⟦β⟧(x, y)) (DCC[τ] ⟦β⟧(x, y'))
  -- ⟦B⟧⟨x, y⟩
  | pair₀    : RedAff B B' → RedAff (DCC[τ] ⟦B⟧⟨x, y⟩) (DCC[τ] ⟦B'⟧⟨x, y⟩)
  | pair₁    : RedAff x x' → RedAff (DCC[τ] ⟦β⟧⟨x, y⟩) (DCC[τ] ⟦β⟧⟨x', y⟩)
  | pair₂    : RedAff y y' → RedAff (DCC[τ] ⟦β⟧⟨x, y⟩) (DCC[τ] ⟦β⟧⟨x, y'⟩)
  -- Coup(B)
  | coup₀    : RedAff β β' → RedAff (DCC[τ] (Coup(β))) (DCC[τ] (Coup(β')))
  -- x and y in x ∘' y
  | comp'₀   : RedAff x x' → RedAff (DCC[τ] x ∘' y) (DCC[τ] x' ∘' y)
  | comp'₁   : RedAff y y' → RedAff (DCC[τ] x ∘' y) (DCC[τ] x ∘' y')
  -- x and y in x ∘ y
  | comp₀    : RedAff x x' → RedAff (DCC[τ] x ∘ y) (DCC[τ] x' ∘ y)
  | comp₁    : RedAff y y' → RedAff (DCC[τ] x ∘ y) (DCC[τ] x ∘ y')
  -- x and y in x ∘∘ y
  | comp₂₀   : RedAff x x' → RedAff (DCC[τ] x ∘∘ y) (DCC[τ] x' ∘∘ y)
  | comp₂₁   : RedAff y y' → RedAff (DCC[τ] x ∘∘ y) (DCC[τ] x ∘∘ y')
/-
App congruence:
-/
  | congrFun : RedAff f f' → RedAff (DCC[τ] (f x)) (DCC[τ] (f' x))
  | congrArg : RedAff x x' → RedAff (DCC[τ] (f x)) (DCC[τ] (f x'))

@[dcc_force_reduce, dcc_force_aff]
def step?.{u} {τ : Type u} (e : GenericExpr τ) : Option ((e' : GenericExpr τ) × (PULift.{u + 1, 0} (RedAff (τ := τ) e e'))) :=
  match e with
  | (DCC[?] Π(f_α, f_β)) =>
    match f_α.step?, f_β.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.pi₀ h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.pi₁ h₁⟩⟩
    | _, _ => .none
  | (DCC[?] Σ(f_α, f_β)) =>
    match f_α.step?, f_β.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.sigma₀ h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.sigma₁ h₁⟩⟩
    | _, _ => .none
  | (DCC[?] (Eql(_f_α) &(_env) &(_x))) => .some ⟨_, ⟨.eql⟩⟩
  | (DCC[?] (x = y)) =>
    match x.step?, y.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.eq₀ h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.eq₁ h₁⟩⟩
    | _, _ => .none
  | DCC[?] !(x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.bang₀ h⟩⟩
    | _ => .none
  | DCC[?] !<x> =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.map₀ h⟩⟩
    | _ => .none
  | DCC[?] (!<_f> &(_x))                                 => .some ⟨_, ⟨.map⟩⟩
  | DCC[?] ($<_f> &(_x))                                 => .some ⟨_, ⟨.fmap⟩⟩
  | DCC[?] (*<_α> &(_x))                                 => .some ⟨_, ⟨.unmap⟩⟩
  | DCC[?] *<x> =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.unmap₀ h⟩⟩
    | _ => .none
  | DCC[?] $<x> =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.fmap₀ h⟩⟩
    | _ => .none
  | DCC[?] &(x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.box₀ h⟩⟩
    | _ => .none
  | DCC[?] ((⟦_β⟧⟨_M, _N⟩ &(_x)))                        => .some ⟨_, ⟨.pair⟩⟩
  | (DCC[?] (Eval(_α, _β, _x) ⟦__β⟧(_y, _z)))            => .some ⟨_, ⟨.evalc⟩⟩
  | (DCC[?] (`(_β, _x) _y))                              => .some ⟨_, ⟨.quot⟩⟩
  | (DCC[?] (Id(_α) _x))                                 => .some ⟨_, ⟨.id⟩⟩
  | (DCC[?] (Fst(_α) ⟦_γ⟧(_a, _b)))                     => .some ⟨_, ⟨.fstc⟩⟩
  | DCC? Fst(B) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨ .fstc₀ h⟩⟩
    | _ => .none
  | DCC? Snd(B) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨ .sndc₀ h⟩⟩
    | _ => .none
  | DCC? Eql(B) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨ .eql₀ h⟩⟩
    | _ => .none
  | DCC? Id(A) =>
    match A.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨ .id₀ h⟩⟩
    | _ => .none
  | DCC? refl(B) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨ .refl₀ h⟩⟩
    | _ => .none
  | (DCC[?] (Snd(_α) ⟦_γ⟧(_a, _b)))                     => .some ⟨_, ⟨.sndc⟩⟩
  | (DCC[?] ((_x ∘' _y) _z))                             => .some ⟨_, ⟨.comp'⟩⟩
  | DCC? x ∘' y =>
    match x.step?, y.step? with
    | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.comp'₀ h⟩⟩
    | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp'₁ h⟩⟩
    | _, _ => .none
  | (DCC[?] ((_x ∘ _y) _z))                              => .some ⟨_, ⟨.comp⟩⟩
  | DCC? x ∘ y =>
    match x.step?, y.step? with
    | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.comp₀ h⟩⟩
    | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp₁ h⟩⟩
    | _, _ => .none
  | (DCC[?] ((_x ∘∘ _y) _z))                             => .some ⟨_, ⟨.comp₂⟩⟩
  | DCC? x ∘∘ y =>
    match x.step?, y.step? with
    | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.comp₂₀ h⟩⟩
    | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp₂₁ h⟩⟩
    | _, _ => .none
  | (DCC[?] (!Λ(_α, _β, _x) &(_y) &(_z)))                => .some ⟨_, ⟨.curr'⟩⟩
  | DCC[?] !Λ(A, B, x) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.curr'₁ h⟩⟩
    | .none => match A.step?, x.step? with
      | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.curr'₀ h⟩⟩
      | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.curr'₂ h⟩⟩
      | _, _ => .none
  | (DCC[?] (Λ(_α, _β, _x) _y _z)) => .some ⟨_, ⟨.curr⟩⟩
  | DCC[?] Λ(A, B, x) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.curr₁ h⟩⟩
    | .none => match A.step?, x.step? with
      | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.curr₀ h⟩⟩
      | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.curr₂ h⟩⟩
      | _, _ => .none
  | DCC[?] Eval(A, B, x) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.eval₁ h⟩⟩
    | .none => match A.step?, x.step? with
      | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.eval₀ h⟩⟩
      | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.eval₂ h⟩⟩
      | _, _ => .none
  | (DCC[?] (Σ(_f_α, _f_β) _env))                        => .some ⟨_, ⟨.sigma⟩⟩
  | DCC[?] ⟦β⟧(x, y) =>
    match β.step? with
    | .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.sig₀ h₁⟩⟩
    | _ =>
      match x.step?, y.step? with
      | .some ⟨x', ⟨h₁⟩⟩, _ => .some ⟨(DCC[?] ⟦β⟧(x', y)), ⟨.sig₁ h₁⟩⟩
      | _, .some ⟨y', ⟨h₁⟩⟩ => .some ⟨(DCC[?] ⟦β⟧(x, y')), ⟨.sig₂ h₁⟩⟩
      | _, _ => .none
  | DCC[?] ⟦B⟧⟨x, y⟩ =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pair₀ h⟩⟩
    | _ =>
      match x.step?, y.step? with
      | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.pair₁ h⟩⟩
      | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pair₂ h⟩⟩
      | _, _ => .none
  | (DCC[?] (Coup(β))) =>
    match β.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.coup₀ h⟩⟩
    | _ => .none
  | DCC? `(B, x) =>
    match B.step?, x.step? with
    | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.quot₀ h⟩⟩
    | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.quot₁ h⟩⟩
    | _, _ => .none
  | DCC[?] (f x) =>
    match f.step?, x.step? with
    | .some ⟨f', ⟨h₁⟩⟩, _ => .some ⟨(DCC[?] (f' x)), ⟨.congrFun h₁⟩⟩
    | _, .some ⟨x', ⟨h₁⟩⟩ => .some ⟨(DCC[?] (f x')), ⟨.congrArg h₁⟩⟩
    | _, _ => .none
  | _ => .none

@[dcc_force_reduce, dcc_force_aff]
instance RedAff.instRedRel.{u} {τ : Type u} : RedRel (α := GenericExpr τ) (RedAff (τ := τ)) size where
  run := step?

theorem red_aff_sn.{u} {τ : Type u} : ∀ (e : GenericExpr τ), Acc (fun b a => RedAff (τ := τ) a b) e :=
  RedAff.instRedRel.sn

theorem red_aff_trans_sn.{u} {τ : Type u} [DecidableEq τ] : ∀ (e : GenericExpr τ), Acc (fun b a => Relation.TransGen RedAff a b) e :=
  RedAff.instRedRel.to_trans.sn

theorem RedAff.mkCongrFun (h : RedAff f f') : RedAff (DCC? (f x)) (DCC? (f' x)) := .congrFun h
theorem RedAff.mkCongArg (h : RedAff x x') : RedAff (DCC? (f x)) (DCC? (f x')) := .congrArg h

theorem congrFun' (hr : Relation.ReflTransGen RedAff f f') : Relation.ReflTransGen RedAff (DCC? (f x)) (DCC? (f' x)) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := RedAff.instRedRel.decreasing h₁
    exact .trans (.single (.congrFun h₁)) (congrFun' h₂)
termination_by size f

theorem congrArg' (hr : Relation.ReflTransGen RedAff x x') : Relation.ReflTransGen RedAff (DCC? (f x)) (DCC? (f x')) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := RedAff.instRedRel.decreasing h₁
    exact .trans (.single (.congrArg h₁)) (congrArg' h₂)
termination_by size x

@[aesop safe forward (rule_sets := [DccForceReduce])]
theorem RedAff.elim_point₁ {A B : GenericExpr τ_c} (hr : RedAff A B) (h_arr : point_arity A = 1 := by rfl) : ∃ p', B = (A.set_points (A.points.set 0 p')) ∧ RedAff A.points[0] p' := by
  unfold point_arity at h_arr
  split at h_arr <;> (
    first
    | (grind)
    | (
      simp at h_arr
      dcc_simp
      cases hr
      grind))

theorem RedAff.mk_point {x y e : GenericExpr τ_c} {n : Fin (point_arity e)} (hr : RedAff x y := by assumption) (heq : (points e)[n] = x := by dcc_simp; rfl) : RedAff e (e.set_points ((points e).set n y)) := by
  unfold points at heq
  split at heq <;> (
    first
    | (grind)
    | (dcc_simp at n
       fin_cases n <;> (
       dcc_simp at *
       cases heq
       constructor
       assumption)))

theorem RedAff.elim_points {A B : GenericExpr τ_c} (hr : RedAff A B) (h_arr : 0 < point_arity A := by grind) : ∃ (p' : GenericExpr τ_c) (n : Fin (point_arity A)), B = (A.set_points (A.points.set n p')) ∧ RedAff A.points[n] p' := by
  unfold point_arity at h_arr
  split at h_arr
  any_goals (grind)
  any_goals (
    focus
    try (
      have ⟨p', heq, hr⟩ := hr.elim_point₁
      exact ⟨p', ⟨0, by grind⟩, heq, hr⟩)
    done)
  any_goals (
    focus
    try (
      cases hr
      · rename_i hr; exact ⟨_, ⟨0, by grind⟩, rfl, by assumption⟩
      · rename_i hr; exact ⟨_, ⟨1, by grind⟩, rfl, by assumption⟩)
    done)
  any_goals (
    focus
    try (
      cases hr
      · rename_i hr; exact ⟨_, ⟨0, by grind⟩, rfl, by assumption⟩
      · rename_i hr; exact ⟨_, ⟨1, by grind⟩, rfl, by assumption⟩
      · rename_i hr; exact ⟨_, ⟨2, by grind⟩, rfl, by assumption⟩))

theorem RedAff.instCongruent'_mp {e : GenericExpr τ_c} {p : Fin (point_arity e)} (h : RedAff (points e)[p] p') : RedAff e (set_points e ((points e).set p p')) := by
  simp [points] at h
  split at h <;> (simp [point_arity] at p; simp at h)
  any_goals (grind)
  any_goals (fin_cases p <;> (
      try (simp at h)
      dcc_simp
      constructor; assumption))

theorem RedAff.instCongruent'_mpr {e : GenericExpr τ_c} {p : Fin (point_arity e)} (h : RedAff e (set_points e ((points e).set p p'))) : RedAff (points e)[p] p' := by
  simp [points] at h
  split at h <;> (simp [point_arity] at p; simp at h)
  any_goals (grind)
  any_goals (
    focus
    try (
      fin_cases p
      any_goals (
        dcc_simp at h
        cases h
        any_goals (assumption)
        try (any_goals (
          focus
          try (
            have h_dec := RedAff.instRedRel.decreasing (by assumption)
            grind))))))

theorem red_aff_congr_point {e : GenericExpr τ_c} {p : Fin (point_arity e)} (h : Relation.ReflTransGen RedAff (points e)[p] p') : Relation.ReflTransGen RedAff e (set_points e ((points e).set p p')) := by
  match h.cases_head with
  | .inl h =>
    cases h
    simp [set_points_self_noop]
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec₁ := RedAff.instRedRel.decreasing h₁
    have ha := RedAff.instCongruent'_mp h₁
    have h_dec₂ := RedAff.instRedRel.decreasing ha
    have hb := RedAff.instCongruent'_mpr ha
    rename_i w
    have heq := congr_point_arr (e := e) (p := p) (p' := w)
    have heq' : (points (e.set_points (e.points.set (↑ p) w))).get ⟨p, by rw [← congr_point_arr]; grind⟩ = w := by
      grind
    change (points _)[p] = w at heq'
    rw [← heq'] at h₂
    --exact .trans (.single ha) (by sorry)
    have h := red_aff_congr_point (e := (e.set_points
          (e.points.set p w)))
          (p' := p')
          (p := ⟨↑p,
        Eq.mpr (_root_.id (_root_.congrArg (fun _a => ↑p < _a) (Eq.symm congr_point_arr)))
          red_aff_congr_point._proof_1_4⟩) h₂
    simp at h
    expose_names
    exact .trans (.single ha) (by
      simp_all
      grind)
termination_by size e

instance RedAff.instCongruent'.{u} {τ : Type u} : Congruent' (RedAff (τ := τ)) where
  congr_iff := ⟨RedAff.instCongruent'_mp, RedAff.instCongruent'_mpr⟩

instance RedAff.instCongruent.{u} {τ : Type u} : Congruent (RedAff (τ := τ)) where

theorem aff_mk_point' {x y e : GenericExpr τ_c} (hr : Relation.ReflTransGen RedAff x y) (hn : n < point_arity e := by grind) (heq : (points e)[(Fin.mk n hn)] = x := by first | rfl | grind | (dcc_simp; rfl)) : Relation.ReflTransGen RedAff e (e.set_points ((points e).set n y)) := by
  cases heq
  exact red_aff_congr_point hr

theorem aff_mk_point'' {x y e : GenericExpr τ_c} (n : ℕ) (hr : RedAff x y := by assumption) (hn : n < point_arity e := by grind) (heq : (points e)[(Fin.mk n hn)] = x := by first | rfl | grind | (dcc_simp; rfl)) : Relation.ReflTransGen RedAff e (e.set_points ((points e).set n y)) := aff_mk_point' (.single hr)

@[grind ., grind →, grind! →]
theorem mk_inner_norm (h_points : 0 < point_arity e)
  (hrn : List.Forall (IsNorm RedAff) (points e).toList) : IsNorm RedAff e := by
  unfold point_arity at h_points
  split at h_points <;> (
    first
    | (grind)
    | (
    intro ⟨_, h⟩
    simp [points, Vector.toList] at hrn
    cases h <;> grind))

theorem elim_inner_norm (hrn : IsNorm RedAff e) : List.Forall (IsNorm RedAff)
  (points e).toList := by
  unfold points
  split
  any_goals (simp)
  case h_4 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · intro ⟨_, h⟩
      exact hrn ⟨_, .eq₁ (by assumption)⟩
  any_goals (
    intro ⟨_, h⟩
    exact hrn ⟨_, by constructor; assumption⟩)
  case h_8 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · intro ⟨_, h⟩
      exact hrn ⟨_, .sigma₁ (by assumption)⟩
  case h_9 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · intro ⟨_, h⟩
      exact hrn ⟨_, .quot₁ (by assumption)⟩
  case h_10 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · constructor
      · intro ⟨_, h⟩
        exact hrn ⟨_, .sig₁ (by assumption)⟩
      · intro ⟨_, h⟩
        exact hrn ⟨_, .sig₂ (by assumption)⟩
  case h_15 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · intro ⟨_, h⟩
      exact hrn ⟨_, .pi₁ (by assumption)⟩
  case h_16 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · intro ⟨_, h⟩
      exact hrn ⟨_, .comp'₁ (by assumption)⟩
  case h_17 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · intro ⟨_, h⟩
      exact hrn ⟨_, .comp₁ (by assumption)⟩
  case h_18 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · intro ⟨_, h⟩
      exact hrn ⟨_, .comp₂₁ (by assumption)⟩
  case h_19 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · constructor
      · intro ⟨_, h⟩
        exact hrn ⟨_, .pair₁ (by assumption)⟩
      · intro ⟨_, h⟩
        exact hrn ⟨_, .pair₂ (by assumption)⟩
  case h_20 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · constructor
      · intro ⟨_, h⟩
        exact hrn ⟨_, .curr₁ (by assumption)⟩
      · intro ⟨_, h⟩
        exact hrn ⟨_, .curr₂ (by assumption)⟩
  case h_21 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · constructor
      · intro ⟨_, h⟩
        exact hrn ⟨_, .curr'₁ (by assumption)⟩
      · intro ⟨_, h⟩
        exact hrn ⟨_, .curr'₂ (by assumption)⟩
  case h_22 =>
    constructor
    · intro ⟨_, h⟩
      exact hrn ⟨_, by constructor; assumption⟩
    · constructor
      · intro ⟨_, h⟩
        exact hrn ⟨_, .eval₁ (by assumption)⟩
      · intro ⟨_, h⟩
        exact hrn ⟨_, .eval₂ (by assumption)⟩

@[aesop safe apply (rule_sets := [DccForceReduce])]
theorem refl_conf : ∃ B, Relation.ReflTransGen r A B ∧ Relation.ReflTransGen r A B := ⟨_, .refl, .refl⟩

@[aesop safe apply (rule_sets := [DccReduce])]
theorem congrFun_of_single (h : RedAff x x' := by assumption) : Relation.ReflTransGen RedAff (DCC? (x y)) (DCC? (x' y)) := .single (.congrFun h)

@[aesop safe apply (rule_sets := [DccReduce])]
theorem congrArg_of_single (h : RedAff y y' := by assumption) : Relation.ReflTransGen RedAff (DCC? (x y)) (DCC? (x y')) := .single (.congrArg h)

attribute [aesop safe (rule_sets := [DccForceReduce]) [constructors]] Relation.ReflTransGen

set_option maxHeartbeats 10000000000 in
open Congruent' in
open Congruent in @[dcc_reduce, aesop safe apply (rule_sets := [DccReduce])]
theorem RedAff.conf.{u} {α : Type u} {A B C : GenericExpr α} (h₁ : (RedAff (τ := α)) A B) (h₂ : RedAff A C) : ∃ D, RedAff.instRedRel.ReflTrans B D ∧ RedAff.instRedRel.ReflTrans C D := by
  induction h₁ generalizing C
  -- Main reductions:
  case eql =>
    cases h₂ with
    | congrFun hr =>
      cases hr with
      | congrFun hr =>
        have ⟨_, h⟩ := hr.elim_point₁
        dcc_simp at h
        cases h.left
        exact ⟨_, .refl, .single (by constructor)⟩
      | congrArg hr =>
        have ⟨_, h⟩ := hr.elim_point₁
        dcc_simp at h
        cases h.left
        exact ⟨_, .refl, .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .trans (.single (h.right.mk_point (n := ⟨0, by grind⟩)))
        (.single (h.right.mk_point (n := ⟨1, by grind⟩))), .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case fmap | map =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .single ((RedAff.congrFun h.right).mk_point (n := ⟨0, by grind⟩)), .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .single ((RedAff.congrArg h.right).mk_point (n := ⟨0, by grind⟩)), .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case unmap =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .single (RedAff.congrFun h.right), .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .single (RedAff.congrArg h.right), .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case pair =>
    cases h₂ with
    | congrFun hr =>
      cases hr with
      | pair₀ hr =>
        exact ⟨_, .single (hr.congrFun.mk_point (n := ⟨0, by grind⟩)), .single (by constructor)⟩
      | pair₁ hr =>
        exact ⟨_, .trans (.single (hr.congrFun.mk_point (n := ⟨1, by grind⟩))) (.single (hr.congrFun.congrArg.mk_point (n := ⟨2, by grind⟩))), .single (by constructor)⟩
      | pair₂ hr =>
        exact ⟨_, .single (hr.congrFun.congrFun.mk_point (n := ⟨2, by grind⟩)), .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      dcc_simp at h
      cases h.left
      exact ⟨_, .trans (.trans (.trans (.single (h.right.congrArg.mk_point (n := ⟨0, by grind⟩)))
        (.single (h.right.congrArg.mk_point (n := ⟨1, by grind⟩))))
        (.single (h.right.congrArg.congrArg.mk_point (n := ⟨2, by grind⟩))))
        (.single (h.right.congrArg.congrFun.mk_point (n := ⟨2, by grind⟩))), .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case evalc =>
    cases h₂ with
    | congrFun hr =>
      cases hr
      case eval₂ hr =>
        exact ⟨_, .single hr.congrFun.congrFun, .single .evalc⟩
      case _ hr | _ hr => exact ⟨_, .refl, .single .evalc⟩
    | congrArg hr =>
      cases hr
      case _ => exact ⟨_, .refl, .single .evalc⟩
      case _ hr => exact ⟨_, .single hr.congrArg.congrFun, .single .evalc⟩
      case _ hr => exact ⟨_, .single hr.congrArg, .single .evalc⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case quot =>
    cases h₂ with
    | congrFun h =>
      cases h
      case _ => exact ⟨_, .refl, .single (by constructor)⟩
      case _ hr => exact ⟨_, .single hr, .single (by constructor)⟩
    | congrArg h => exact ⟨_, .refl, .single (by constructor)⟩
    | _ => dcc_aesop' [force_reduce, force_step]
  case id =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      cases h.left
      exact ⟨_, .refl, .single (by constructor)⟩
    | congrArg hr => exact ⟨_, .single hr, .single (by constructor)⟩
    | _ => exact ⟨_, .refl, .refl⟩
  case fstc | sndc =>
    cases h₂ with
    | congrFun hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      cases h.left
      exact ⟨_, .refl, .single (by constructor)⟩
    | congrArg hr =>
      cases hr <;> (
        first
        | exact ⟨_, .refl, .single (by constructor)⟩
        | exact ⟨_, .single (by assumption), .single (by constructor)⟩)
    | _ => exact ⟨_, .refl, .refl⟩
  case comp' | comp | comp₂ =>
    cases h₂ with
    | congrFun hr =>
      cases hr
      case _ hr => exact ⟨_, .single hr.congrFun, .single (by constructor)⟩
      case _ hr => exact ⟨_, .single hr.congrFun.congrArg, .single (by constructor)⟩
    | congrArg hr =>
      exact ⟨_, .single hr.congrArg.congrArg, .single (by constructor)⟩
    | _ => exact ⟨_, .refl, .refl⟩
  case curr =>
    cases h₂ with
    | congrFun hr =>
      cases hr with
      | congrFun hr =>
        cases hr
        · exact ⟨_, .refl, .single (by constructor)⟩
        case _ hr => exact ⟨_, .single hr.sig₀.congrArg, .single (by constructor)⟩
        case _ hr => exact ⟨_, .single hr.congrFun, .single (by constructor)⟩
      | congrArg hr =>
        exact ⟨_, .single hr.sig₁.congrArg, .single (by constructor)⟩
    | congrArg hr =>
      exact ⟨_, .single hr.sig₂.congrArg, .single (by constructor)⟩
    | _ => exact ⟨_, .refl, .refl⟩
  case curr' =>
    cases h₂ with
    | congrFun hr =>
      cases hr with
      | congrFun hr =>
        cases hr
        · exact ⟨_, .refl, .single (by constructor)⟩
        case _ hr => exact ⟨_, .single hr.sig₀.box₀.congrArg, .single (by constructor)⟩
        case _ hr => exact ⟨_, .single hr.congrFun, .single (by constructor)⟩
      | congrArg hr =>
        have ⟨_, h⟩ := hr.elim_point₁
        cases h.left
        exact ⟨_, .single h.right.sig₁.box₀.congrArg, .single (by constructor)⟩
    | congrArg hr =>
      have ⟨_, h⟩ := hr.elim_point₁
      cases h.left
      exact ⟨_, .single h.right.sig₂.box₀.congrArg, .single (by constructor)⟩
    | _ => exact ⟨_, .refl, .refl⟩
  case sigma =>
    cases h₂ with
    | congrFun hr =>
      cases hr
      · exact ⟨_, .refl, .single (by constructor)⟩
      case _ hr => exact ⟨_, .single hr.congrFun.coup₀, .single (by constructor)⟩
    | congrArg hr =>
      case _ hr => exact ⟨_, .single hr.congrArg.coup₀, .single (by constructor)⟩
    | _ => exact ⟨_, .refl, .refl⟩
  -- Inner congruences:
  case quot₀ hr ih | quot₁ hr ih | sigma₀ hr ih | sigma₁ hr ih | pi₀ hr ih | pi₁ hr ih
    | eq₀ hr ih | eq₁ hr ih | eql₀ hr ih | refl₀ hr ih | fstc₀ hr ih | sndc₀ hr ih | id₀ hr ih | bang₀ hr ih
    | box₀ hr ih | map₀ hr ih | fmap₀ hr ih | unmap₀ hr ih | coup₀ hr ih | comp₀ hr ih | comp₁ hr ih =>
    cases h₂ <;> (
      first
      | (rename_i hr₂
         have ⟨_, h₁, h₂⟩ := ih hr₂
         exact ⟨_, aff_mk_point' h₁ (n := 0), aff_mk_point' h₂ (n := 0)⟩)
      | (rename_i hr₂
         exact ⟨_, .single (mk_point (n := ⟨1, by grind⟩)), .single (mk_point (n := ⟨0, by grind⟩))⟩)
      | (rename_i hr₂
         have ⟨_, h₁, h₂⟩ := ih hr₂
         exact ⟨_, aff_mk_point' h₁ (n := 1), aff_mk_point' h₂ (n := 1)⟩)
      | (rename_i hr₂
         exact ⟨_, .single (mk_point (n := ⟨0, by grind⟩)), .single (mk_point (n := ⟨1, by grind⟩))⟩))
  case curr₀ hr ih | curr₁ hr ih | eval₀ hr ih | curr'₀ hr ih | pair₀ hr ih | sig₀ hr ih
    | comp₂₁ hr ih | comp'₁ hr ih | pair₁ hr ih | sig₁ hr ih | curr'₁ hr ih | eval₁ hr ih
    | comp₂₀ hr ih | comp'₀ hr ih =>
    cases h₂ <;> (
      first
      | (rename_i hr₂
         have ⟨_, h₁, h₂⟩ := ih hr₂
         exact ⟨_, aff_mk_point' h₁ (n := 0), aff_mk_point' h₂ (n := 0)⟩)
      | (rename_i hr₂
         exact ⟨_, .single (mk_point (n := ⟨1, by grind⟩)), .single (mk_point (n := ⟨0, by grind⟩))⟩)
      | (rename_i hr₂
         have ⟨_, h₁, h₂⟩ := ih hr₂
         exact ⟨_, aff_mk_point' h₁ (n := 1), aff_mk_point' h₂ (n := 1)⟩)
      | (rename_i hr₂
         exact ⟨_, .single (mk_point (n := ⟨0, by grind⟩)), .single (mk_point (n := ⟨1, by grind⟩))⟩)
      | (rename_i hr₂
         exact ⟨_, .single (mk_point (n := ⟨2, by grind⟩)), .single (mk_point (n := ⟨0, by grind⟩))⟩)
      | (rename_i hr₂
         exact ⟨_, .single (mk_point (n := ⟨2, by grind⟩)), .single (mk_point (n := ⟨1, by grind⟩))⟩))
  case pair₂ hr ih | sig₂ hr ih | curr₂ hr ih | eval₂ hr ih | curr'₂ hr ih =>
    cases h₂
    · exact ⟨_, aff_mk_point' (.single (by assumption)) (n := 0), aff_mk_point' (.single (by assumption)) (n := 2)⟩
    · exact ⟨_, aff_mk_point' (.single (by assumption)) (n := 1), aff_mk_point' (.single (by assumption)) (n := 2)⟩
    · rename_i hr₂
      have ⟨_, h₁, h₂⟩ := ih hr₂
      exact ⟨_, aff_mk_point' h₁ (n := 2), aff_mk_point' h₂ (n := 2)⟩
  case congrArg hr ih =>
    rename_i x x' f
    cases h₂
    <;> (try (
      have ⟨p', heq, hrp⟩ := hr.elim_point₁
      dcc_simp at heq; dcc_simp at hrp
      cases heq))
    case eql =>
      exact ⟨_, .single (by constructor), .trans (aff_mk_point'' 0) (aff_mk_point'' 1)⟩
    case fmap | map =>
      exact ⟨_, .single (by constructor), aff_mk_point'' 0 hrp.congrArg⟩
    case unmap =>
      exact ⟨_, .single (by constructor), .single hrp.congrArg⟩
    case pair =>
      exact ⟨_, .single (by constructor), .trans (.trans (aff_mk_point'' 0 hrp.congrArg) (aff_mk_point'' 1 hrp.congrArg))
        ((aff_mk_point'' 2 hrp.congrArg.congrArg).trans (aff_mk_point'' 2 hrp.congrArg.congrFun))⟩
    case evalc =>
      cases hr with
      | sig₀ hr => exact ⟨_, .single (by constructor), .refl⟩
      | sig₁ hr => exact ⟨_, .single (by constructor), .single hr.congrArg.congrFun⟩
      | sig₂ hr => exact ⟨_, .single (by constructor), .single hr.congrArg⟩
    case quot => exact ⟨_, .single (by constructor), .refl⟩
    case id => exact ⟨_, .single (by constructor), .single (by assumption)⟩
    case sndc | fstc =>
      cases hr
      <;> (first
           | exact ⟨_, .single (by constructor), .refl⟩
           | exact ⟨_, .single (by constructor), .single (by assumption)⟩)
    case comp' | comp | comp₂ =>
      exact ⟨_, .single (by constructor), .single hr.congrArg.congrArg⟩
    case curr => exact ⟨_, .single (by constructor), .single (.congrArg (.sig₂ (by assumption)))⟩
    case curr' hr => exact ⟨_, .single (by constructor), .single (.congrArg (.box₀ (.sig₂ (by assumption))))⟩
    case sigma => exact ⟨_, .single (by constructor), .single (.coup₀ hr.congrArg)⟩
    case congrFun hr => exact ⟨_, .single (.congrFun hr), .single (.congrArg (by assumption))⟩
    case congrArg hr =>
      have ⟨_, h₁, h₂⟩ := ih hr
      exact ⟨_, congrArg' h₁, congrArg' h₂⟩
  case congrFun hr ih =>
    rename_i f f' x
    cases h₂
    <;> (try (
      have ⟨p', heq, hrp⟩ := hr.elim_point₁
      dcc_simp at heq; dcc_simp at hrp
      cases heq))
    case eql =>
      cases hr
      <;> (
        rename_i hr
        have ⟨p', heq, hrp⟩ := hr.elim_point₁
        dcc_simp at heq; dcc_simp at hrp
        cases heq
        exact ⟨_, .single (by constructor), .refl⟩)
    case map | fmap =>
      exact ⟨_, .single (by constructor), aff_mk_point'' 0 hrp.congrFun⟩
    case unmap =>
      exact ⟨_, .single (by constructor), .single hrp.congrFun⟩
    case pair =>
      cases hr
      · rename_i hr; exact ⟨_, .single (by constructor), aff_mk_point'' 0 hr.congrFun⟩
      · rename_i hr; exact ⟨_, .single (by constructor), .trans (aff_mk_point'' 1 hr.congrFun) (aff_mk_point'' 2 hr.congrFun.congrArg)⟩
      · rename_i hr; exact ⟨_, .single (by constructor), aff_mk_point'' 2 hr.congrFun.congrFun⟩
    case evalc =>
      cases hr
      case eval₂ hr =>
        exact ⟨_, .single (by constructor), .single hr.congrFun.congrFun⟩
      case _ | _ => exact ⟨_, .single (by constructor), .refl⟩
    case quot =>
      cases hr
      · exact ⟨_, .single (by constructor), .refl⟩
      · exact ⟨_, .single (by constructor), .single (by assumption)⟩
    case id | fstc | sndc =>
      cases hr
      · exact ⟨_, .single (by constructor), .refl⟩
    case comp | comp₂ | comp' =>
      cases hr
      · rename_i hr; exact ⟨_, .single (by constructor), .single hr.congrFun⟩
      · rename_i hr; exact ⟨_, .single (by constructor), .single hr.congrFun.congrArg⟩
    case curr =>
      cases hr with
      | congrFun hr =>
        cases hr
        · rename_i hr; exact ⟨_, .single (by constructor), .refl⟩
        · rename_i hr; exact ⟨_, .single (by constructor), (congrArg' (aff_mk_point'' 0))⟩
        · rename_i hr; exact ⟨_, .single (by constructor), .single (.congrFun (by assumption))⟩
      | congrArg hr => exact ⟨_, .single (by constructor), (congrArg' (aff_mk_point'' 1))⟩
    case curr' =>
      cases hr with
      | congrFun hr =>
        cases hr
        · rename_i hr; exact ⟨_, .single (by constructor), .refl⟩
        · rename_i hr; exact ⟨_, .single (by constructor), .single (.congrArg (.box₀ (.sig₀ (by assumption))))⟩
        · rename_i hr; exact ⟨_, .single (by constructor), .single (.congrFun (by assumption))⟩
      | congrArg hr =>
        have ⟨p', heq, hrp⟩ := hr.elim_point₁
        dcc_simp at heq; dcc_simp at hrp
        cases heq
        exact ⟨_, .single (by constructor), .single (.congrArg (.box₀ (.sig₁ (by assumption))))⟩
    case sigma =>
      cases hr with
      | sigma₀ hr => exact ⟨_, .single (by constructor), .refl⟩
      | sigma₁ hr => exact ⟨_, .single (by constructor), .single (.coup₀ hr.congrFun)⟩
    case congrFun hr₂ =>
      have ⟨_, ha, hb⟩ := ih hr₂
      exact ⟨_, congrFun' ha, congrFun' hb⟩
    case congrArg hr => exact ⟨_, .single (.congrArg (by assumption)), .single (.congrFun (by assumption))⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance RedAff.instConf.{u} {τ : Type u} : Confluent (RedAff (τ := τ)) := ⟨RedAff.conf⟩

theorem red_aff_globally_conf.{u} {τ : Type u} {A B C : GenericExpr τ} : Relation.ReflTransGen (RedAff (τ := τ)) A B → Relation.ReflTransGen RedAff A C → ∃ D,
  Relation.ReflTransGen RedAff B D ∧ Relation.ReflTransGen RedAff C D :=
  RedAff.instRedRel.globally_confluent.conf

#check Relation.ReflTransGen.head_induction_on

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance instConfRedAffTrans.{u} {τ : Type u} : Confluent (RedAff (τ := τ)) (m := Relation.ReflTransGen) := RedAff.instRedRel.globally_confluent

set_option maxHeartbeats 10000000000 in
def semi_complete.{u} {τ : Type u} {A B : GenericExpr τ} (hr : A.RedAff B) : ∃ B', ∃ (h : A.RedAff B'), (step? A) = .some ⟨B', ⟨h⟩⟩ := by
  change ∃ _, ∃ _, (step? _) = .some _
  unfold step?
  split
  any_goals (
    focus
    try (
      split
      case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨0, by grind⟩), rfl⟩
      case h_2 hr' heq _ => exact ⟨_, hr'.mk_point (n := ⟨1, by grind⟩), rfl⟩
      case h_3 hn₁ hn₂ =>
        cases hr <;> (
          rename_i hr
          have ⟨_, hr'', heq⟩ := semi_complete hr
          grind))
    done)
  any_goals (exact ⟨_, by constructor, rfl⟩)
  any_goals (
    focus
    try (
      split
      case h_1 hr' heq =>
        exact ⟨_, hr'.mk_point (n := ⟨0, by grind⟩), rfl⟩
      case h_2 hn₁ hn₂ =>
        cases hr <;> (
          rename_i hr
          have ⟨_, hr'', heq⟩ := semi_complete hr
          grind))
    done)
  any_goals (
    focus
    try (
      split
      case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨1, by grind⟩), rfl⟩
      · split
        case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨0, by grind⟩), rfl⟩
        case h_2 hr' heq _ => exact ⟨_, hr'.mk_point (n := ⟨2, by grind⟩), rfl⟩
        case h_3 hn₁ hn₂ =>
          cases hr <;> (
            rename_i hr
            have ⟨_, hr'', heq⟩ := semi_complete hr
            grind))
    done)
  any_goals (
    focus
    try (
      split
      case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨0, by grind⟩), rfl⟩
      · split
        case h_1 hr' heq => exact ⟨_, hr'.mk_point (n := ⟨1, by grind⟩), rfl⟩
        case h_2 hr' heq _ => exact ⟨_, hr'.mk_point (n := ⟨2, by grind⟩), rfl⟩
        case h_3 hn₁ hn₂ =>
          cases hr <;> (
            rename_i hr
            have ⟨_, hr'', heq⟩ := semi_complete hr
            grind))
    done)
  case h_40 =>
    cases hr
    <;> simp_all
    any_goals (grind)
    case congrFun hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      simp [heq]
      exact hr'.congrFun
    case congrArg hr =>
      have ⟨_, hr', heq⟩ := semi_complete hr
      simp [heq]
      split
      · exact ⟨_, .congrFun (by assumption), rfl⟩
      · exact ⟨_, .congrArg (by assumption), rfl⟩
      · grind
  case h_41 =>
    simp_all
    cases hr
    any_goals (grind)

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance RedAff.instSemicomplete.{u} {τ : Type u} : SemiComplete (RedAff (τ := τ)) := ⟨semi_complete⟩

theorem aff_complete (h : Relation.ReflTransGen RedAff A B)
  (hn : IsNorm RedAff B) : reduce RedAff A = ⟨B, ⟨h⟩⟩ :=
  RedAff.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance instComplete.{u} {τ : Type u} : Complete (Relation.ReflTransGen (RedAff (τ := τ))) (P := IsNorm RedAff) := RedAff.instRedRel.instComplete

-- RedRel.reduce Size RedAff.instRedRel : (e : Expr) → (e' : Expr) × PULift (Relation.ReflTransGen RedAff e e')
#check reduce RedAff

/-
Complete.complete
  Id : ∀ (h : Relation.ReflTransGen RedAff ?m.8 ?m.9), IsNorm RedAff ?m.9 → Rel.run Id ?m.8 = pure ⟨?m.9, { down := h }⟩
-/
#check instComplete.complete

theorem RedAff.decreasing' (h : RedAff A B) : size B < size A := by
  induction h <;> grind

@[grind ., grind →]
theorem red_aff_decreasing?.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] (h : Relation.ReflTransGen (RedAff (τ := τ)) A B) : (size B) ≤ (size A) := by
  if hs : (size A) = (size B) then
    simp_all
  else
    rw [← Relation.reflGen_transGen] at h
    match h with
    | .refl => grind
    | .single h =>
      have hn' : B.size < A.size := RedAff.instRedRel.to_trans.decreasing h
      grind

@[grind ., grind →]
theorem red_aff_trans_decreasing.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] : Relation.TransGen (RedAff (τ := τ)) A B → (size B) < (size A) :=
  RedAff.instRedRel.to_trans.decreasing

@[dcc_force_reduce, dcc_force_aff]
abbrev RedAff.reduce.{u} {τ : Type u} := GenericExpr.reduce (RedAff (τ := τ))

attribute [dcc_force_reduce, dcc_force_aff] RedAff.reduce.eq_def

instance RedAff.instDecidableNorm.{u} {α : Type u} [DecidableEq α]
{A : GenericExpr α}  : Decidable (IsNorm (RedAff (τ := α)) A) :=
  match heq₀ : GenericExpr.reduce RedAff A with
  | ⟨A', ⟨h⟩⟩ =>
    if heq : A' = A then
      have h_norm := reduce_norm (h := heq ▸ h) (A := A) (B := A) (hR := RedAff.instRedRel) (heq ▸ heq₀)
      .isTrue (fun ⟨a, b⟩ => by
        exact h_norm ⟨_, b⟩)
    else
      .isFalse (fun h => by
        have h := RedAff.instRedRel.reduce_norm_fst h
        simp_all)

@[dcc_judge]
def RedAffReflTrans.{u} {τ : Type u} := Relation.ReflTransGen (RedAff (τ := τ))

theorem RedAffReflTrans.reflGen_transGen.{u} {τ : Type u} : Relation.ReflGen (Relation.TransGen RedAff) = RedAffReflTrans (τ := τ) :=
  Relation.reflGen_transGen

@[dcc_judge]
def RedAffTrans.{u} {τ : Type u} := Relation.TransGen (RedAff (τ := τ))

namespace RedAffTrans

def single (r : RedAff A B) : RedAffTrans A B := Relation.TransGen.single r

def trans (r₁ : RedAffTrans A B) (r₂ : RedAffTrans B C) : RedAffTrans A C := Relation.TransGen.trans r₁ r₂

def to_reflTrans {a b : Expr} (r : RedAffTrans a b) : RedAffReflTrans a b :=
  Relation.TransGen.to_reflTransGen (a := a) (b := b) r

end RedAffTrans

namespace RedAffReflTrans

def cases_head.{u} {τ_c : Type u} {a b : GenericExpr τ_c} (r : RedAffReflTrans a b) :=
  Relation.ReflTransGen.cases_head (a := a) (b := b) r

def single.{u} {τ : Type u} {A B : GenericExpr τ}
  (r : RedAff A B) : (RedAffReflTrans (τ := τ)) A B := Relation.ReflTransGen.single r

def trans.{u} {τ : Type u} {A B C : GenericExpr τ} (r₁ : RedAffReflTrans A B)
  (r₂ : RedAffReflTrans B C) : RedAffReflTrans A C := Relation.ReflTransGen.trans r₁ r₂

def conf.{u} {τ : Type u} {A B C : GenericExpr τ} (h₁ : RedAffReflTrans A B) (h₂ : RedAffReflTrans A C) : ∃ D, RedAffReflTrans B D ∧ RedAffReflTrans C D := RedAff.instRedRel.globally_confluent.conf h₁ h₂

def elim_head_norm.{u} {τ : Type u} {A B : GenericExpr τ} (h : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B :=
  hn.unique_refl h

@[grind ., grind →]
theorem red_aff_decreasing?.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] (h : (RedAffReflTrans (τ := τ)) A B) : (size B) ≤ (size A) := by
  if hs : (size A) = (size B) then
    simp_all
  else
    rw [← reflGen_transGen] at h
    match h with
    | .refl => grind
    | .single h =>
      have hn' : B.size < A.size := RedAff.instRedRel.to_trans.decreasing h
      grind

def elim_norm (hr : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B := by
  change Relation.ReflTransGen _ _ _ at hr
  exact hn.unique_refl hr

@[grind ., grind <=]
theorem elim_norm' (hr : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B := by
  change Relation.ReflTransGen _ _ _ at hr
  exact hn.unique_refl hr

def push_head (hr₁ : RedAffReflTrans A C) (hn : IsNorm RedAff C) (hr₂ : RedAff A B) : RedAffReflTrans B C :=
  have ⟨_, h₁, h₂⟩ := RedAff.instRedRel.globally_confluent.conf hr₁ (.single hr₂)
  hn.unique_refl h₁ ▸ h₂

end RedAffReflTrans

namespace RedAffTrans

@[grind ., grind →]
theorem red_aff_trans_decreasing.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] : (RedAffTrans (τ := τ)) A B → (size B) < (size A) := by
  change Relation.TransGen _ _ _ → _
  exact (RedAff.instRedRel (τ := τ)).to_trans.decreasing

end RedAffTrans

namespace RedAff

abbrev decreasing.{u} {τ_c : Type u} (x y : GenericExpr τ_c) := (RedAff.instRedRel (τ := τ_c)).decreasing (x := x) (y := y)

end RedAff

namespace RedAffReflTrans

def push_head' (hr₁ : RedAffReflTrans A C) (hn : IsNorm RedAff C) (hr₂ : RedAffReflTrans A B) : RedAffReflTrans B C := by
  have ⟨_, h₁, h₂⟩ := hr₁.conf hr₂
  have heq := hn.unique_refl h₁
  exact heq ▸ h₂

@[grind ., grind →]
theorem decreasing?.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] (h : (RedAffReflTrans (τ := τ)) A B) : (size B) ≤ (size A) := red_aff_decreasing? h

end RedAffReflTrans

inductive RedAffNorm : GenericExpr τ_c → NormExpr (RedAff (τ := τ_c)) → Type u
  | mk : (hr : RedAffReflTrans A B) → (hn : IsNorm RedAff B) → RedAffNorm A ⟨B, hn⟩
deriving DecidableEq

@[dcc_step]
def RedAffNorm.decreasing? (h : RedAffNorm A B) : B.size ≤ A.size :=
  match h with
  | ⟨hr, _hn⟩ => GenericExpr.decreasing? _ hr

@[grind]
def RedAffNorm.raw (_r : RedAffNorm (τ_c := τ_c) A B) : NormExpr (RedAff (τ := τ_c)) := B

@[dcc_step]
def RedAffNorm.is_norm (r : RedAffNorm (τ_c := τ_c) A B) : IsNorm RedAff B.raw :=
  match r with
  | ⟨_ha, hb⟩ => hb

@[grind]
def aff_sound (heq : reduce RedAff A = ⟨B, ⟨h⟩⟩) : RedAffNorm A ⟨B, reduce_norm heq⟩ := ⟨reduce_sound heq, reduce_norm heq⟩

@[grind]
def aff_sound' (A : GenericExpr τ_c) : RedAffNorm A ⟨(reduce RedAff A).fst, reduce_norm rfl⟩ := ⟨reduce_sound rfl, reduce_norm rfl⟩

@[grind, inline, dcc_reduce]
def red_aff (A : GenericExpr τ_c) : NormExpr (RedAff (τ := τ_c)) := ⟨(reduce RedAff A).fst, reduce_norm (A := A) rfl⟩

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedAffNorm.complete {A : GenericExpr τ_c} {B : NormExpr RedAff (τ := τ_c)} (h : RedAffNorm A B) : red_aff A = B :=
  match h with
  | ⟨hr, hn⟩ => by
    have ha := reduce_complete_fst hr hn
    simp [red_aff, ha]

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedAffNorm.complete_fst {A : GenericExpr τ_c} (h : RedAffNorm A ⟨B, hn_B⟩) : (reduce RedAff A).fst = B :=
  match h with
  | ⟨hr, hn⟩ => by
    have ha := reduce_complete_fst hr hn
    simp [ha]

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedAffNorm.complete_snd {A : GenericExpr τ_c} (h : RedAffNorm A ⟨B, hn_B⟩) : (reduce RedAff A).snd = ⟨reduce_sound rfl⟩ :=
  match h with
  | ⟨hr, hn⟩ => by simp

@[dcc_reduce]
def RedAffNorm.eq (hr : RedAffNorm e (red_aff e)) : hr = aff_sound rfl :=
  match hr with
  | ⟨hr, hn⟩ => by
    have heq := reduce_complete hr hn
    grind

abbrev RedAffNorm.red (h : RedAffNorm A ⟨B, hn⟩) : RedAffReflTrans A B :=
  match h with
  | ⟨hr, _⟩ => hr

def RedAffNorm.aff_complete (h : RedAffNorm A ⟨B, hn⟩) : reduce RedAff A = ⟨B, ⟨h.red⟩⟩ :=
  match h with
  | ⟨hr₁, hn₁⟩ => reduce_complete hr₁ hn₁

def RedAffNorm.out_eq (h : RedAffNorm A B) : B = (red_aff A) :=
  match h with
  | .mk hr hn => by
    have heq := reduce_complete hr hn
    rw [red_aff]
    aesop

@[ext]
def RedAffNorm.ext (h₁ h₂ : RedAffNorm A B) : h₁ = h₂ := by
  match h₁ with
  | ⟨hr₁, hn₁⟩ =>
    match h₂ with
    | ⟨hr₂, hn₂⟩ =>
      dcc_simp_all

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def RedAffNorm.unique (h₁ : RedAffNorm A B) (h₂ : RedAffNorm A C) : B = C :=
  match h₁, h₂ with
  | ⟨ha, hb⟩, ⟨hc, hd⟩ => NormExpr.ext (norm_unique ha hb hc hd)

@[macro_inline, dcc_size, aesop safe apply (rule_sets := [DccSize]) ]
def RedAffNorm.absurd {P : Sort v} (h₁ : RedAffNorm A B) (h₂ : RedAffNorm A C) (hneq : B ≠ C := by intro h; cases h) : P :=
  _root_.absurd (h₁.unique h₂) (by simp_all)

def RedAffNorm.elim_norm (hr : RedAffNorm A B) (hn : IsNorm RedAff A) : B = ⟨A, hn⟩ :=
  match hr with
  | ⟨hr, _hn⟩ => by
    have h := hn.unique_refl hr
    cases h
    grind

def RedAffNorm.push_head (hrt : RedAffNorm A C) (hr : RedAff A B) : RedAffNorm B C :=
  match hrt with
  | ⟨hrt, hn⟩ => ⟨hrt.push_head hn hr, hn⟩

open Congruent in
def RedAffNorm.congrFun (hrt : RedAffNorm (DCC? (f x)) C) (hrt_f : RedAffNorm f ⟨f', hn_f⟩) : RedAffNorm (DCC? (f' x)) C :=
  match hrt, hrt_f with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, _hn₂⟩ =>
    ⟨
      have ⟨_, h₁, h₂⟩ := hr₁.conf (Congruent.congrFun' (hR := RedAff.instCongruent.reflTrans) hr₂)
      hn₁.unique_refl h₁ ▸ h₂, hn₁⟩

open Congruent in
def RedAffNorm.congrArg (hrt : RedAffNorm (DCC? (f x)) C) (hrt_x : RedAffNorm x ⟨x', hn_f⟩) : RedAffNorm (DCC? (f x')) C :=
  match hrt, hrt_x with
  | ⟨hr₁, hn₁⟩, ⟨hr₂, _hn₂⟩ =>
    ⟨
      have ⟨_, h₁, h₂⟩ := hr₁.conf (Congruent.congrArg' (hR := RedAff.instCongruent.reflTrans) hr₂)
      hn₁.unique_refl h₁ ▸ h₂, hn₁⟩

namespace IsNorm

def map (h : IsNorm RedAff (.map f)) : IsNorm RedAff f :=
  fun ⟨_, hr⟩ => h ⟨_, .map₀ hr⟩

def unmap (h : IsNorm RedAff (.unmap f)) : IsNorm RedAff f :=
  fun ⟨_, hr⟩ => h ⟨_, .unmap₀ hr⟩

end IsNorm

end GenericExpr

abbrev Expr.RedAff := GenericExpr.RedAff (τ := Unit)
