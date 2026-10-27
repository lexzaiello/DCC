import Dcc.Attrs
import Dcc.Ast.Core
import Dcc.Ast.Dsl
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.OfArity
import Mathlib.Data.Fin.Tuple.Curry

open Dsl

namespace Expr

@[inline, grind, dcc_size]
def point_arity (e : Expr) : ℕ :=
  open Dsl in match e with
  | DCC? (? _x) => 1
  | DCC? (𝟘.Rec _motive) => 1
  | DCC? (𝟚.Rec _motive _x _y) => 3
  | DCC? 𝟙₂ => 0
  | DCC? 𝟘₂ => 0
  | DCC? 𝟚 => 0
  | DCC[.] ∗ => 0
  | DCC[.] 𝟙 => 0
  | DCC[.] 𝟘 => 0
  | DCC[.] (= _A _x _y) => 3
  | DCC[.] (Eql _α)  => 1
  | DCC[.] (=' _α)  => 1
  | DCC[.] (refl _α) => 1
  | DCC[.] Sort _m => 0
  | DCC[.] (Σ_α _β) => 2
  | DCC[.] (Σ'_α _β) => 2
  | DCC[.] (`_β _x) => 2
  | DCC[.] (,__β _x _y) => 3
  | DCC[.] (Id _α)      => 1
  | DCC[.] (Fst _α)    => 1
  | DCC[.] (Swap _B _C) => 2
  | DCC[.] (Snd _α)    => 1
  | DCC[.] (Π _α _β) => 2
  | DCC[.] (∘ _f _g)  => 2
  | DCC[.] (⟨,⟩_β _a _b)   => 3
  | DCC[.] (Λ _α _β _x) => 3
  | DCC[.] (!Λ _α _β _x) => 3
  | DCC[.] (Eval _α _β _x) => 3
  | DCC[.] (!_x)   => 1
  | DCC[.] (*_f)    => 1
  | DCC[.] (&_x)   => 1
  | DCC[.] (!<> _x)   => 1
  | DCC[.] ($<> _x)   => 1
  | DCC[.] (_f _x)
  | .hole _n => 0

@[aesop norm (rule_sets := [DccForceReduce]), grind, dcc_rel]
def points (e : Expr) : Vector Expr (point_arity e) :=
  match e with
  | DCC? (𝟘.Rec motive) => ⟨#[motive], by grind⟩
  | DCC? (𝟚.Rec motive x y) => ⟨#[motive, x, y], by grind⟩
  | DCC[.] ∗ => ⟨#[], by grind⟩
  | DCC? (? m) => ⟨#[m], by grind⟩
  | DCC? 𝟚 | DCC? 𝟘₂ | DCC? 𝟙₂ | DCC[.] 𝟙 => ⟨#[], by grind⟩
  | DCC[.] 𝟘 => ⟨#[], by grind⟩
  | DCC[.] (= A x y) => ⟨#[A, x, y], by grind⟩
  | DCC[.] (Eql α)  => ⟨#[α], by grind⟩
  | DCC[.] (=' α)  => ⟨#[α], by grind⟩
  | DCC[.] (refl α) => ⟨#[α], by grind⟩
  | DCC[.] Sort _m => ⟨#[], by grind⟩
  | DCC[.] (Σ α β) => ⟨#[α, β], by grind⟩
  | DCC[.] (Σ' α β) => ⟨#[α, β], by grind⟩
  | DCC[.] (`β x) => ⟨#[β, x], by grind⟩
  | DCC[.] (,β x y) => ⟨#[β, x, y], by grind⟩
  | DCC[.] (Id α)      => ⟨#[α], by grind⟩
  | DCC[.] (Fst α)    => ⟨#[α], by grind⟩
  | DCC[.] (Swap B C)    => ⟨#[B, C], by grind⟩
  | DCC[.] (Snd α)    => ⟨#[α], by grind⟩
  | DCC[.] (Π α β) => ⟨#[α, β], by grind⟩
  | DCC[.] (∘ f g)  => ⟨#[f, g], by grind⟩
  | DCC[.] (⟨,⟩β a b)   => ⟨#[β, a, b], by grind⟩
  | DCC[.] (Λ α β x) => ⟨#[α, β, x], by grind⟩
  | DCC[.] (!Λ α β x) => ⟨#[α, β, x], by grind⟩
  | DCC[.] (Eval α β x) => ⟨#[α, β, x], by grind⟩
  | DCC[.] (!x)   => ⟨#[x], by grind⟩
  | DCC[.] (*f)    => ⟨#[f], by grind⟩
  | DCC[.] (&x)   => ⟨#[x], by grind⟩
  | DCC[.] (!<> x)   => ⟨#[x], by grind⟩
  | DCC[.] ($<> x)   => ⟨#[x], by grind⟩
  | DCC[.] (_f _x) => ⟨#[], by grind⟩
  | .hole _n => ⟨#[], by grind⟩

@[aesop norm (rule_sets := [DccForceReduce]), grind, dcc_reduce]
def set_points (e : Expr) (points' : Vector Expr (point_arity e)) : Expr :=
  match e with
  | DCC? (𝟘.Rec motive) =>
    have heq : point_arity (DCC? (𝟘.Rec motive)) = 1 := by grind
    .ind_bot points'[0]
  | DCC? ∗ => .tintro
  | DCC? 𝟙 => .top
  | DCC? 𝟘 => .bot
  | DCC? 𝟙₂ => .true
  | DCC? 𝟘₂ => .false
  | DCC? 𝟚 => .bool
  | DCC? (? m) =>
    have heq : point_arity (DCC? (? m)) = 1 := by grind
    .hole_ty points'[0]
  | DCC? (𝟚.Rec motive x y) =>
    have heq : point_arity (DCC? (𝟚.Rec motive x y)) = 3 := by grind
    .ind_bool points'[0] points'[1] points'[2]
  | DCC? (= A x y) =>
    have heq : point_arity (DCC? (= A x y)) = 3 := by grind
    .eq points'[0] points'[1] points'[2]
  | DCC? (Eql α)  =>
    have heq : point_arity (DCC? (Eql α)) = 1 := by grind
    .eql points'[0]
  | DCC? (=' α)  =>
    have heq : point_arity (DCC? (=' α)) = 1 := by grind
    .eq_mk points'[0]
  | DCC? (refl α) =>
    have heq : point_arity (DCC? (refl α)) = 1 := by grind
    .refl points'[0]
  | DCC? Sort m => .sort m
  | DCC? (Σ α β) =>
    have heq : point_arity (DCC? (Σ α β)) = 2 := by grind
    .sigma points'[0] points'[1]
  | DCC? (Σ' α β) =>
    have heq : point_arity (DCC? (Σ' α β)) = 2 := by grind
    .sigma' points'[0] points'[1]
  | DCC? (`β x) =>
    have heq : point_arity (DCC? (`β x)) = 2 := by grind
    .quot points'[0] points'[1]
  | DCC? (,β x y) =>
    have heq : point_arity (DCC? (,β x y)) = 3 := by grind
    .mkc points'[0] points'[1] points'[2]
  | DCC? (Id α)      =>
    have heq : point_arity (DCC? (Id α)) = 1 := by grind
    .id points'[0]
  | DCC? (Fst α)    =>
    have heq : point_arity (DCC? (Fst α)) = 1 := by grind
    .fstc points'[0]
  | DCC? (Swap B C)    =>
    have heq : point_arity (DCC? (Swap B C)) = 2 := by grind
    .swap points'[0] points'[1]
  | DCC? (Snd α)    =>
    have heq : point_arity (DCC? (Snd α)) = 1 := by grind
    .sndc points'[0]
  | DCC? (Π α β) =>
    have heq : point_arity (DCC? (Π α β)) = 2 := by grind
    .pi points'[0] points'[1]
  | DCC? (∘ f g)  =>
    have heq : point_arity (DCC? (∘ f g)) = 2 := by grind
    .comp points'[0] points'[1]
  | DCC? (⟨,⟩β a b)   =>
    have heq : point_arity (DCC? (⟨,⟩β a b)) = 3 := by grind
    .pair points'[0] points'[1] points'[2]
  | DCC? (Λ α β x) =>
    have heq : point_arity (DCC? (Λ α β x)) = 3 := by grind
    .curr points'[0] points'[1] points'[2]
  | DCC? (!Λ α β x) =>
    have heq : point_arity (DCC? (!Λ α β x)) = 3 := by grind
    .curr' points'[0] points'[1] points'[2]
  | DCC? (Eval α β x) =>
    have heq : point_arity (DCC? (Eval α β x)) = 3 := by grind
    .eval points'[0] points'[1] points'[2]
  | DCC? (!x)   =>
    have heq : point_arity (DCC? (!x)) = 1 := by grind
    .bang points'[0]
  | DCC? (*f)    =>
    have heq : point_arity (DCC? (*f)) = 1 := by grind
    .unbox points'[0]
  | DCC? (&x)   =>
    have heq : point_arity (DCC? (&x)) = 1 := by grind
    .box points'[0]
  | DCC? (!<> x)   =>
    have heq : point_arity (DCC? (!<> x)) = 1 := by grind
    .map points'[0]
  | DCC? ($<> x)   =>
    have heq : point_arity (DCC? ($<> x)) = 1 := by grind
    .fmap points'[0]
  | DCC? (f x) => .app f x
  | .hole n => .hole n

theorem set_points_eq_set_points₁ : set_points e ⟨#[x], h⟩ = (e.set_points (e.points.set 0 (h := by grind) x)) := by
  induction e
  any_goals (grind)
  any_goals (simp [set_points, points])

theorem set_points_eq_set_points₂ : set_points e ⟨#[x, y], h⟩ = (e.set_points ((e.points.set 0 (h := by grind) x).set 1 (h := by grind) y)) := by
  induction e
  any_goals (grind)
  any_goals (simp [set_points, points])

theorem set_points_eq_set_points₃ : set_points e ⟨#[x, y, z], h⟩ = (e.set_points (((e.points.set 0 (h := by grind) x).set 1 (h := by grind) y).set 2 (h := by grind) z)) := by
  induction e
  any_goals (grind)
  any_goals (simp [set_points, points])

theorem set_points_eq_set_points₄ : set_points e ⟨#[x, y, z, z'], h⟩ = (e.set_points ((((e.points.set 0 (h := by grind) x).set 1 (h := by grind) y).set 2 (h := by grind) z).set 3 (h := by grind) z')) := by
  induction e
  any_goals (grind)

@[grind =_, grind ., grind! ., dcc_rel]
theorem congr_point_arr {e : Expr} {p : Fin (point_arity e)} : point_arity e = point_arity (set_points e ((points e).set p p')) := by
  induction e <;> grind

theorem congr_point_lt (h : n < point_arity e := by assumption) : n < point_arity (set_points e (e.points.set n p' hn)) := by
  induction e <;> grind

theorem set_points_eq_set_points₂' : set_points e ⟨#[x, y], h⟩ = (set_points (e.set_points (e.points.set 0 (h := by grind) x)) ((points (e.set_points (e.points.set 0 (h := by grind) x))).set 1 (h := by
  have h := congr_point_arr (e := e) (p := ⟨0, by grind⟩) (p' := x)
  grind) y)) := by
  induction e
  any_goals (grind)
  any_goals (simp [set_points, points])

-- congr_point_arr (h : r e (set_points e ((points e).set p p'))) : point_arity e = (set_points e ((points e).set p p'))

@[grind =, grind! ., dcc_rel]
theorem set_points_self_noop : set_points e e.points = e := by
  induction e
  any_goals (first | grind | aesop)

@[grind =, grind ., dcc_rel]
theorem get_set_point {e p' : Expr} {p : Fin (point_arity e)} : (points (set_points e ((points e).set p p'))).get ⟨p, by rw [← congr_point_arr]; grind⟩ = p' := by
  induction e
  any_goals (grind)
  any_goals (
    focus
    try (
      rename_i a_ih
      dcc_simp at p
      fin_cases p <;> (dcc_simp; rfl)))

theorem get_set_point' {n : ℕ} {hn : n < point_arity e} {p : Fin (point_arity e)} (heq : p = ⟨n, hn⟩) : (set_points e (e.points.set n (e.points.get p) hn)) = e := by
  induction e
  any_goals (grind)
  any_goals (
    focus
    try (
      simp [point_arity] at p
      fin_cases p
      any_goals (
        cases heq
        simp [set_points, points]
        rfl)))

set_option maxHeartbeats 100000000000 in
@[grind =, grind! .]
theorem set_same_point_comp {e x y : Expr} {p : Fin (point_arity e)} : set_points (set_points e ((points e).set p x)) ((points (set_points e ((points e).set p x))).set (h := by rw [← congr_point_arr]; grind) p y) = set_points e ((points e).set p y) := by
  induction e <;> grind

@[grind, dcc_size, aesop safe norm (rule_sets := [DccSize])]
def max_hole (e : Expr) : ℕ :=
  match e with
  | DCC? (𝟚.Rec motive x y) => max motive.max_hole (max x.max_hole y.max_hole)
  | DCC? (𝟘.Rec motive) => motive.max_hole
  | DCC? (? m) => m.max_hole
  | DCC? 𝟚 | DCC? 𝟘₂ | DCC? 𝟙₂ => 0
  | DCC? ∗ => 0
  | DCC? 𝟙 => 0
  | DCC? 𝟘 => 0
  | DCC? (= A x y) => max A.max_hole (max x.max_hole y.max_hole)
  | DCC? (=' B)  => B.max_hole
  | DCC? (Eql B)  => B.max_hole
  | DCC? (refl B) => B.max_hole
  | DCC? Sort _m => 0
  | DCC? (Σ B C) => max B.max_hole C.max_hole
  | DCC? (Σ' B C) => max B.max_hole C.max_hole
  | DCC? (`B x) => max B.max_hole x.max_hole
  | DCC? (,B x y) => max B.max_hole (max x.max_hole y.max_hole)
  | DCC? (Id A)      => A.max_hole
  | DCC? (Fst B)    => B.max_hole
  | DCC? (Snd B)    => B.max_hole
  | DCC? (Swap B C)    => max B.max_hole C.max_hole
  | DCC? (Π B C) => max B.max_hole C.max_hole
  | DCC? (∘ x y)  => max x.max_hole y.max_hole
  | DCC? (⟨,⟩B x y)   => max B.max_hole (max x.max_hole y.max_hole)
  | DCC? (Λ A B x) => max A.max_hole (max B.max_hole x.max_hole)
  | DCC? (!Λ A B x) => max A.max_hole (max B.max_hole x.max_hole)
  | DCC? (Eval A B x) => max A.max_hole (max B.max_hole x.max_hole)
  | DCC? (!x)   => x.max_hole
  | DCC? (*x)    => x.max_hole
  | DCC? (&x)   => x.max_hole
  | DCC? (!<> x)   => x.max_hole
  | DCC? ($<> x)   => x.max_hole
  | DCC? (f x) => max f.max_hole x.max_hole
  | .hole n => n

@[grind, dcc_size, aesop safe norm (rule_sets := [DccSize])]
def min_hole (e : Expr) : ℕ :=
  match e with
  | DCC? (𝟚.Rec motive x y) => min motive.min_hole (min x.min_hole y.min_hole)
  | DCC? (𝟘.Rec motive) => motive.min_hole
  | DCC? (? m) => m.min_hole
  | DCC? 𝟚 | DCC? 𝟘₂ | DCC? 𝟙₂ => 0
  | DCC? ∗ => 0
  | DCC? 𝟙 => 0
  | DCC? 𝟘 => 0
  | DCC? (= A x y) => min A.min_hole (min x.min_hole y.min_hole)
  | DCC? (=' B)  => B.min_hole
  | DCC? (Eql B)  => B.min_hole
  | DCC? (refl B) => B.min_hole
  | DCC? Sort _m => 0
  | DCC? (Σ B C) => min B.min_hole C.min_hole
  | DCC? (Σ' B C) => min B.min_hole C.min_hole
  | DCC? (`B x) => min B.min_hole x.min_hole
  | DCC? (,B x y) => min B.min_hole (min x.min_hole y.min_hole)
  | DCC? (Id A)      => A.min_hole
  | DCC? (Fst B)    => B.min_hole
  | DCC? (Snd B)    => B.min_hole
  | DCC? (Swap B C)    => min B.min_hole C.min_hole
  | DCC? (Π B C) => min B.min_hole C.min_hole
  | DCC? (∘ x y)  => min x.min_hole y.min_hole
  | DCC? (⟨,⟩B x y)   => min B.min_hole (min x.min_hole y.min_hole)
  | DCC? (Λ A B x) => min A.min_hole (min B.min_hole x.min_hole)
  | DCC? (!Λ A B x) => min A.min_hole (min B.min_hole x.min_hole)
  | DCC? (Eval A B x) => min A.min_hole (min B.min_hole x.min_hole)
  | DCC? (!x)   => x.min_hole
  | DCC? (*x)    => x.min_hole
  | DCC? (&x)   => x.min_hole
  | DCC? (!<> x)   => x.min_hole
  | DCC? ($<> x)   => x.min_hole
  | DCC? (f x) => min f.min_hole x.min_hole
  | .hole n => n

def cases_point_arity (e : Expr) : point_arity e = 0 ∨ point_arity e = 1 ∨ point_arity e = 2 ∨ point_arity e = 3 ∨ point_arity e = 4 := by
  induction e
  any_goals (simp [point_arity])

def cases_point_arity' (e : Expr) : (PLift (point_arity e = 0)) ⊕ (PLift (point_arity e = 1)) ⊕ (PLift (point_arity e = 2)) ⊕ (PLift (point_arity e = 3)) ⊕ (PLift (point_arity e = 4)) :=
  match heq : point_arity e with
  | 0 => .inl ⟨rfl⟩
  | 1 => .inr (.inl ⟨rfl⟩)
  | 2 => .inr (.inr (.inl ⟨rfl⟩))
  | 3 => .inr (.inr (.inr (.inl ⟨rfl⟩)))
  | 4 => .inr (.inr (.inr (.inr ⟨rfl⟩)))
  | .succ (.succ (.succ (.succ (.succ n)))) => by
    unfold point_arity at heq
    split at heq
    any_goals (grind)

set_option maxHeartbeats 100000000000 in
theorem get_unset_point (hneq : m ≠ n) : ((set_points e (e.points.set m x' h₁)).points.get ⟨n, h₂⟩) = e.points.get ⟨n, by
  have h := congr_point_arr (e := e) (p := ⟨m, h₁⟩) (p' := x')
  grind⟩ := by
  have h₃ := congr_point_arr (e := e) (p := ⟨m, h₁⟩) (p' := x')
  --cases e
  match cases_point_arity e with
  | .inr (.inr (.inr (.inr h))) =>
    cases e
    any_goals (grind)
  | .inr (.inr (.inr (.inl h))) =>
    cases e
    any_goals (grind)
    all_goals (
      simp [point_arity] at h₁
      have hn_n : n < 3 := by grind
      match m with
      | 0 =>
        match n with
        | 0 => exact (hneq rfl).elim
        | 2 | 1 => simp [set_points, points, Vector.get]
      | 1 =>
        match n with
        | 2 | 0 =>
          simp [set_points, points, Vector.get]
        | 1 => exact (hneq rfl).elim
      | 2 =>
        match n with
        | 1 | 0 =>
          simp [set_points, points, Vector.get]
        | 2 => exact (hneq rfl).elim)
  | .inr (.inr (.inl h)) =>
    cases e
    any_goals (
      focus
      simp [point_arity] at h
      done)
    all_goals (
      simp [point_arity] at h₁
      have hn_n : n < 2 := by grind
      match m with
      | 0 =>
        match n with
        | 0 => exact (hneq rfl).elim
        | 1 => simp [set_points, points, Vector.get]
      | 1 =>
        match n with
        | 0 =>
          simp [set_points, points, Vector.get]
        | 1 => exact (hneq rfl).elim)
  | .inr (.inl h) =>
    cases e
    any_goals (grind)
  | .inl h =>
    cases e
    any_goals (
      focus
      simp [point_arity] at h
      done)
    all_goals (simp [point_arity] at h₁)

end Expr
