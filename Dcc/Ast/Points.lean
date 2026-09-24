import Dcc.Attrs
import Dcc.Ast.Core
import Dcc.Ast.Dsl
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.OfArity
import Mathlib.Data.Fin.Tuple.Curry

open Dsl

namespace GenericExpr

@[inline, grind, dcc_size]
def point_arity (e : GenericExpr (τ := τ_c)) : ℕ :=
  open Dsl in match e with
  | DCC? (≃.mk _to_fun _inv_fun _comp_id _id_comp) => 4
  | DCC? (≃.Ind _motive _x) => 2
  | DCC? (≃.1 _x _y) => 2
  | DCC? (≃.2 _x _y) => 2
  | DCC? (≃.3 _x _y) => 2
  | DCC? (≃.4 _x _y) => 2
  | DCC? (⊥.Ind _motive) => 1
  | DCC? (Bool.Ind _motive _x _y) => 3
  | DCC? (? _m) => 0
  | DCC? _A ≃ _B => 2
  | DCC? True => 0
  | DCC? False => 0
  | DCC? Bool => 0
  | DCC? (Unify _τ₁ _τ₂ _A _B) => 4
  | DCC? (Dom _x) => 0
  | DCC? (Dom₂ _x) => 0
  | DCC? (Uncoup _x) => 0
  | DCC? (Unbang _x) => 0
  | DCC[.] ∗ => 0
  | DCC[.] ⊤ => 0
  | DCC[.] ⊥ => 0
  | DCC[.] _x = _y => 2
  | DCC[.] (Eql _α)  => 1
  | DCC[.] (refl _α) => 1
  | DCC[.] Sort _m => 0
  | DCC[.] (Σ_α _β) => 2
  | DCC[.] (`_β _x) => 2
  | DCC[.] (,__β _x _y) => 3
  | DCC[.] (Σ_β) => 1
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
  | .const _n => 0
  | .hole _n => 0

@[aesop norm (rule_sets := [DccForceReduce]), grind, dcc_rel]
def points (e : GenericExpr (τ := τ_c)) : Vector (GenericExpr (τ := τ_c)) (point_arity e) :=
  match e with
  | DCC? (≃.mk to_fun inv_fun comp_id id_comp) => ⟨#[to_fun, inv_fun, comp_id, id_comp], by simp [point_arity]⟩
  | DCC? (≃.Ind motive x) => ⟨#[motive, x], by grind⟩
  | DCC? (≃.1 x y) => ⟨#[x, y], by grind⟩
  | DCC? (≃.2 x y) => ⟨#[x, y], by grind⟩
  | DCC? (≃.3 x y) => ⟨#[x, y], by grind⟩
  | DCC? (≃.4 x y) => ⟨#[x, y], by grind⟩
  | DCC? (⊥.Ind motive) => ⟨#[motive], by grind⟩
  | DCC? (Bool.Ind motive x y) => ⟨#[motive, x, y], by grind⟩
  | DCC? (Unify τ_A τ_B A B) => ⟨#[τ_A, τ_B, A, B], by simp [point_arity]⟩
  | DCC? A ≃ B => ⟨#[A, B], by grind⟩
  | DCC[.] (Dom _x) => ⟨#[], by grind⟩
  | DCC[.] (Dom₂ _x) => ⟨#[], by grind⟩
  | DCC? (Uncoup _x) => ⟨#[], by grind⟩
  | DCC? (Unbang _x) => ⟨#[], by grind⟩
  | DCC[.] ∗ => ⟨#[], by grind⟩
  | DCC? (? _m) | DCC? Bool | DCC? False | DCC? True | DCC[.] ⊤ => ⟨#[], by grind⟩
  | DCC[.] ⊥ => ⟨#[], by grind⟩
  | DCC[.] x = y => ⟨#[x, y], by grind⟩
  | DCC[.] (Eql α)  => ⟨#[α], by grind⟩
  | DCC[.] (refl α) => ⟨#[α], by grind⟩
  | DCC[.] Sort _m => ⟨#[], by grind⟩
  | DCC[.] (Σ α β) => ⟨#[α, β], by grind⟩
  | DCC[.] (`β x) => ⟨#[β, x], by grind⟩
  | DCC[.] (,β x y) => ⟨#[β, x, y], by grind⟩
  | DCC[.] (Σ β) => ⟨#[β], by grind⟩
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
  | .const _n => ⟨#[], by grind⟩
  | .hole _n => ⟨#[], by grind⟩

@[grind, dcc_reduce]
def uncurry (pre : GenericExpr τ_c)
  (mk    : Function.OfArity (GenericExpr τ_c) (GenericExpr τ_c) (point_arity pre))
  (f     : GenericExpr τ_c → GenericExpr τ_c) :=
  mk.uncurry (fun (i : Fin (point_arity pre)) => f ((points pre).get i))

@[grind, dcc_reduce]
def map_points (e : GenericExpr (τ := τ_c))
  (fn : GenericExpr τ_c → GenericExpr τ_c) : GenericExpr τ_c :=
  uncurry e (match e with
  | DCC? (≃.mk _a _b _c _d) => .cong_mk
  | DCC? (≃.Ind _motive _x) => .ind_cong
  | DCC? (≃.1 _x _y) => .cong_1
  | DCC? (≃.2 _x _y) => .cong_2
  | DCC? (≃.3 _x _y) => .cong_3
  | DCC? (≃.4 _x _y) => .cong_4
  | DCC? (⊥.Ind _motive) => .ind_bot
  | DCC? (Bool.Ind _motive _x _y) => .ind_bool
  | DCC? True => .true
  | DCC? False => .false
  | DCC? Bool => .bool
  | DCC? _A ≃ _B => .cong
  | DCC? (Unify _τ_A _τ_B _A _B) => .unify
  | DCC? (? m) => .hole_ty m
  | DCC? (Dom x) => Function.OfArity.const _ (DCC? (Dom x)) _
  | DCC? (Dom₂ x) => Function.OfArity.const _ (DCC? (Dom₂ x)) _
  | DCC? (Uncoup x) => Function.OfArity.const _ (DCC? (Uncoup x)) _
  | DCC? (Unbang x) => Function.OfArity.const _ (DCC? (Unbang x)) _
  | DCC? ∗ => .tintro
  | DCC? ⊤ => .top
  | DCC? ⊥ => .bot
  | DCC? _x = _y => .eq
  | DCC? (Eql _α)  => .eql
  | DCC? (refl _α) => .refl
  | DCC? Sort m => .sort m
  | DCC? (Σ _α _β) => .sigma
  | DCC? (`_β _x) => .quot
  | DCC? (,_β _x _y) => .mkc
  | DCC? (Σ_β) => .coup
  | DCC? (Id _α)      => .id
  | DCC? (Fst _α)    => .fstc
  | DCC? (Swap _B _C)    => .swap
  | DCC? (Snd _α)    => .sndc
  | DCC? (Π _α _β) => .pi
  | DCC? (∘ _f _g)  => .comp
  | DCC? (⟨,⟩_β _a _b) => .pair
  | DCC? (Λ _α _β _x) => .curr
  | DCC? (!Λ _α _β _x) => .curr'
  | DCC? (Eval _α _β _x) => .eval
  | DCC? (! _x)   => .bang
  | DCC? (* _f)    => .unbox
  | DCC? (& _x)   => .box
  | DCC? (!<> _x)   => .map
  | DCC? ($<> _x)   => .fmap
  | DCC? (f x) => .app f x
  | .const n => Function.OfArity.const _ (.const n) _
  | .hole n => Function.OfArity.const _ (.hole n) _) fn

@[aesop norm (rule_sets := [DccForceReduce]), grind, dcc_reduce]
def set_points (e : GenericExpr (τ := τ_c))
  (points' : Vector (@GenericExpr τ_c) (point_arity e)) : GenericExpr τ_c :=
  match e with
  | DCC? (≃.mk a b c d) =>
    have heq : point_arity (DCC? (≃.mk a b c d)) = 4 := by simp [point_arity]
    .cong_mk points'[0] points'[1] points'[2] points'[3]
  | DCC? (≃.Ind motive x) =>
    have heq : point_arity (DCC? (≃.Ind motive x)) = 2 := by grind
    .ind_cong points'[0] points'[1]
  | DCC? (≃.1 x y) =>
    have heq : point_arity (DCC? (≃.1 x y)) = 2 := by grind
    .cong_1 points'[0] points'[1]
  | DCC? (≃.2 x y) =>
    have heq : point_arity (DCC? (≃.2 x y)) = 2 := by grind
    .cong_2 points'[0] points'[1]
  | DCC? (≃.3 x y) =>
    have heq : point_arity (DCC? (≃.3 x y)) = 2 := by grind
    .cong_3 points'[0] points'[1]
  | DCC? (≃.4 x y) =>
    have heq : point_arity (DCC? (≃.4 x y)) = 2 := by grind
    .cong_4 points'[0] points'[1]
  | DCC? (⊥.Ind motive) =>
    have heq : point_arity (DCC? (⊥.Ind motive)) = 1 := by grind
    .ind_bot points'[0]
  | DCC? (Dom x) => DCC? (Dom x)
  | DCC? (Dom₂ x) => DCC? (Dom₂ x)
  | DCC? (Uncoup x) => DCC? (Uncoup x)
  | DCC? (Unbang x) => DCC? (Unbang x)
  | DCC? ∗ => .tintro
  | DCC? ⊤ => .top
  | DCC? ⊥ => .bot
  | DCC? True => .true
  | DCC? False => .false
  | DCC? Bool => .bool
  | DCC? (? _m) => DCC? (? _m)
  | DCC? (Bool.Ind motive x y) =>
    have heq : point_arity (DCC? (Bool.Ind motive x y)) = 3 := by grind
    .ind_bool points'[0] points'[1] points'[2]
  | DCC? x = y =>
    have heq : point_arity (DCC? x = y) = 2 := by grind
    .eq points'[0] points'[1]
  | DCC? (Eql α)  =>
    have heq : point_arity (DCC? (Eql α)) = 1 := by grind
    .eql points'[0]
  | DCC? (refl α) =>
    have heq : point_arity (DCC? (refl α)) = 1 := by grind
    .refl points'[0]
  | DCC? Sort m => .sort m
  | DCC? (Σ α β) =>
    have heq : point_arity (DCC? (Σ α β)) = 2 := by grind
    .sigma points'[0] points'[1]
  | DCC? (A ≃ B) =>
    have heq : point_arity (DCC? (A ≃ B)) = 2 := by grind
    .cong points'[0] points'[1]
  | DCC? (Unify τ_A τ_B A B) =>
    have heq : point_arity (DCC? (Unify τ_A τ_B A B)) = 4 := by dcc_simp
    .unify points'[0] points'[1] points'[2] points'[3]
  | DCC? (`β x) =>
    have heq : point_arity (DCC? (`β x)) = 2 := by grind
    .quot points'[0] points'[1]
  | DCC? (,β x y) =>
    have heq : point_arity (DCC? (,β x y)) = 3 := by grind
    .mkc points'[0] points'[1] points'[2]
  | DCC? (Σβ) =>
    have heq : point_arity (DCC? (Σβ)) = 1 := by grind
    .coup points'[0]
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
  | .const n => .const n
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
  any_goals (simp [set_points, points])

-- congr_point_arr (h : r e (set_points e ((points e).set p p'))) : point_arity e = (set_points e ((points e).set p p'))

@[grind =, grind! ., dcc_rel]
theorem set_points_self_noop : set_points e e.points = e := by
  induction e
  any_goals (first | grind | aesop)

@[grind =_, grind ., grind! ., dcc_rel]
theorem congr_point_arr {e : GenericExpr τ_c} {p : Fin (point_arity e)} : point_arity e = point_arity (set_points e ((points e).set p p')) := by
  induction e <;> grind

theorem congr_point_lt (h : n < point_arity e := by assumption) : n < point_arity (set_points e (e.points.set n p' hn)) := by
  induction e <;> grind

@[grind =, grind ., dcc_rel]
theorem get_set_point {e p' : GenericExpr τ_c} {p : Fin (point_arity e)} : (points (set_points e ((points e).set p p'))).get ⟨p, by rw [← congr_point_arr]; grind⟩ = p' := by
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

@[grind =, grind! .]
theorem set_same_point_comp {e x y : GenericExpr τ_c} {p : Fin (point_arity e)} : set_points (set_points e ((points e).set p x)) ((points (set_points e ((points e).set p x))).set (h := by rw [← congr_point_arr]; grind) p y) = set_points e ((points e).set p y) := by
  induction e <;> grind

@[grind =]
theorem map_points_id (e : GenericExpr τ) : map_points e _root_.id = e := by
  cases e <;> aesop

@[grind ., grind =>]
theorem map_points_ar_eq (heq : map_points e fn = e') : point_arity e = point_arity e' := by
  cases e <;> aesop

@[grind =, grind =_, grind! .]
theorem map_points_map {e : GenericExpr τ} : points (map_points e fn) ≍ Vector.map fn (points e) := by
  cases e <;> (
    focus
    try (
      conv =>
        right
        simp [points]
        rfl
      simp [map_points, uncurry, Function.OfArity.uncurry]
      aesop))

@[grind ., grind =>, grind! .]
theorem map_points_eq {e e' : GenericExpr τ} (heq : map_points e fn = e') : points e' ≍ (points e).map fn := by
  cases e <;> grind

@[grind, dcc_size, aesop safe norm (rule_sets := [DccSize])]
def max_hole (e : GenericExpr τ_c) : ℕ :=
  match e with
  | DCC? (≃.mk a b c d) => max a.max_hole (max b.max_hole (max c.max_hole d.max_hole))
  | DCC? (Bool.Ind motive x y) => max motive.max_hole (max x.max_hole y.max_hole)
  | DCC? (≃.Ind motive x) => max motive.max_hole x.max_hole
  | DCC? (≃.1 x y) => max x.max_hole y.max_hole
  | DCC? (≃.2 x y) => max x.max_hole y.max_hole
  | DCC? (≃.3 x y) => max x.max_hole y.max_hole
  | DCC? (≃.4 x y) => max x.max_hole y.max_hole
  | DCC? (⊥.Ind motive) => motive.max_hole
  | DCC? A ≃ B => max A.max_hole B.max_hole
  | DCC? (Unify τ_A τ_B A B) => max τ_A.max_hole (max τ_B.max_hole (max A.max_hole B.max_hole))
  | DCC? (? _m) => 0
  | DCC? Bool | DCC? False | DCC? True => 0
  | DCC? (Dom x) => x.max_hole
  | DCC? (Dom₂ x) => x.max_hole
  | DCC? (Uncoup x) => x.max_hole
  | DCC? (Unbang x) => x.max_hole
  | DCC? ∗ => 0
  | DCC? ⊤ => 0
  | DCC? ⊥ => 0
  | DCC? x = y => max x.max_hole y.max_hole
  | DCC? (Eql B)  => B.max_hole
  | DCC? (refl B) => B.max_hole
  | DCC? Sort _m => 0
  | DCC? (Σ B C) => max B.max_hole C.max_hole
  | DCC? (`B x) => max B.max_hole x.max_hole
  | DCC? (,B x y) => max B.max_hole (max x.max_hole y.max_hole)
  | DCC? (Σ B) => B.max_hole
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
  | .const _n => 0
  | .hole n => n

@[grind]
def min_hole (e : GenericExpr τ_c) : ℕ :=
  match e with
  | DCC? (≃.mk a b c d) => min a.min_hole (min b.min_hole (min c.min_hole d.min_hole))
  | DCC? (Bool.Ind motive x y) => min motive.min_hole (min x.min_hole y.min_hole)
  | DCC? (≃.Ind motive x) => min motive.min_hole x.min_hole
  | DCC? (≃.1 x y) => min x.min_hole y.min_hole
  | DCC? (≃.2 x y) => min x.min_hole y.min_hole
  | DCC? (≃.3 x y) => min x.min_hole y.min_hole
  | DCC? (≃.4 x y) => min x.min_hole y.min_hole
  | DCC? (⊥.Ind motive) => motive.min_hole
  | DCC? A ≃ B => min A.min_hole B.min_hole
  | DCC? (? _m) => 0
  | DCC? True | DCC? False | DCC? Bool => 0
  | DCC? (Unify τ_A τ_B A B) => min τ_A.min_hole (min τ_B.min_hole (min A.min_hole B.min_hole))
  | DCC? (Dom x) => x.min_hole
  | DCC? (Dom₂ x) => x.min_hole
  | DCC? (Uncoup x) => x.min_hole
  | DCC? (Unbang x) => x.min_hole
  | DCC? ∗ => 0
  | DCC? ⊤ => 0
  | DCC? ⊥ => 0
  | DCC? x = y => min x.min_hole y.min_hole
  | DCC? (Eql B)  => B.min_hole
  | DCC? (refl B) => B.min_hole
  | DCC? Sort _m => 0
  | DCC? (Σ B C) => min B.min_hole C.min_hole
  | DCC? (` B x) => min B.min_hole x.min_hole
  | DCC? (,B x y) => min B.min_hole (min x.min_hole y.min_hole)
  | DCC? (Σ B) => B.min_hole
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
  | DCC? (! x)   => x.min_hole
  | DCC? (* x)    => x.min_hole
  | DCC? (& x)   => x.min_hole
  | DCC? (!<> x)   => x.min_hole
  | DCC? ($<> x)   => x.min_hole
  | DCC? (f x) => min f.min_hole x.min_hole
  | .const _n => 0
  | .hole n => n

def cases_point_arity (e : GenericExpr τ_c) : point_arity e = 0 ∨ point_arity e = 1 ∨ point_arity e = 2 ∨ point_arity e = 3 ∨ point_arity e = 4 := by
  induction e
  any_goals (simp [point_arity])

def cases_point_arity' (e : GenericExpr τ_c) : (PLift (point_arity e = 0)) ⊕ (PLift (point_arity e = 1)) ⊕ (PLift (point_arity e = 2)) ⊕ (PLift (point_arity e = 3)) ⊕ (PLift (point_arity e = 4)) :=
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

theorem get_unset_point (hneq : m ≠ n) : ((set_points (τ_c := τ_c) e (e.points.set m x' h₁)).points.get ⟨n, h₂⟩) = e.points.get ⟨n, by
  have h := congr_point_arr (e := e) (p := ⟨m, h₁⟩) (p' := x')
  grind⟩ := by
  have h₃ := congr_point_arr (e := e) (p := ⟨m, h₁⟩) (p' := x')
  --cases e
  match cases_point_arity e with
  | .inr (.inr (.inr (.inr h))) =>
    cases e
    any_goals (grind)
    all_goals (
      simp [point_arity] at h₁
      have hn_n : n < 4 := by grind
      match m with
      | 0 =>
        match n with
        | 0 => exact (hneq rfl).elim
        | 3 | 2 | 1 => simp [set_points, points, Vector.get]
      | 1 =>
        match n with
        | 3 | 2 | 0 =>
          simp [set_points, points, Vector.get]
        | 1 => exact (hneq rfl).elim
      | 2 =>
        match n with
        | 1 | 3 | 0 =>
          simp [set_points, points, Vector.get]
        | 2 => exact (hneq rfl).elim
      | 3 =>
        match n with
        | 2 | 1 | 0 =>
          simp [set_points, points, Vector.get]
        | 3 => exact (hneq rfl).elim)
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

end GenericExpr
