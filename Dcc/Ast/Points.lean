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
  match e with
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

@[grind, dcc_size]
def branch_arity (e : GenericExpr (τ := τ_c)) : ℕ :=
  match e with
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
  | DCC[.] (Σ _α _β) => 2
  | DCC[.] (`_β _x) => 2
  | DCC[.] (,__β _x _y) => 3
  | DCC[.] (Σ_β) => 1
  | DCC[.] (Id _α)      => 1
  | DCC[.] (Fst _α)    => 1
  | DCC[.] (Snd _α)    => 1
  | DCC[.] (Swap _B _C) => 2
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
  | DCC[.] (_f _x) => 2
  | .const _n => 0
  | .hole _n => 0

@[grind]
def branches (e : GenericExpr (τ := τ_c)) : Vector (GenericExpr (τ := τ_c)) (branch_arity e) :=
  match e with
  | DCC? (Dom x) => ⟨#[], by grind⟩
  | DCC? (Dom₂ x) => ⟨#[], by grind⟩
  | DCC? (Uncoup _x) => ⟨#[], by grind⟩
  | DCC? (Unbang _x) => ⟨#[], by grind⟩
  | DCC[.] ∗ => ⟨#[], by grind⟩
  | DCC[.] ⊤ => ⟨#[], by grind⟩
  | DCC[.] ⊥ => ⟨#[], by grind⟩
  | DCC[.] x = y => ⟨#[x, y], by grind⟩
  | DCC[.] (Eql α)  => ⟨#[α], by grind⟩
  | DCC[.] (refl α) => ⟨#[α], by grind⟩
  | DCC[.] Sort _m => ⟨#[], by grind⟩
  | DCC[.] (Σ α β) => ⟨#[α, β], by grind⟩
  | DCC[.] (`β x) => ⟨#[β, x], by grind⟩
  | DCC[.] (,β x y) => ⟨#[β, x, y], by grind⟩
  | DCC[.] (Σβ) => ⟨#[β], by grind⟩
  | DCC[.] (Id α)      => ⟨#[α], by grind⟩
  | DCC[.] (Fst α)    => ⟨#[α], by grind⟩
  | DCC[.] (Snd α)    => ⟨#[α], by grind⟩
  | DCC[.] (Swap B C)    => ⟨#[B, C], by grind⟩
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
  | DCC[.] (f x) => ⟨#[f, x], by grind⟩
  | .const _n => ⟨#[], by grind⟩
  | .hole _n => ⟨#[], by grind⟩

/-
How many points there are that index the environment,
determining a resulting term.
-/
@[grind, dcc_size]
def n_indices (e : GenericExpr (τ := τ_c)) : ℕ :=
  match e with
  | DCC? (Dom _x) => 0
  | DCC? (Dom₂ _x) => 0
  | DCC? (Uncoup _x) => 0
  | DCC? (Unbang _x) => 0
  | DCC[.] ∗ => 0
  | DCC[.] ⊤ => 0
  | DCC[.] ⊥ => 0
  | DCC[.] _x = _y => 0
  | DCC[.] (Eql _α)  => 0
  | DCC[.] (refl _α) => 0
  | DCC[.] Sort _m => 0
  | DCC[.] (Σ _α _β) => 2
  | DCC[.] (`_β _x) => 0
  | DCC[.] (,__β _x _y) => 0
  | DCC[.] (Σ _β) => 0
  | DCC[.] (Id _α)      => 0
  | DCC[.] (Fst _α)    => 0
  | DCC[.] (Swap _B _C)    => 0
  | DCC[.] (Snd _α)    => 0
  | DCC[.] (Π _α _β) => 2
  | DCC[.] (∘ _f _g)  => 0
  | DCC[.] (⟨,⟩_β _a _b)   => 0
  | DCC[.] (Λ _α _β _x) => 0
  | DCC[.] (!Λ _α _β _x) => 0
  | DCC[.] (Eval _α _β _x) => 0
  | DCC[.] (!_x)   => 0
  | DCC[.] (*_f)    => 1
  | DCC[.] (&_x)   => 0
  | DCC[.] (!<> _x)   => 1
  | DCC[.] ($<> _x)   => 1
  | DCC[.] (_f _x)
  | .const _n => 0
  | .hole _n => 0

@[grind, dcc_size]
def indices (e : GenericExpr (τ := τ_c)) : Vector (GenericExpr (τ := τ_c)) (n_indices e) :=
  match e with
  | DCC[.] (Dom _x) => ⟨#[], by grind⟩
  | DCC[.] (Dom₂ _x) => ⟨#[], by grind⟩
  | DCC? (Uncoup _x) => ⟨#[], by grind⟩
  | DCC? (Unbang _x) => ⟨#[], by grind⟩
  | DCC[.] ∗ => ⟨#[], by grind⟩
  | DCC[.] ⊤ => ⟨#[], by grind⟩
  | DCC[.] ⊥ => ⟨#[], by grind⟩
  | DCC[.] _x = _y => ⟨#[], by grind⟩
  | DCC[.] (Eql _α)  => ⟨#[], by grind⟩
  | DCC[.] (refl _α) => ⟨#[], by grind⟩
  | DCC[.] Sort _m => ⟨#[], by grind⟩
  | DCC[.] (Σ α β) => ⟨#[α, β], by grind⟩
  | DCC[.] (`_β _x) => ⟨#[], by grind⟩
  | DCC[.] (,__β _x _y) => ⟨#[], by grind⟩
  | DCC[.] (Σ_β) => ⟨#[], by grind⟩
  | DCC[.] (Id _α)      => ⟨#[], by grind⟩
  | DCC[.] (Fst _α)    => ⟨#[], by grind⟩
  | DCC[.] (Swap _B _C)    => ⟨#[], by grind⟩
  | DCC[.] (Snd _α)    => ⟨#[], by grind⟩
  | DCC[.] (Π α β) => ⟨#[α, β], by grind⟩
  | DCC[.] (∘ _f _g)  => ⟨#[], by grind⟩
  | DCC[.] (⟨,⟩_β _a _b)   => ⟨#[], by grind⟩
  | DCC[.] (Λ _α _β _x) => ⟨#[], by grind⟩
  | DCC[.] (!Λ _α _β _x) => ⟨#[], by grind⟩
  | DCC[.] (Eval _α _β _x) => ⟨#[], by grind⟩
  | DCC[.] (!_x)   => ⟨#[], by grind⟩
  | DCC[.] (*f)    => ⟨#[f], by grind⟩
  | DCC[.] (&_x)   => ⟨#[], by grind⟩
  | DCC[.] (!<> x)   => ⟨#[x], by grind⟩
  | DCC[.] ($<> x)   => ⟨#[x], by grind⟩
  | DCC[.] (_f _x)
  | .const _n => ⟨#[], by grind⟩
  | .hole _n => ⟨#[], by grind⟩

@[aesop norm (rule_sets := [DccForceReduce]), grind, dcc_rel]
def points (e : GenericExpr (τ := τ_c)) : Vector (GenericExpr (τ := τ_c)) (point_arity e) :=
  match e with
  | DCC[.] (Dom _x) => ⟨#[], by grind⟩
  | DCC[.] (Dom₂ _x) => ⟨#[], by grind⟩
  | DCC? (Uncoup _x) => ⟨#[], by grind⟩
  | DCC? (Unbang _x) => ⟨#[], by grind⟩
  | DCC[.] ∗ => ⟨#[], by grind⟩
  | DCC[.] ⊤ => ⟨#[], by grind⟩
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
  | DCC? (Dom x) => DCC? (Dom x)
  | DCC? (Dom₂ x) => DCC? (Dom₂ x)
  | DCC? (Uncoup x) => DCC? (Uncoup x)
  | DCC? (Unbang x) => DCC? (Unbang x)
  | DCC? ∗ => .tintro
  | DCC? ⊤ => .top
  | DCC? ⊥ => .bot
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

-- congr_point_arr (h : r e (set_points e ((points e).set p p'))) : point_arity e = (set_points e ((points e).set p p'))

@[grind =, grind! ., dcc_rel]
theorem set_points_self_noop : set_points e e.points = e := by
  induction e
  any_goals (first | grind | aesop)

@[grind =_, grind ., grind! ., dcc_rel]
theorem congr_point_arr {e : GenericExpr τ_c} {p : Fin (point_arity e)} : point_arity e = point_arity (set_points e ((points e).set p p')) := by
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

@[grind =, grind! .]
theorem set_same_point_comp {e x y : GenericExpr τ_c} {p : Fin (point_arity e)} : set_points (set_points e ((points e).set p x)) ((points (set_points e ((points e).set p x))).set (h := by rw [← congr_point_arr]; grind) p y) = set_points e ((points e).set p y) := by
  induction e <;> grind

@[grind, dcc_reduce]
def uncurry' (pre : GenericExpr τ_c)
  (mk : Function.OfArity (GenericExpr τ_c) (GenericExpr τ_c) (branch_arity pre))
  (f  : GenericExpr τ_c → GenericExpr τ_c) := mk.uncurry (fun (i : Fin (branch_arity pre)) => f ((branches pre).get i))

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

@[grind]
def has_at_least_hole_level (lv : ℕ) (e : GenericExpr τ_c) : Bool :=
  match e with
  | DCC? (Dom x) => x.has_at_least_hole_level lv
  | DCC? (Dom₂ x) => x.has_at_least_hole_level lv
  | DCC? (Uncoup x) => x.has_at_least_hole_level lv
  | DCC? (Unbang x) => x.has_at_least_hole_level lv
  | DCC? ∗ => False
  | DCC? ⊤ => False
  | DCC? ⊥ => False
  | DCC? x = y => x.has_at_least_hole_level lv || y.has_at_least_hole_level lv
  | DCC? (Eql B)  => B.has_at_least_hole_level lv
  | DCC? (refl B) => B.has_at_least_hole_level lv
  | DCC? Sort _m => false
  | DCC? (Σ B C) => B.has_at_least_hole_level lv || C.has_at_least_hole_level lv
  | DCC? (`B x) => B.has_at_least_hole_level lv || x.has_at_least_hole_level lv
  | DCC? (,B x y) => B.has_at_least_hole_level lv || x.has_at_least_hole_level lv || y.has_at_least_hole_level lv
  | DCC? (Σ B) => B.has_at_least_hole_level lv
  | DCC? (Id A)      => A.has_at_least_hole_level lv
  | DCC? (Fst B)    => B.has_at_least_hole_level lv
  | DCC? (Snd B)    => B.has_at_least_hole_level lv
  | DCC? (Swap B C)    => B.has_at_least_hole_level lv || C.has_at_least_hole_level lv
  | DCC? (Π B C) => B.has_at_least_hole_level lv || C.has_at_least_hole_level lv
  | DCC? (∘ x y)  => x.has_at_least_hole_level lv || y.has_at_least_hole_level lv
  | DCC? (⟨,⟩B x y)   => B.has_at_least_hole_level lv || x.has_at_least_hole_level lv || y.has_at_least_hole_level lv
  | DCC? (Λ A B x) => A.has_at_least_hole_level lv || B.has_at_least_hole_level lv || x.has_at_least_hole_level lv
  | DCC? (!Λ A B x) => A.has_at_least_hole_level lv || B.has_at_least_hole_level lv || x.has_at_least_hole_level lv
  | DCC? (Eval A B x) => A.has_at_least_hole_level lv || B.has_at_least_hole_level lv || x.has_at_least_hole_level lv
  | DCC? (!x)   => x.has_at_least_hole_level lv
  | DCC? (*x)    => x.has_at_least_hole_level lv
  | DCC? (&x)   => x.has_at_least_hole_level lv
  | DCC? (!<> x)   => x.has_at_least_hole_level lv
  | DCC? ($<> x)   => x.has_at_least_hole_level lv
  | DCC? (f x) => f.has_at_least_hole_level lv || x.has_at_least_hole_level lv
  | .const _n => false
  | .hole n => n ≥ lv

end GenericExpr
