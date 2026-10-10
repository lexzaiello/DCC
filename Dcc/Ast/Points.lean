import Dcc.Attrs
import Dcc.Ast.Core
import Dcc.Ast.Dsl
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.OfArity
import Mathlib.Data.Fin.Tuple.Curry

open Dsl

namespace GenericExpr

inductive Points : (e : GenericExpr τ) → List (GenericExpr τ) → Type u
  | dup      : Points (DCC? (Dup B x)) [B, x]
  | bot_rec  : Points (DCC? (⊥.Rec motive)) [motive]
  | bool_rec : Points (DCC? (Bool.Rec motive x y)) [motive, x, y]
  | bimap    : Points (DCC? (Map A B x y)) [A, B, x, y]
  | assoc    : Points (DCC? (Assoc A B C)) [A, B, C]
  | ty_hole  : Points (DCC? (? m)) [m]
  | tintro   : Points (DCC? ∗) []
  | bool     : Points (DCC? Bool) []
  | false    : Points (DCC? False) []
  | true     : Points (DCC? True) []
  | top      : Points (DCC? ⊤) []
  | bot      : Points (DCC? ⊥) []
  | sort     : Points (DCC? Sort m) []
  | eq       : Points (DCC? (= A x y)) [A, x, y]
  | eql      : Points (DCC? (Eql B)) [B]
  | refl     : Points (DCC? (refl B)) [B]
  | sigma    : Points (DCC? (Σ B C )) [B, C]
  | quot     : Points (DCC? (`B x)) [B, x]
  | mkc      : Points (DCC? (,B x y)) [B, x, y]
  | id       : Points (DCC? (Id A)) [A]
  | fst      : Points (DCC? (Fst B)) [B]
  | snd      : Points (DCC? (Snd B)) [B]
  | swap     : Points (DCC? (Swap B C)) [B, C]
  | pi       : Points (DCC? (Π B C)) [B, C]
  | comp     : Points (DCC? (∘ f g)) [f, g]
  | pair     : Points (DCC? (⟨,⟩B x y)) [B, x, y]
  | curr     : Points (DCC? (Λ A B x)) [A, B, x]
  | curr'    : Points (DCC? (!Λ A B x)) [A, B, x]
  | eval     : Points (DCC? (Eval A B x)) [A, B, x]
  | bang     : Points (DCC? (! A)) [A]
  | box      : Points (DCC? (& x)) [x]
  | unbox    : Points (DCC? (* A)) [A]
  | map      : Points (DCC? (!<> x)) [x]
  | fmap     : Points (DCC? ($<> x)) [x]
  | app      : Points (DCC? (f x)) []
  | const    : Points (.const _) []
  | hole     : Points (.hole _) []
deriving Repr

def points (e : GenericExpr τ) : Σ xs, Points e xs := by
  cases e <;> exact ⟨_, by constructor⟩

def Points.complete (h : Points e l) : points e = ⟨l, h⟩ := by
  cases h <;> simp [points]

inductive WithPoints : (e : GenericExpr τ) → (points₀ : List (GenericExpr τ)) → (Points e points₀) → (points₁ : List (GenericExpr τ)) → (points₀.length = points₁.length) → (e' : GenericExpr τ) → Type u
  | dup      : WithPoints (DCC? (Dup B x)) [B, x] .dup [B', x'] rfl (DCC? (Dup B' x'))
  | bimap    : WithPoints (DCC? (Map A B x y)) [A, B, x, y] .bimap [A', B', x', y'] rfl (DCC? (Map A' B' x' y'))
  | bot_rec  : WithPoints (DCC? (⊥.Rec motive)) [motive] .bot_rec [motive'] rfl (DCC? (⊥.Rec motive'))
  | bool_rec : WithPoints (DCC? (Bool.Rec motive x y)) [motive, x, y] .bool_rec [motive', x', y'] rfl (DCC? (Bool.Rec motive' x' y'))
  | assoc    : WithPoints (DCC? (Assoc A B C)) [A, B, C] .assoc [A', B', C'] rfl (DCC? (Assoc A' B' C'))
  | ty_hole  : WithPoints (DCC? (? x)) [x] .ty_hole [x'] rfl (DCC? (? x'))
  | tintro   : WithPoints (DCC? ∗) [] .tintro [] rfl (DCC? ∗)
  | bool     : WithPoints (DCC? Bool) [] .bool [] rfl (DCC? Bool)
  | true     : WithPoints (DCC? True) [] .true [] rfl (DCC? True)
  | false    : WithPoints (DCC? False) [] .false [] rfl (DCC? False)
  | top      : WithPoints (DCC? ⊤) [] .top [] rfl (DCC? ⊤)
  | bot      : WithPoints (DCC? ⊥) [] .bot [] rfl (DCC? ⊥)
  | sort     : WithPoints (DCC? Sort m) [] .sort [] rfl (DCC? Sort m)
  | eq       : WithPoints (DCC? (= A x y)) [A, x, y] .eq [A', x', y'] rfl (DCC? (= A' x' y'))
  | eql      : WithPoints (DCC? (Eql B)) [B] .eql [B'] rfl (DCC? (Eql B'))
  | refl     : WithPoints (DCC? (refl B)) [B] .refl [B'] rfl (DCC? (refl B'))
  | sigma    : WithPoints (DCC? (Σ B C)) [B, C] .sigma [B', C'] rfl (DCC? (Σ B' C'))
  | quot     : WithPoints (DCC? (`B x)) [B, x] .quot [B', x'] rfl (DCC? (`B' x'))
  | mkc      : WithPoints (DCC? (,B x y)) [B, x, y] .mkc [B', x', y'] rfl (DCC? (,B' x' y'))
  | id       : WithPoints (DCC? (Id A)) [A] .id [A'] rfl (DCC? (Id A'))
  | fst      : WithPoints (DCC? (Fst B)) [B] .fst [B'] rfl (DCC? (Fst B'))
  | snd      : WithPoints (DCC? (Snd B)) [B] .snd [B'] rfl (DCC? (Snd B'))
  | swap     : WithPoints (DCC? (Swap B C)) [B, C] .swap [B', C'] rfl (DCC? (Swap B' C'))
  | pi       : WithPoints (DCC? (Π B C)) [B, C] .pi [B', C'] rfl (DCC? (Π B' C'))
  | comp     : WithPoints (DCC? (∘ f g)) [f, g] .comp [f', g'] rfl (DCC? (∘ f' g'))
  | pair     : WithPoints (DCC? (⟨,⟩B x y)) [B, x, y] .pair [B', x', y'] rfl (DCC? (⟨,⟩B' x' y'))
  | curr     : WithPoints (DCC? (Λ A B x)) [A, B, x] .curr [A', B', x'] rfl (DCC? (Λ A' B' x'))
  | curr'    : WithPoints (DCC? (!Λ A B x)) [A, B, x] .curr' [A', B', x'] rfl (DCC? (!Λ A' B' x'))
  | eval     : WithPoints (DCC? (Eval A B x)) [A, B, x] .eval [A', B', x'] rfl (DCC? (Eval A' B' x'))
  | bang     : WithPoints (DCC? (! A)) [A] .bang [A'] rfl (DCC? (! A'))
  | box      : WithPoints (DCC? (& x)) [x] .box [x'] rfl (DCC? (& x'))
  | unbox    : WithPoints (DCC? (* A)) [A] .unbox [A'] rfl (DCC? (* A'))
  | fmap     : WithPoints (DCC? ($<> x)) [x] .fmap [x'] rfl (DCC? ($<> x'))
  | map      : WithPoints (DCC? (!<> x)) [x] .map [x'] rfl (DCC? (!<> x'))
  | app      : WithPoints (DCC? (f x)) [] .app [] rfl (DCC? (f x))
  | const    : WithPoints (.const x) [] .const [] rfl (.const x)
  | hole     : WithPoints (.hole x) [] .hole [] rfl (.hole x)
deriving Repr

theorem with_points_id (h : WithPoints e points₀ hp points₀ heq e') : e = e' := by
  cases h <;> rfl

def with_points (e : GenericExpr τ) (points₀ : List (GenericExpr τ)) (hp : Points e points₀) (points₁ : List (GenericExpr τ)) (heq : points₀.length = points₁.length) : Σ e', WithPoints e points₀ hp points₁ heq e' := by
  cases hp
  any_goals (
    focus
    try (
      simp at heq
      match heq, points₁ with
      | _, [_] =>
        exact ⟨_, by constructor⟩)
    done)
  any_goals (
    focus
    try (
      simp at heq
      match heq, points₁ with
      | _, [_, _] =>
        exact ⟨_, by constructor⟩)
    done)
  any_goals (
    focus
    try (
      simp at heq
      match heq, points₁ with
      | _, [_, _, _] =>
        exact ⟨_, by constructor⟩)
    done)
  any_goals (
    focus
    try (
      simp at heq
      match heq, points₁ with
      | _, [_, _, _, _] =>
        exact ⟨_, by constructor⟩)
    done)
  any_goals (
    focus
    try (
      simp at heq
      match points₁ with
      | [] => exact ⟨_, by constructor⟩))

@[aesop default safe forward (rule_sets := [DccSize])]
theorem Points.sizeOf {e : GenericExpr τ} (h : Points e l) (heq : x = l.get n) : sizeOf x < sizeOf e := by
  cases h <;> grind
/-
@[inline, grind, dcc_size]
def point_arity (e : GenericExpr (τ := τ_c)) : ℕ :=
  open Dsl in match e with
  | DCC? (? _x) => 1
  | DCC? (Dup _B _x) => 2
  | DCC? (Bool.Rec _motive _x _y) => 3
  | DCC? (⊥.Rec _motive) => 1
  | DCC? True => 0
  | DCC? False => 0
  | DCC? Bool => 0
  | DCC? (Map _A _B _f _g) => 4
  | DCC? (Assoc _A _B _C) => 3
  | DCC[.] ∗ => 0
  | DCC[.] ⊤ => 0
  | DCC[.] ⊥ => 0
  | DCC[.] (= _A _x _y) => 3
  | DCC[.] (Eql _α)  => 1
  | DCC[.] (refl _α) => 1
  | DCC[.] Sort _m => 0
  | DCC[.] (Σ _α _β) => 2
  | DCC[.] (`_β _x) => 2
  | DCC[.] (,__β _x _y) => 3
  | DCC[.] (Id _α)      => 1
  | DCC[.] (Fst _α _β)    => 2
  | DCC[.] (Swap _B _C) => 2
  | DCC[.] (Snd _α _β)    => 2
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
  | DCC? (Dup B x) => ⟨#[B, x], by simp [point_arity]⟩
  | DCC? (⊥.Rec motive) => ⟨#[motive], by grind⟩
  | DCC? (Bool.Rec motive x y) => ⟨#[motive, x, y], by grind⟩
  | DCC? (Map A B x y) => ⟨#[A, B, x, y], by simp [point_arity]⟩
  | DCC? (Assoc A B C) => ⟨#[A, B, C], by simp [point_arity]⟩
  | DCC[.] ∗ => ⟨#[], by grind⟩
  | DCC? (? m) => ⟨#[m], by grind⟩
  | DCC? Bool | DCC? False | DCC? True | DCC[.] ⊤ => ⟨#[], by grind⟩
  | DCC[.] ⊥ => ⟨#[], by grind⟩
  | DCC[.] (= A x y) => ⟨#[A, x, y], by grind⟩
  | DCC[.] (Eql α)  => ⟨#[α], by grind⟩
  | DCC[.] (refl α) => ⟨#[α], by grind⟩
  | DCC[.] Sort _m => ⟨#[], by grind⟩
  | DCC[.] (Σ α β) => ⟨#[α, β], by grind⟩
  | DCC[.] (`β x) => ⟨#[β, x], by grind⟩
  | DCC[.] (,β x y) => ⟨#[β, x, y], by grind⟩
  | DCC[.] (Id α)      => ⟨#[α], by grind⟩
  | DCC[.] (Fst α β)    => ⟨#[α, β], by grind⟩
  | DCC[.] (Swap B C)    => ⟨#[B, C], by grind⟩
  | DCC[.] (Snd α β)    => ⟨#[α, β], by grind⟩
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
  | DCC? (Dup _B _x) => .dup
  | DCC? (⊥.Rec _motive) => .ind_bot
  | DCC? (Bool.Rec _motive _x _y) => .ind_bool
  | DCC? True => .true
  | DCC? False => .false
  | DCC? Bool => .bool
  | DCC? (? _m) => .hole_ty
  | DCC? (Map _A _B _x _y) => .bimap
  | DCC? (Assoc _A _B _C) => .assoc
  | DCC? ∗ => .tintro
  | DCC? ⊤ => .top
  | DCC? ⊥ => .bot
  | DCC? (= _A _x _y) => .eq
  | DCC? (Eql _α)  => .eql
  | DCC? (refl _α) => .refl
  | DCC? Sort m => .sort m
  | DCC? (Σ _α _β) => .sigma
  | DCC? (`_β _x) => .quot
  | DCC? (,_β _x _y) => .mkc
  | DCC? (Id _α)      => .id
  | DCC? (Fst _α _β)    => .fstc
  | DCC? (Swap _B _C)    => .swap
  | DCC? (Snd _α _β)    => .sndc
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
  | DCC? (Dup B x) =>
    have heq : point_arity (DCC? (Dup B x)) = 2 := by grind
    .dup points'[0] points'[1]
  | DCC? (Map A B x y) =>
    have heq : point_arity (DCC? (Map A B x y)) = 4 := by simp [point_arity]
    .bimap points'[0] points'[1] points'[2] points'[3]
  | DCC? (Assoc A B C) =>
    have heq : point_arity (DCC? (Assoc A B C)) = 3 := by simp [point_arity]
    .assoc points'[0] points'[1] points'[2]
  | DCC? (⊥.Rec motive) =>
    have heq : point_arity (DCC? (⊥.Rec motive)) = 1 := by grind
    .ind_bot points'[0]
  | DCC? ∗ => .tintro
  | DCC? ⊤ => .top
  | DCC? ⊥ => .bot
  | DCC? True => .true
  | DCC? False => .false
  | DCC? Bool => .bool
  | DCC? (? m) =>
    have heq : point_arity (DCC? (? m)) = 1 := by grind
    .hole_ty points'[0]
  | DCC? (Bool.Rec motive x y) =>
    have heq : point_arity (DCC? (Bool.Rec motive x y)) = 3 := by grind
    .ind_bool points'[0] points'[1] points'[2]
  | DCC? (= A x y) =>
    have heq : point_arity (DCC? (= A x y)) = 3 := by grind
    .eq points'[0] points'[1] points'[2]
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
  | DCC? (Id α)      =>
    have heq : point_arity (DCC? (Id α)) = 1 := by grind
    .id points'[0]
  | DCC? (Fst α β)    =>
    have heq : point_arity (DCC? (Fst α β)) = 2 := by grind
    .fstc points'[0] points'[1]
  | DCC? (Swap B C)    =>
    have heq : point_arity (DCC? (Swap B C)) = 2 := by grind
    .swap points'[0] points'[1]
  | DCC? (Snd α β)    =>
    have heq : point_arity (DCC? (Snd α β)) = 2 := by grind
    .sndc points'[0] points'[1]
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

set_option maxHeartbeats 100000000000 in
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
  | DCC? (Dup B x) => max B.max_hole x.max_hole
  | DCC? (Map A B x y) => max A.max_hole (max B.max_hole (max x.max_hole y.max_hole))
  | DCC? (Assoc A B C) => max A.max_hole (max B.max_hole C.max_hole)
  | DCC? (Bool.Rec motive x y) => max motive.max_hole (max x.max_hole y.max_hole)
  | DCC? (⊥.Rec motive) => motive.max_hole
  | DCC? (? m) => m.max_hole
  | DCC? Bool | DCC? False | DCC? True => 0
  | DCC? ∗ => 0
  | DCC? ⊤ => 0
  | DCC? ⊥ => 0
  | DCC? (= A x y) => max A.max_hole (max x.max_hole y.max_hole)
  | DCC? (Eql B)  => B.max_hole
  | DCC? (refl B) => B.max_hole
  | DCC? Sort _m => 0
  | DCC? (Σ B C) => max B.max_hole C.max_hole
  | DCC? (`B x) => max B.max_hole x.max_hole
  | DCC? (,B x y) => max B.max_hole (max x.max_hole y.max_hole)
  | DCC? (Id A)      => A.max_hole
  | DCC? (Fst B C)    => max B.max_hole C.max_hole
  | DCC? (Snd B C)    => max B.max_hole C.max_hole
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
  | DCC? (Dup B x) => min B.min_hole x.min_hole
  | DCC? (Map A B x y) => min A.min_hole (min B.min_hole (min x.min_hole y.min_hole))
  | DCC? (Assoc A B C) => min A.min_hole (min B.min_hole C.min_hole)
  | DCC? (Bool.Rec motive x y) => min motive.min_hole (min x.min_hole y.min_hole)
  | DCC? (⊥.Rec motive) => motive.min_hole
  | DCC? (? m) => m.min_hole
  | DCC? True | DCC? False | DCC? Bool => 0
  | DCC? ∗ => 0
  | DCC? ⊤ => 0
  | DCC? ⊥ => 0
  | DCC? (= A x y) => min A.min_hole (min x.min_hole y.min_hole)
  | DCC? (Eql B)  => B.min_hole
  | DCC? (refl B) => B.min_hole
  | DCC? Sort _m => 0
  | DCC? (Σ B C) => min B.min_hole C.min_hole
  | DCC? (` B x) => min B.min_hole x.min_hole
  | DCC? (,B x y) => min B.min_hole (min x.min_hole y.min_hole)
  | DCC? (Id A)      => A.min_hole
  | DCC? (Fst B C)    => min B.min_hole C.min_hole
  | DCC? (Snd B C)    => min B.min_hole C.min_hole
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

set_option maxHeartbeats 100000000000 in
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

@[grind ., grind →]
theorem sizeOf_lt_point {e : GenericExpr τ_c} {hn : n < point_arity e} : sizeOf ((points e).get ⟨n, hn⟩) < sizeOf e := by
  unfold point_arity at hn
  split at hn
  any_goals (grind)
  any_goals (simp [points, Vector.get])
  any_goals (
    simp at hn
    match n with
    | 0 => simp; grind
    | 1 => simp; grind
    | 2 => simp; grind
    | 3 => simp; grind)

def point_arity₀_cases (heq : point_arity e = 0) : Σ' h, e.cases_point_arity' = .inl h := by
  unfold point_arity at heq
  split at heq
  any_goals (grind)
  any_goals (exact ⟨⟨by simp [point_arity]⟩, rfl⟩)

def point_arity₁_cases (heq : point_arity e = 1) : Σ' h, e.cases_point_arity' = .inr (.inl h) := by
  unfold point_arity at heq
  split at heq
  any_goals (grind)
  any_goals (exact ⟨⟨by simp [point_arity]⟩, rfl⟩)

def point_arity₂_cases (heq : point_arity e = 2) : Σ' h, e.cases_point_arity' = .inr (.inr (.inl h)) := by
  unfold point_arity at heq
  split at heq
  any_goals (grind)
  any_goals (exact ⟨⟨by simp [point_arity]⟩, rfl⟩)

def point_arity₃_cases (heq : point_arity e = 3) : Σ' h, e.cases_point_arity' = .inr (.inr (.inr (.inl h))) := by
  unfold point_arity at heq
  split at heq
  any_goals (grind)
  any_goals (exact ⟨⟨by simp [point_arity]⟩, rfl⟩)

def point_arity₄_cases (heq : point_arity e = 4) : Σ' h, e.cases_point_arity' = .inr (.inr (.inr (.inr h))) := by
  unfold point_arity at heq
  split at heq
  any_goals (grind)
  any_goals (exact ⟨⟨by simp [point_arity]⟩, rfl⟩)

set_option maxHeartbeats 100000000000 in
theorem set_points_assoc (e : GenericExpr τ_c) (hlt₁ : m < point_arity e) (hlt₂ : n < point_arity e) : set_points e ((e.points.set m x).set n y) = set_points (set_points e (e.points.set m x)) ((set_points e (e.points.set m x)).points.set n y (h := by
  have h := congr_point_arr (e := e) (p := ⟨m, by grind⟩) (p' := x)
  rw [← h]
  assumption)) := by
  induction e
  any_goals (grind)

theorem congr_point_arr' : (set_points e ⟨p, h⟩).point_arity = e.point_arity := by
 induction e <;> grind

set_option maxHeartbeats 100000000000 in
theorem set_points_points : (set_points e ⟨p, h⟩).points = ⟨p, h.trans congr_point_arr'.symm⟩ := by
  cases e
  any_goals (simp [set_points]; grind)
-/
end GenericExpr
