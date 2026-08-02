import Dcc.Attrs
import Dcc.Ast.Core
import Dcc.Ast.Dsl
import Mathlib.Logic.Function.OfArity
import Mathlib.Data.Fin.Tuple.Curry

namespace GenericExpr

@[grind, dcc_size]
def point_arity (e : GenericExpr (τ := τ_c)) : ℕ :=
  match e with
  | DCC[.] ∗ => 0
  | DCC[.] ⊤ => 0
  | DCC[.] ⊥ => 0
  | DCC[.] _x = _y => 2
  | DCC[.] Eql(_α)  => 1
  | DCC[.] refl(_α) => 1
  | DCC[.] Sort _m => 0
  | DCC[.] Σ(_α, _β) => 2
  | DCC[.] `(_β, _x) => 2
  | DCC[.] ⟦__β⟧(_x, _y) => 3
  | DCC[.] Coup(_β) => 1
  | DCC[.] Id(_α)      => 1
  | DCC[.] Fstc(_α)    => 1
  | DCC[.] Sndc(_α)    => 1
  | DCC[.] Π(_α, _β) => 2
  | DCC[.] (_f ∘' _g) => 2
  | DCC[.] (_f ∘ _g)  => 2
  | DCC[.] (_f ∘∘ _g)  => 2
  | DCC[.] ⟦_β⟧⟨_a, _b⟩   => 3
  | DCC[.] Λ(_α, _β, _x) => 3
  | DCC[.] !Λ(_α, _β, _x) => 3
  | DCC[.] Eval(_α, _β, _x) => 3
  | DCC[.] !(_x)   => 1
  | DCC[.] *(_α)   => 1
  | DCC[.] *<_f>    => 1
  | DCC[.] &(_x)   => 1
  | DCC[.] !<_x>   => 1
  | DCC[.] $<_x>   => 1
  | DCC[.] (_f _x)
  | .const _n => 0

@[grind, dcc_size]
def branch_arity (e : GenericExpr (τ := τ_c)) : ℕ :=
  match e with
  | DCC[.] ∗ => 0
  | DCC[.] ⊤ => 0
  | DCC[.] ⊥ => 0
  | DCC[.] _x = _y => 2
  | DCC[.] Eql(_α)  => 1
  | DCC[.] refl(_α) => 1
  | DCC[.] Sort _m => 0
  | DCC[.] Σ(_α, _β) => 2
  | DCC[.] `(_β, _x) => 2
  | DCC[.] ⟦__β⟧(_x, _y) => 3
  | DCC[.] Coup(_β) => 1
  | DCC[.] Id(_α)      => 1
  | DCC[.] Fstc(_α)    => 1
  | DCC[.] Sndc(_α)    => 1
  | DCC[.] Π(_α, _β) => 2
  | DCC[.] (_f ∘' _g) => 2
  | DCC[.] (_f ∘ _g)  => 2
  | DCC[.] (_f ∘∘ _g)  => 2
  | DCC[.] ⟦_β⟧⟨_a, _b⟩   => 3
  | DCC[.] Λ(_α, _β, _x) => 3
  | DCC[.] !Λ(_α, _β, _x) => 3
  | DCC[.] Eval(_α, _β, _x) => 3
  | DCC[.] !(_x)   => 1
  | DCC[.] *(_α)   => 1
  | DCC[.] *<_f>    => 1
  | DCC[.] &(_x)   => 1
  | DCC[.] !<_x>   => 1
  | DCC[.] $<_x>   => 1
  | DCC[.] (_f _x) => 2
  | .const _n => 0

@[grind]
def branches (e : GenericExpr (τ := τ_c)) : Vector (GenericExpr (τ := τ_c)) (branch_arity e) :=
  match e with
  | DCC[.] ∗ => ⟨#[], by grind⟩
  | DCC[.] ⊤ => ⟨#[], by grind⟩
  | DCC[.] ⊥ => ⟨#[], by grind⟩
  | DCC[.] x = y => ⟨#[x, y], by grind⟩
  | DCC[.] Eql(α)  => ⟨#[α], by grind⟩
  | DCC[.] refl(α) => ⟨#[α], by grind⟩
  | DCC[.] Sort _m => ⟨#[], by grind⟩
  | DCC[.] Σ(α, β) => ⟨#[α, β], by grind⟩
  | DCC[.] `(β, x) => ⟨#[β, x], by grind⟩
  | DCC[.] ⟦β⟧(x, y) => ⟨#[β, x, y], by grind⟩
  | DCC[.] Coup(β) => ⟨#[β], by grind⟩
  | DCC[.] Id(α)      => ⟨#[α], by grind⟩
  | DCC[.] Fstc(α)    => ⟨#[α], by grind⟩
  | DCC[.] Sndc(α)    => ⟨#[α], by grind⟩
  | DCC[.] Π(α, β) => ⟨#[α, β], by grind⟩
  | DCC[.] (f ∘' g) => ⟨#[f, g], by grind⟩
  | DCC[.] (f ∘ g)  => ⟨#[f, g], by grind⟩
  | DCC[.] (f ∘∘ g)  => ⟨#[f, g], by grind⟩
  | DCC[.] ⟦β⟧⟨a, b⟩   => ⟨#[β, a, b], by grind⟩
  | DCC[.] Λ(α, β, x) => ⟨#[α, β, x], by grind⟩
  | DCC[.] !Λ(α, β, x) => ⟨#[α, β, x], by grind⟩
  | DCC[.] Eval(α, β, x) => ⟨#[α, β, x], by grind⟩
  | DCC[.] !(x)   => ⟨#[x], by grind⟩
  | DCC[.] *(α)   => ⟨#[α], by grind⟩
  | DCC[.] *<f>    => ⟨#[f], by grind⟩
  | DCC[.] &(x)   => ⟨#[x], by grind⟩
  | DCC[.] !<x>   => ⟨#[x], by grind⟩
  | DCC[.] $<x>   => ⟨#[x], by grind⟩
  | DCC[.] (f x) => ⟨#[f, x], by grind⟩
  | .const _n => ⟨#[], by grind⟩

/-
How many points there are that index the environment,
determining a resulting term.
-/
@[grind, dcc_size]
def n_indices (e : GenericExpr (τ := τ_c)) : ℕ :=
  match e with
  | DCC[.] ∗ => 0
  | DCC[.] ⊤ => 0
  | DCC[.] ⊥ => 0
  | DCC[.] _x = _y => 0
  | DCC[.] Eql(_α)  => 0
  | DCC[.] refl(_α) => 0
  | DCC[.] Sort _m => 0
  | DCC[.] Σ(_α, _β) => 2
  | DCC[.] `(_β, _x) => 0
  | DCC[.] ⟦__β⟧(_x, _y) => 0
  | DCC[.] Coup(_β) => 0
  | DCC[.] Id(_α)      => 0
  | DCC[.] Fstc(_α)    => 0
  | DCC[.] Sndc(_α)    => 0
  | DCC[.] Π(_α, _β) => 2
  | DCC[.] (_f ∘' _g) => 0
  | DCC[.] (_f ∘ _g)  => 0
  | DCC[.] (_f ∘∘ _g)  => 0
  | DCC[.] ⟦_β⟧⟨_a, _b⟩   => 0
  | DCC[.] Λ(_α, _β, _x) => 0
  | DCC[.] !Λ(_α, _β, _x) => 0
  | DCC[.] Eval(_α, _β, _x) => 0
  | DCC[.] !(_x)   => 0
  | DCC[.] *(_α)   => 0
  | DCC[.] *<_f>    => 1
  | DCC[.] &(_x)   => 0
  | DCC[.] !<_x>   => 1
  | DCC[.] $<_x>   => 1
  | DCC[.] (_f _x)
  | .const _n => 0

@[grind, dcc_size]
def indices (e : GenericExpr (τ := τ_c)) : Vector (GenericExpr (τ := τ_c)) (n_indices e) :=
  match e with
  | DCC[.] ∗ => ⟨#[], by grind⟩
  | DCC[.] ⊤ => ⟨#[], by grind⟩
  | DCC[.] ⊥ => ⟨#[], by grind⟩
  | DCC[.] _x = _y => ⟨#[], by grind⟩
  | DCC[.] Eql(_α)  => ⟨#[], by grind⟩
  | DCC[.] refl(_α) => ⟨#[], by grind⟩
  | DCC[.] Sort _m => ⟨#[], by grind⟩
  | DCC[.] Σ(α, β) => ⟨#[α, β], by grind⟩
  | DCC[.] `(_β, _x) => ⟨#[], by grind⟩
  | DCC[.] ⟦__β⟧(_x, _y) => ⟨#[], by grind⟩
  | DCC[.] Coup(_β) => ⟨#[], by grind⟩
  | DCC[.] Id(_α)      => ⟨#[], by grind⟩
  | DCC[.] Fstc(_α)    => ⟨#[], by grind⟩
  | DCC[.] Sndc(_α)    => ⟨#[], by grind⟩
  | DCC[.] Π(α, β) => ⟨#[α, β], by grind⟩
  | DCC[.] (_f ∘' _g) => ⟨#[], by grind⟩
  | DCC[.] (_f ∘ _g)  => ⟨#[], by grind⟩
  | DCC[.] (_f ∘∘ _g)  => ⟨#[], by grind⟩
  | DCC[.] ⟦_β⟧⟨_a, _b⟩   => ⟨#[], by grind⟩
  | DCC[.] Λ(_α, _β, _x) => ⟨#[], by grind⟩
  | DCC[.] !Λ(_α, _β, _x) => ⟨#[], by grind⟩
  | DCC[.] Eval(_α, _β, _x) => ⟨#[], by grind⟩
  | DCC[.] !(_x)   => ⟨#[], by grind⟩
  | DCC[.] *(_α)   => ⟨#[], by grind⟩
  | DCC[.] *<f>    => ⟨#[f], by grind⟩
  | DCC[.] &(_x)   => ⟨#[], by grind⟩
  | DCC[.] !<x>   => ⟨#[x], by grind⟩
  | DCC[.] $<x>   => ⟨#[x], by grind⟩
  | DCC[.] (_f _x)
  | .const _n => ⟨#[], by grind⟩

@[grind]
def points (e : GenericExpr (τ := τ_c)) : Vector (GenericExpr (τ := τ_c)) (point_arity e) :=
  match e with
  | DCC[.] ∗ => ⟨#[], by grind⟩
  | DCC[.] ⊤ => ⟨#[], by grind⟩
  | DCC[.] ⊥ => ⟨#[], by grind⟩
  | DCC[.] x = y => ⟨#[x, y], by grind⟩
  | DCC[.] Eql(α)  => ⟨#[α], by grind⟩
  | DCC[.] refl(α) => ⟨#[α], by grind⟩
  | DCC[.] Sort _m => ⟨#[], by grind⟩
  | DCC[.] Σ(α, β) => ⟨#[α, β], by grind⟩
  | DCC[.] `(β, x) => ⟨#[β, x], by grind⟩
  | DCC[.] ⟦β⟧(x, y) => ⟨#[β, x, y], by grind⟩
  | DCC[.] Coup(β) => ⟨#[β], by grind⟩
  | DCC[.] Id(α)      => ⟨#[α], by grind⟩
  | DCC[.] Fstc(α)    => ⟨#[α], by grind⟩
  | DCC[.] Sndc(α)    => ⟨#[α], by grind⟩
  | DCC[.] Π(α, β) => ⟨#[α, β], by grind⟩
  | DCC[.] (f ∘' g) => ⟨#[f, g], by grind⟩
  | DCC[.] (f ∘ g)  => ⟨#[f, g], by grind⟩
  | DCC[.] (f ∘∘ g)  => ⟨#[f, g], by grind⟩
  | DCC[.] ⟦β⟧⟨a, b⟩   => ⟨#[β, a, b], by grind⟩
  | DCC[.] Λ(α, β, x) => ⟨#[α, β, x], by grind⟩
  | DCC[.] !Λ(α, β, x) => ⟨#[α, β, x], by grind⟩
  | DCC[.] Eval(α, β, x) => ⟨#[α, β, x], by grind⟩
  | DCC[.] !(x)   => ⟨#[x], by grind⟩
  | DCC[.] *(α)   => ⟨#[α], by grind⟩
  | DCC[.] *<f>    => ⟨#[f], by grind⟩
  | DCC[.] &(x)   => ⟨#[x], by grind⟩
  | DCC[.] !<x>   => ⟨#[x], by grind⟩
  | DCC[.] $<x>   => ⟨#[x], by grind⟩
  | DCC[.] (_f _x) => ⟨#[], by grind⟩
  | .const _n => ⟨#[], by grind⟩

@[grind, dcc_reduce]
def uncurry (pre : GenericExpr τ_c)
  (mk    : Function.OfArity (GenericExpr τ_c) (GenericExpr τ_c) (point_arity pre))
  (f     : GenericExpr τ_c → GenericExpr τ_c) :=
  mk.uncurry (fun (i : Fin (point_arity pre)) => f ((points pre).get i))

@[grind, dcc_reduce]
def map_points (e : GenericExpr (τ := τ_c))
  (fn : GenericExpr τ_c → GenericExpr τ_c) : GenericExpr τ_c :=
  uncurry e (match e with
  | DCC? ∗ => .tintro
  | DCC? ⊤ => .top
  | DCC? ⊥ => .bot
  | DCC? _x = _y => .eq
  | DCC? Eql(_α)  => .eql
  | DCC? refl(_α) => .refl
  | DCC? Sort m => .sort m
  | DCC? Σ(_α, _β) => .sigma
  | DCC? `(_β, _x) => .quot
  | DCC? ⟦_β⟧(_x, _y) => .mkc
  | DCC? Coup(_β) => .coup
  | DCC? Id(_α)      => .id
  | DCC? Fstc(_α)    => .fstc
  | DCC? Sndc(_α)    => .sndc
  | DCC? Π(_α, _β) => .pi
  | DCC? (_f ∘' _g) => .comp'
  | DCC? (_f ∘ _g)  => .comp
  | DCC? (_f ∘∘ _g)  => .comp₂
  | DCC? ⟦_β⟧⟨_a, _b⟩   => .pair
  | DCC? Λ(_α, _β, _x) => .curr
  | DCC? !Λ(_α, _β, _x) => .curr'
  | DCC? Eval(_α, _β, _x) => .eval
  | DCC? !(_x)   => .bang
  | DCC? *(_α)   => .unbox
  | DCC? *<_f>    => .unmap
  | DCC? &(_x)   => .box
  | DCC? !<_x>   => .map
  | DCC? $<_x>   => .fmap
  | DCC? (f x) => .app f x
  | .const n => Function.OfArity.const _ (.const n) _) fn

@[grind, dcc_reduce]
def uncurry' (pre : GenericExpr τ_c)
  (mk : Function.OfArity (GenericExpr τ_c) (GenericExpr τ_c) (branch_arity pre))
  (f  : GenericExpr τ_c → GenericExpr τ_c) := mk.uncurry (fun (i : Fin (branch_arity pre)) => f ((branches pre).get i))

@[grind, dcc_reduce]
def map_branches (e : GenericExpr (τ := τ_c))
  (fn : (GenericExpr τ_c) → GenericExpr τ_c) : GenericExpr τ_c :=
  uncurry' e (match e with
  | DCC? ∗ => .tintro
  | DCC? ⊤ => .top
  | DCC? ⊥ => .bot
  | DCC? _x = _y => .eq
  | DCC? Eql(_α)  => .eql
  | DCC? refl(_α) => .refl
  | DCC? Sort m => .sort m
  | DCC? Σ(_α, _β) => .sigma
  | DCC? `(_β, _x) => .quot
  | DCC? ⟦_β⟧(_x, _y) => .mkc
  | DCC? Coup(_β) => .coup
  | DCC? Id(_α)      => .id
  | DCC? Fstc(_α)    => .fstc
  | DCC? Sndc(_α)    => .sndc
  | DCC? Π(_α, _β) => .pi
  | DCC? (_f ∘' _g) => .comp'
  | DCC? (_f ∘ _g)  => .comp
  | DCC? (_f ∘∘ _g)  => .comp₂
  | DCC? ⟦_β⟧⟨_a, _b⟩   => .pair
  | DCC? Λ(_α, _β, _x) => .curr
  | DCC? !Λ(_α, _β, _x) => .curr'
  | DCC? Eval(_α, _β, _x) => .eval
  | DCC? !(_x)   => .bang
  | DCC? *(_α)   => .unbox
  | DCC? *<_f>    => .unmap
  | DCC? &(_x)   => .box
  | DCC? !<_x>   => .map
  | DCC? $<_x>   => .fmap
  | DCC? (_f _x) => GenericExpr.app
  | .const n => Function.OfArity.const _ (.const n) _) fn

@[grind, dcc_reduce]
def map_indices (e : GenericExpr (τ := τ_c))
  (fn : GenericExpr τ_c → GenericExpr τ_c) : GenericExpr τ_c :=
  uncurry e (match e with
  | DCC? ∗ => .tintro
  | DCC? ⊤ => .top
  | DCC? ⊥ => .bot
  | DCC? _x = _y => .eq
  | DCC? Eql(_α)  => .eql
  | DCC? refl(_α) => .refl
  | DCC? Sort m => .sort m
  | DCC? Σ(_α, _β) => .sigma
  | DCC? `(_β, _x) => .quot
  | DCC? ⟦_β⟧(_x, _y) => .mkc
  | DCC? Coup(_β) => .coup
  | DCC? Id(_α)      => .id
  | DCC? Fstc(_α)    => .fstc
  | DCC? Sndc(_α)    => .sndc
  | DCC? Π(_α, _β) => .pi
  | DCC? (_f ∘' _g) => .comp'
  | DCC? (_f ∘ _g)  => .comp
  | DCC? (_f ∘∘ _g)  => .comp₂
  | DCC? ⟦_β⟧⟨_a, _b⟩   => .pair
  | DCC? Λ(_α, _β, _x) => .curr
  | DCC? !Λ(_α, _β, _x) => .curr'
  | DCC? Eval(_α, _β, _x) => .eval
  | DCC? !(_x)   => .bang
  | DCC? *(_α)   => .unbox
  | DCC? *<_f>    => .unmap
  | DCC? &(_x)   => .box
  | DCC? !<_x>   => .map
  | DCC? $<_x>   => .fmap
  | DCC? (f x) => .app f x
  | .const n => Function.OfArity.const _ (.const n) _) fn

@[grind =]
theorem map_points_id (e : GenericExpr τ) : map_points e _root_.id = e := by
  cases e <;> aesop

@[grind =]
theorem map_branches_id (e : GenericExpr τ) : map_branches e _root_.id = e := by
  cases e <;> aesop

@[grind =]
theorem map_indices_id (e : GenericExpr τ) : map_indices e _root_.id = e := by
  cases e <;> aesop

@[grind ., grind =>]
theorem map_points_ar_eq (heq : map_points e fn = e') : point_arity e = point_arity e' := by
  cases e <;> aesop

@[grind ., grind =>]
theorem map_branches_ar_eq (heq : map_branches e fn = e') : branch_arity e = branch_arity e' := by
  cases e <;> aesop

@[grind ., grind =>]
theorem map_indices_ar_eq (heq : map_indices e fn = e') : n_indices e = n_indices e' := by
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

@[grind =, grind =_, grind! .]
theorem map_branches_map {e : GenericExpr τ} : branches (map_branches e fn) ≍ Vector.map fn (branches e) := by
  cases e <;> (
    focus
    try (
      conv =>
        right
        simp [branches]
        rfl
      simp [map_branches, uncurry', Function.OfArity.uncurry]
      aesop))

@[grind =, grind =_, grind! .]
theorem map_indices_map {e : GenericExpr τ} : indices (map_indices e fn) ≍ Vector.map fn (indices e) := by
  cases e <;> (
    focus
    try (
      conv =>
        right
        simp [indices]
        rfl
      simp [map_indices, uncurry, Function.OfArity.uncurry]
      aesop))

@[grind ., grind =>, grind! .]
theorem map_points_eq {e e' : GenericExpr τ} (heq : map_points e fn = e') : points e' ≍ (points e).map fn := by
  cases e <;> grind

@[grind ., grind =>, grind! .]
theorem map_branches_eq {e e' : GenericExpr τ} (heq : map_branches e fn = e') : branches e' ≍ (branches e).map fn := by
  cases e <;> grind

@[grind ., grind =>, grind! .]
theorem map_indices_eq {e e' : GenericExpr τ} (heq : map_indices e fn = e') : indices e' ≍ (indices e).map fn := by
  cases e <;> grind

end GenericExpr
