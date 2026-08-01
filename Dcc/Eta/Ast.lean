import Dcc.Ast
import Dcc.Aff.Size
import Mathlib.Data.Option.Basic
import Mathlib.Logic.Function.OfArity
import Mathlib.Data.Fin.Tuple.Curry

open Relation (ReflTransGen)

/-
An alternative η-reduction algorithm that does not appeal to semantics.

simple algorithm:
- extend AST with a constructor "hole"
- apply "hole" to expr

Base eta:
  Hole = 0 ... n
  If application reduces to:
  - Hole -> function eta-reduces to Id
  - f' Hole -> function reduces to f'
  - c, where c does not contain Hole -> eta-reduces to `(α, c)

If domain is:
- Coup(β)
  - hole = ⟦β⟧(1, 2)
  Projection eta:
    If application reduces to:
    1. Base eta (hole := 1), η-reduces to f₁
      -> eta-reduces to f₁ ∘' Fstc(β)
    2. Base eta (hole := 2), η-reduces to f₁
      -> eta-reduces to f₁ ∘' Sndc(β)

- Sort | ⊤ | (Π(f_α, f_β) ...) | (f x)
  Use base

- will need extra cases for Π?
-/

section

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

inductive Hole where
  | mk   : ℕ → Hole
  | sort : ℕ → Hole
deriving BEq, Repr, DecidableEq

inductive EtaConst where
  | hole  : Hole → EtaConst
  | const : τ_c  → EtaConst
deriving BEq, DecidableEq, Repr

gen_dsl "DCCη" for (EtaConst (τ := Unit))

instance Hole.instToFormat : Std.ToFormat Hole := ⟨repr⟩
instance EtaConst.instToFormat [Repr τ_c] : Std.ToFormat (@EtaConst τ_c) := ⟨repr⟩

abbrev EtaExpr := GenericExpr (EtaConst (τ_c := τ_c))

namespace GenericExpr

@[grind]
def contains (e : GenericExpr (τ := τ_c))
  (to_find : GenericExpr (τ := τ_c)) : Bool :=
  e = to_find ||
  match e, to_find with
  | .const x₁, x₂ => .const x₁ = x₂
  | DCC[.] ∗, DCC[.] ∗ => true
  | DCC[.] ⊤, DCC[.] ⊤ => true
  | DCC[.] Sort _n, DCC[.] Sort __n => true
  | DCC[.] ⊥, DCC[.] ⊥ => true
  | DCC[.] Π(x, y), to_find
  | DCC[.] (x ∘' y), to_find
  | DCC[.] (x ∘ y), to_find
  | DCC[.] (x ∘∘ y), to_find
  | DCC[.] (x y), to_find
  | DCC[.] x = y, to_find => x.contains to_find || y.contains to_find
  | DCC[.] Fstc(α), to_find
  | DCC[.] Sndc(α), to_find
  | DCC[.] Coup(α), to_find
  | DCC[.] &(α), to_find
  | DCC[.] !<α>, to_find
  | DCC[.] $<α>, to_find
  | DCC[.] !(α), to_find
  | DCC[.] *(α), to_find
  | DCC[.] *<α>, to_find
  | DCC[.] Id(α), to_find
  | DCC[.] Eql(α), to_find
  | DCC[.] refl(α), to_find => α.contains to_find
  | DCC[.] Σ(α, β), to_find => α.contains to_find || β.contains to_find
  | DCC[.] `(β, x), to_find => β.contains to_find || x.contains to_find
  | DCC[.] Eval(β, x, y), to_find
  | DCC[.] !Λ(β, x, y), to_find
  | DCC[.] Λ(β, x, y), to_find
  | DCC[.] ⟦β⟧⟨x, y⟩, to_find
  | DCC[.] ⟦β⟧(x, y), to_find => β.contains to_find || x.contains to_find || y.contains to_find
  | _, _ => false

@[grind =]
theorem contains_refl {e : @GenericExpr τ_c} : contains e e = true := by
  unfold contains
  simp

@[grind]
def contains_hole (e : GenericExpr (τ := (@EtaConst τ))) : Bool :=
    match e with
    | DCC[.] ∗ => False
    | DCC[.] ⊤ => False
    | DCC[.] Sort _n => False
    | DCC[.] ⊥ => False
    | DCC[.] Π(x, y)
    | DCC[.] (x ∘' y)
    | DCC[.] (x ∘ y)
    | DCC[.] (x ∘∘ y)
    | DCC[.] (x y)
    | DCC[.] x = y => x.contains_hole ∨ y.contains_hole
    | DCC[.] Fstc(α)
    | DCC[.] Sndc(α)
    | DCC[.] Coup(α)
    | DCC[.] &(α)
    | DCC[.] !<α>
    | DCC[.] $<α>
    | DCC[.] !(α)
    | DCC[.] *(α)
    | DCC[.] *<α>
    | DCC[.] Id(α)
    | DCC[.] Eql(α)
    | DCC[.] refl(α) => α.contains_hole
    | DCC[.] Σ(α, β) => α.contains_hole ∨ β.contains_hole
    | DCC[.] `(β, x) => β.contains_hole ∨ x.contains_hole
    | DCC[.] Eval(β, x, y)
    | DCC[.] !Λ(β, x, y)
    | DCC[.] Λ(β, x, y)
    | DCC[.] ⟦β⟧⟨x, y⟩
    | DCC[.] ⟦β⟧(x, y) => β.contains_hole ∨ x.contains_hole ∨ y.contains_hole
    | .const (.hole _) => True
    | .const _ => False

@[grind]
def hole_mem_tm (e : GenericExpr (τ := (@EtaConst τ))) : Bool :=
    match e with
    | DCC[.] ∗ => False
    | DCC[.] ⊤ => False
    | DCC[.] Sort _n => False
    | DCC[.] ⊥ => False
    | DCC[.] Π(x, y)
    | DCC[.] (x ∘' y)
    | DCC[.] (x ∘ y)
    | DCC[.] (x ∘∘ y)
    | DCC[.] (x y)
    | DCC[.] x = y => x.hole_mem_tm ∨ y.hole_mem_tm
    | DCC[.] Fstc(α)
    | DCC[.] Sndc(α)
    | DCC[.] Coup(α)
    | DCC[.] &(α)
    | DCC[.] !<α>
    | DCC[.] $<α>
    | DCC[.] !(α)
    | DCC[.] *(α)
    | DCC[.] *<α>
    | DCC[.] Id(α)
    | DCC[.] Eql(α)
    | DCC[.] refl(α) => α.hole_mem_tm
    | DCC[.] Σ(α, β) => α.hole_mem_tm ∨ β.hole_mem_tm
    | DCC[.] `(_β, x) => x.hole_mem_tm
    | DCC[.] Eval(_β, x, y)
    | DCC[.] !Λ(_β, x, y)
    | DCC[.] Λ(_β, x, y)
    | DCC[.] ⟦_β⟧⟨x, y⟩
    | DCC[.] ⟦_β⟧(x, y) => x.hole_mem_tm ∨ y.hole_mem_tm
    | .const (.hole _) => True
    | .const _ => False

/-@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def size.{u} {τ : Type u} (e : GenericExpr (EtaConst (τ := τ))) : ℕ :=
  match e with
  | DCC[.] ∗ => 0
  | DCC[.] ⊤ => 2
  | DCC[.] ⊥ => 2
  | DCC[.] x = y => x.size + y.size
  | DCC[.] Eql(α)  => α.size + 3
  | DCC[.] refl(α) => α.size + 2
  | DCC[.] Sort m => m
  | DCC[.] Σ(α, β) => α.size + β.size + 2
  | DCC[.] `(β, x) => β.size + x.size + 2
  | DCC[.] ⟦_β⟧(x, y) => x.size + y.size
  | DCC[.] Coup(β) => β.size
  | DCC[.] Id(α)      => α.size + 2
  | DCC[.] Fstc(α)    => α.size + 2
  | DCC[.] Sndc(α)    => α.size + 2
  | DCC[.] Π(α, β) => α.size + β.size + 1
  | DCC[.] (f ∘' g) => f.size + f.size + g.size + 2
  | DCC[.] (f ∘ g)  => f.size + f.size + g.size + 2
  | DCC[.] (f ∘∘ g)  => f.size + f.size + g.size + 2
  | DCC[.] ⟦_β⟧⟨a, b⟩   => a.size + a.size + b.size + 2
  | DCC[.] Λ(α, β, x) => α.size + β.size + x.size + 2
  | DCC[.] !Λ(α, β, x) => α.size + β.size + x.size + 2
  | DCC[.] Eval(_α, _β, x) => x.size + 1
  | DCC[.] !(x)   => x.size
  | DCC[.] *(α)   => α.size + 1
  | DCC[.] &(x)   => x.size + x.size + x.size + 2
  | DCC[.] !<x>   => x.size + x.size + x.size + 2
  | DCC[.] $<x>   => x.size + x.size + x.size + 2
  | DCC[.] (f x) => f.size + x.size
  | .const _n => 0-/

@[grind]
def arity (e : GenericExpr (τ := τ_c)) : ℕ :=
  match e with
  | DCC[.] ∗ => 0
  | DCC[.] ⊤ => 0
  | DCC[.] ⊥ => 0
  | DCC[.] _x = _y => 0
  | DCC[.] Eql(_α)  => 2
  | DCC[.] refl(_α) => 2
  | DCC[.] Sort _m => 0
  | DCC[.] Σ(_α, _β) => 1
  | DCC[.] `(_α, `(_β, _x)) => 2
  | DCC[.] `(_β, _x) => 1
  | DCC[.] ⟦__β⟧(_x, _y) => 0
  | DCC[.] Coup(_β) => 0
  | DCC[.] Id((Π(_α, _β) _x_α)) => 2
  | DCC[.] Id(_α)      => 1
  | DCC[.] Fstc(_α)    => 1
  | DCC[.] Sndc(_α)    => 1
  | DCC[.] Π(_α, _β) => 1
  | DCC[.] (f ∘' _g) => f.arity
  | DCC[.] (f ∘ _g)  => f.arity
  | DCC[.] (f ∘∘ _g)  => f.arity
  | DCC[.] ⟦_β⟧⟨_a, _b⟩   => 1
  | DCC[.] Λ(_α, _β, _x) => 2
  | DCC[.] !Λ(_α, _β, _x) => 2
  | DCC[.] Eval(_α, _β, _x) => 1
  | DCC[.] !(_x)   => 1
  | DCC[.] *(_α)   => 1
  | DCC[.] *<f>    => f.arity
  | DCC[.] &(_x)   => 1
  | DCC[.] !<_x>   => 1
  | DCC[.] $<_x>   => 1
  | DCC[.] (f _x) => f.arity - 1
  | .const _n => 0

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

@[grind]
def tm_arity (e : GenericExpr (τ := τ_c)) : ℕ :=
  match e with
  | DCC[.] ∗ => 0
  | DCC[.] ⊤ => 0
  | DCC[.] ⊥ => 0
  | DCC[.] _x = _y => 0
  | DCC[.] Eql(_α)  => 2
  | DCC[.] refl(_α) => 2
  | DCC[.] Sort _m => 0
  | DCC[.] Σ(_α, _β) => 1
  | DCC[.] `(_β, _x) => 1
  | DCC[.] ⟦__β⟧(_x, _y) => 0
  | DCC[.] Coup(_β) => 0
  | DCC[.] Id(_α)      => 1
  | DCC[.] Fstc(_α)    => 1
  | DCC[.] Sndc(_α)    => 1
  | DCC[.] Π(_α, _β) => 0
  | DCC[.] (f ∘' _g) => f.tm_arity
  | DCC[.] (f ∘ _g)  => f.tm_arity
  | DCC[.] (f ∘∘ _g)  => f.tm_arity
  | DCC[.] ⟦_β⟧⟨_a, _b⟩   => 1
  | DCC[.] Λ(_α, _β, _x) => 2
  | DCC[.] !Λ(_α, _β, _x) => 2
  | DCC[.] Eval(_α, _β, _x) => 1
  | DCC[.] !(_x)   => 1
  | DCC[.] *(_α)   => 1
  | DCC[.] *<f>    => f.tm_arity
  | DCC[.] &(_x)   => 1
  | DCC[.] !<_x>   => 1
  | DCC[.] $<_x>   => 1
  | DCC[.] (f _x) => f.tm_arity - 1
  | .const _n => 0

@[dcc_reduce]
def is_boxed (e : GenericExpr (τ := τ_c)) : Option (GenericExpr (τ := τ_c)) :=
  match e with
  | DCC[.] &(x) => .some x
  | _ => .none

@[dcc_reduce, grind]
def is_bang (e : GenericExpr (τ := τ_c)) : Option (GenericExpr (τ := τ_c)) :=
  match e with
  | DCC[.] !(x) => .some x
  | _ => .none

@[dcc_reduce, grind]
def is_bang_map (e : GenericExpr τ_c) : Option (GenericExpr (τ := τ_c)) :=
  match e with
  | DCC[.] !<f> => .some f
  | _ => .none

@[dcc_reduce]
def is_box_map (e : GenericExpr τ_c) : Option (GenericExpr (τ := τ_c)) :=
  match e with
  | DCC[.] $<f> => .some f
  | _  => .none

@[dcc_reduce, grind]
def is_quote (e : GenericExpr τ_c) : Option ((β x : GenericExpr τ_c) × PLift (e = (DCC? `(β, x)))) :=
  match e with
  | DCC[.] `(β, x) => .some ⟨β, x, ⟨rfl⟩⟩
  | _ => .none

@[dcc_reduce]
def is_id (e : GenericExpr τ_c) : Option ((α : GenericExpr τ_c) × PLift (e = (DCC? Id(α)))) :=
  match e with
  | DCC[.] Id(_α) => .some ⟨_, ⟨rfl⟩⟩
  | _ => .none

@[dcc_reduce]
def is_type (e : GenericExpr τ_c) : Option ((n : ℕ) × PLift (e = (DCC? Sort n + 1))) :=
  match e with
  | DCC[.] Sort _n + 1 => .some ⟨_, ⟨rfl⟩⟩
  | _ => .none

scoped syntax num                     : gen_dcc
scoped syntax "hole(" term ")"        : gen_dcc
scoped syntax "hole(" "Sort(" term ")" ")" : gen_dcc

macro_rules
  | `(DCC[$_ty:gen_dcc_loc] $n:num) => `(GenericExpr.const (EtaConst.hole (Hole.mk $n:term)))
  | `(DCC[$_ty:gen_dcc_loc] hole(Sort($tm:term))) => `(GenericExpr.const (EtaConst.hole (Hole.sort $tm:term)))
  | `(DCC[$_ty:gen_dcc_loc] hole($tm:term)) => `(GenericExpr.const (EtaConst.hole (Hole.mk $tm:term)))

@[grind =, grind! ., dcc_size]
theorem hole_size_zero.{v} {τ_c : Type v} : (GenericExpr.const (τ := EtaConst) (.hole (τ_c := τ_c) _m)).size = 0 := by
  grind

@[grind =, grind! ., dcc_size]
theorem coup_hole_zero.{v} {τ : Type v} {β : GenericExpr (τ := EtaConst (τ_c := τ))} : (DCC? ⟦β⟧(hole(m), hole(n))).size = 0 := by
  grind

end GenericExpr

namespace NormExpr
open GenericExpr

@[grind, inline]
abbrev arity (e : NormExpr r) : ℕ := e.raw.arity

@[grind, inline]
abbrev tm_arity (e : NormExpr r) : ℕ := e.raw.tm_arity

end NormExpr

namespace GenericExpr

@[grind]
def eta_to_expr (e : GenericExpr (τ := EtaConst (τ_c := τ_c)))
  (hn_contains : ¬ e.contains_hole) : GenericExpr τ_c :=
  match e with
  | DCC? ∗ => DCC? ∗
  | DCC? ⊤ => DCC? ⊤
  | DCC? ⊥ => DCC? ⊥
  | DCC? x = y =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' => (DCC? x' = y')
  | DCC? Eql(x)  =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? Eql(x'))
  | DCC? refl(x) =>
    match x.eta_to_expr (by simp_all [contains_hole])with
    | x' => (DCC? refl(x'))
  | DCC? Sort _m => (DCC? Sort _m)
  | DCC? Σ(x, y) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' => (DCC? Σ(x', y'))
  | DCC? `(x, y) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' => (DCC? `(x', y'))
  | DCC? ⟦x⟧(y, z) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]), z.eta_to_expr (by simp_all [contains_hole]) with
    | x', y', z' => (DCC? ⟦x'⟧(y', z'))
  | DCC? Coup(x) =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? Coup(x'))
  | DCC? Id(x)      =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? Id(x'))
  | DCC? Fstc(x)    =>
    match x.eta_to_expr (by simp_all [contains_hole])with
    | x' => (DCC? Fstc(x'))
  | DCC? Sndc(x)    =>
    match x.eta_to_expr (by simp_all [contains_hole])with
    | x' => (DCC? Sndc(x'))
  | DCC? Π(x, y) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' =>
      (DCC? Π(x', y'))
  | DCC? (x ∘' y) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' =>
      (DCC? x' ∘' y')
  | DCC? (x ∘ y)  =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' =>
      (DCC? x' ∘ y')
  | DCC? (x ∘∘ y)  =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' =>
      (DCC? x' ∘∘ y')
  | DCC? ⟦x⟧⟨y, z⟩   =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]), z.eta_to_expr (by simp_all [contains_hole]) with
    | x', y', z' =>
      (DCC? ⟦x'⟧⟨y', z'⟩)
  | DCC? Λ(x, y, z) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]), z.eta_to_expr (by simp_all [contains_hole]) with
    | x', y', z' =>
      (DCC? Λ(x', y', z'))
  | DCC? !Λ(x, y, z) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]), z.eta_to_expr (by simp_all [contains_hole]) with
    | x', y', z' =>
      (DCC? !Λ(x', y', z'))
  | DCC? Eval(x, y, z) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]), z.eta_to_expr (by simp_all [contains_hole]) with
    | x', y', z' =>
      (DCC? Eval(x', y', z'))
  | DCC? !(x)   =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? !(x'))
  | DCC? *(x)   =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? *(x'))
  | DCC? *<x>   =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? *<x'>)
  | DCC? &(x)   =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? &(x'))
  | DCC? !<x>   =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? !<x'>)
  | DCC? $<x>   =>
    match x.eta_to_expr (by simp_all [contains_hole]) with
    | x' => (DCC? $<x'>)
  | DCC? (x y) =>
    match x.eta_to_expr (by simp_all [contains_hole]), y.eta_to_expr (by simp_all [contains_hole]) with
    | x', y' =>
      (DCC? (x' y'))
  | .const (.hole _) => by simp_all [contains_hole]
  | .const (.const x) => (.const x)

@[grind]
def expr_to_eta (e : GenericExpr (τ := τ_c)) : (GenericExpr (τ := EtaConst (τ_c := τ_c))) :=
  match e with
  | DCC? ∗ => DCC? ∗
  | DCC? ⊤ => DCC? ⊤
  | DCC? ⊥ => DCC? ⊥
  | DCC? x = y =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' => (DCC? x' = y')
  | DCC? Eql(x)  =>
    match x.expr_to_eta with
    | x' => (DCC? Eql(x'))
  | DCC? refl(x) =>
    match x.expr_to_eta with
    | x' => (DCC? refl(x'))
  | DCC? Sort _m => (DCC? Sort _m)
  | DCC? Σ(x, y) =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? Σ(x', y'))
  | DCC? `(x, y) =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? `(x', y'))
  | DCC? ⟦x⟧(y, z) =>
    match x.expr_to_eta, y.expr_to_eta, z.expr_to_eta with
    | x', y', z' =>
      (DCC? ⟦x'⟧(y', z'))
  | DCC? Coup(x) =>
    match x.expr_to_eta with
    | x' => (DCC? Coup(x'))
  | DCC? Id(x)      =>
    match x.expr_to_eta with
    | x' => (DCC? Id(x'))
  | DCC? Fstc(x)    =>
    match x.expr_to_eta with
    | x' => (DCC? Fstc(x'))
  | DCC? Sndc(x)    =>
    match x.expr_to_eta with
    | x' => (DCC? Sndc(x'))
  | DCC? Π(x, y) =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? Π(x', y'))
  | DCC? (x ∘' y) =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? x' ∘' y')
  | DCC? (x ∘ y)  =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? x' ∘ y')
  | DCC? (x ∘∘ y)  =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? x' ∘∘ y')
  | DCC? ⟦x⟧⟨y, z⟩   =>
    match x.expr_to_eta, y.expr_to_eta, z.expr_to_eta with
    | x', y', z' =>
      (DCC? ⟦x'⟧⟨y', z'⟩)
  | DCC? Λ(x, y, z) =>
    match x.expr_to_eta, y.expr_to_eta, z.expr_to_eta with
    | x', y', z' =>
      (DCC? Λ(x', y', z'))
  | DCC? !Λ(x, y, z) =>
    match x.expr_to_eta, y.expr_to_eta, z.expr_to_eta with
    | x', y', z' =>
      (DCC? !Λ(x', y', z'))
  | DCC? Eval(x, y, z) =>
    match x.expr_to_eta, y.expr_to_eta, z.expr_to_eta with
    | x', y', z' =>
      (DCC? Eval(x', y', z'))
  | DCC? !(x)   =>
    match x.expr_to_eta with
    | x' => (DCC? !(x'))
  | DCC? *(x)   =>
    match x.expr_to_eta with
    | x' => (DCC? *(x'))
  | DCC? *<x>   =>
    match x.expr_to_eta with
    | x' => (DCC? *<x'>)
  | DCC? &(x)   =>
    match x.expr_to_eta with
    | x' => (DCC? &(x'))
  | DCC? !<x>   =>
    match x.expr_to_eta with
    | x' => (DCC? !<x'>)
  | DCC? $<x>   =>
    match x.expr_to_eta with
    | x' => (DCC? $<x'>)
  | DCC? (x y) =>
    match x.expr_to_eta, y.expr_to_eta with
    | x', y' =>
      (DCC? (x' y'))
  | .const x => (.const (.const x))

def to_eta_no_hole {e : GenericExpr τ} : ¬ (expr_to_eta e).contains_hole := by
  induction e <;> (simp_all [expr_to_eta, contains_hole])

def to_eta_left_inv
  {e : GenericExpr τ} : eta_to_expr (expr_to_eta e) to_eta_no_hole = e := by
  unfold expr_to_eta
  split
  any_goals (simp [eta_to_expr])
  any_goals (
    focus
    rename_i x
    have ha := x.to_eta_left_inv
    simp [ha]
    done)
  any_goals (
    focus
    rename_i x y
    have ha := x.to_eta_left_inv
    have hb := y.to_eta_left_inv
    simp [ha, hb]
    done)
  any_goals (
    focus
    rename_i x y z
    have ha := x.to_eta_left_inv
    have hb := y.to_eta_left_inv
    have hc := z.to_eta_left_inv
    simp [ha, hb, hc])

def to_eta_right_inv {e : GenericExpr (@EtaConst τ)} (hn : ¬ e.contains_hole) :
  (expr_to_eta (eta_to_expr e hn)) = e := by
  induction e
  any_goals (simp_all [eta_to_expr, expr_to_eta])
  any_goals (
    focus
    aesop
    done)
  any_goals (grind)
  case const x =>
    unfold contains_hole at hn
    simp at hn
    cases x with
    | hole => simp_all
    | const => simp [eta_to_expr, expr_to_eta]

end GenericExpr
