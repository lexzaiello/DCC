import Dcc.Ast
import Dcc.Aff.Red
import Dcc.Relation
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
  | DCC[.] `(_β, _x) => 1
  | DCC[.] ⟦__β⟧(_x, _y) => 0
  | DCC[.] Coup(_β) => 0
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

inductive ViewPi : GenericExpr τ_c → Type u
  | pi      : ViewPi (DCC? Π(f_α, f_β))

@[grind, dcc_rel]
def view_pi? (e : GenericExpr τ_c) : Option (ViewPi e) :=
  match e with
  | (DCC? Π(_f_α, _f_β))         => .some .pi
  | _ => .none

@[grind ., grind =_]
theorem ViewPi.complete (h : ViewPi e) : view_pi? e = .some h := by
  cases h
  · simp [view_pi?]

@[grind =, grind =_]
theorem ViewPi.complete_none (h : ViewPi e → False) : view_pi? e = .none := by
  unfold view_pi?
  split <;> (
    first
    | exact (h (by constructor)).elim
    | grind)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_pi?_none_sound (h : view_pi? e = .none) : ViewPi e → False := fun h => by
  simp_all [h.complete]

inductive ViewCoup : GenericExpr τ_c → Type u
  | coup    : ViewCoup (DCC? Coup(β))
  | bang    : ViewCoup (DCC? !(α))

@[grind, dcc_rel]
def view_coup? (e : GenericExpr τ_c) : Option (ViewCoup e) :=
  match e with
  | (DCC? Coup(_β)) => .some .coup
  | (DCC? !(_α))    => .some .bang
  | _ => .none

inductive IsEtaTm : GenericExpr τ_c → Type u
  | eql    : IsEtaTm (DCC? Eql(f_α))
  -- Id(α) x
  | id     : IsEtaTm (DCC? Id(α))
  -- (f ∘ g) x
  | comp   : IsEtaTm f → IsEtaTm (DCC? (f ∘ g))
  | comp'  : IsEtaTm f → IsEtaTm (DCC? (f ∘' g))
  | comp₂  : IsEtaTm f → IsEtaTm (DCC? (f ∘∘ g))
  -- Fstc(..) (x, y) -> x
  | fstc   : IsEtaTm (DCC? Fstc(β))
  | sndc   : IsEtaTm (DCC? Sndc(β))
  -- Σ(f_α, f_β) env -> Coup(...)
  | sigma  : IsEtaTm (DCC? Σ(f_α, f_β))
  -- `(β, x) y
  | quot   : IsEtaTm (DCC? `(β, x))
  -- ⟨f, g⟩ x
  | pair   : IsEtaTm (DCC? ⟦β⟧⟨f, g⟩)
  -- Λ(α, β, x) y z
  | curr   : IsEtaTm (DCC? Λ(α, β, x))
  | curr'  : IsEtaTm (DCC? !Λ(α, β, x))
  | eval   : IsEtaTm (DCC? Eval(α, β, x))
  | map    : IsEtaTm (DCC? !<f>)
  | fmap   : IsEtaTm (DCC? $<f>)
  | unmap  : IsEtaTm (DCC? *<f>)
  | deref  : IsEtaTm (DCC? *(x))
  | top    : IsEtaTm (DCC? ⊤)
  | bot    : IsEtaTm (DCC? ⊥)
  | tintro : IsEtaTm (DCC? ∗)
  | sort   : IsEtaTm (DCC? Sort m)
  | box    : IsEtaTm (DCC? &(x))
  | mk     : IsEtaTm (DCC? ⟦β⟧(x, y))
  | eq     : IsEtaTm (DCC? x = y)
  | refl   : IsEtaTm (DCC? refl(f_α))
  | const  : IsEtaTm (.const _x)
  | app    : IsEtaTm f → IsEtaTm (DCC? (f x))

@[grind]
def is_eta_tm? (e : GenericExpr τ_c) : Option (IsEtaTm e) :=
  match e with
  | (DCC? Eql(f_α)) => .some (by constructor)
  | (DCC? Id(α)) => .some (by constructor)
  | (DCC? f ∘ g) =>
    match f.is_eta_tm? with
    | .some h => .some (by constructor; exact h)
    | .none => .none
  | (DCC? f ∘' g) =>
    match f.is_eta_tm? with
    | .some h => .some (by constructor; exact h)
    | .none => .none
  | (DCC? f ∘∘ g) =>
    match f.is_eta_tm? with
    | .some h => .some (by constructor; exact h)
    | .none => .none
  | (DCC? Fstc(β)) => .some (by constructor)
  | (DCC? Sndc(β)) => .some (by constructor)
  | (DCC? Σ(f_α, f_β)) => .some (by constructor)
  | (DCC? `(β, x)) => .some (by constructor)
  | (DCC? ⟦β⟧⟨f, g⟩) => .some (by constructor)
  | (DCC? ⟦β⟧(x, y)) => .some (by constructor)
  | (DCC? Λ(α, β, x)) => .some (by constructor)
  | (DCC? !Λ(α, β, x)) => .some (by constructor)
  | (DCC? Eval(α, β, x)) => .some (by constructor)
  | (DCC? !<f>) => .some (by constructor)
  | (DCC? $<f>) => .some (by constructor)
  | (DCC? *(f)) => .some (by constructor)
  | (DCC? *<f>) => .some (by constructor)
  | (DCC? &(f)) => .some (by constructor)
  | (DCC? x = y) => .some (by constructor)
  | (DCC? refl(f_α)) => .some (by constructor)
  | (DCC? Sort m) => .some (by constructor)
  | (DCC? ⊤) => .some (by constructor)
  | (DCC? ⊥) => .some (by constructor)
  | (DCC? ∗) => .some (by constructor)
  | (DCC? (f x)) =>
    match f.is_eta_tm? with
    | .some h => .some (by constructor; exact h)
    | .none => .none
  | .const _x => .some (by constructor)
  | .coup _
  | .bang _
  | .pi _ _ => .none

@[grind ., grind =_, aesop safe forward (rule_sets := [DccRel])]
theorem IsEtaTm.complete (h : IsEtaTm e) : is_eta_tm? e = .some h := by
  induction h <;> simp_all [is_eta_tm?]

@[grind =, grind =_]
theorem IsEtaTm.complete_none (h : IsEtaTm e → False) : is_eta_tm? e = .none := by
  induction e
  any_goals (
    focus
    simp [is_eta_tm?]
    try split
    try (
      apply False.elim
      apply h
      constructor
      try assumption)
    try rfl)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem is_eta_tm?_none_sound (h : is_eta_tm? e = .none) : IsEtaTm e → False := fun h => by
  simp_all [h.complete]

def is_eta_tm?_sound (_h : is_eta_tm? e = .some hr) : IsEtaTm e := hr

inductive ViewEta : GenericExpr τ_c → Type u
  | pi_type : ViewEta (DCC? (Π(f_α, f_β) env))
  | pi      : ViewEta (DCC? Π(f_α, f_β))
  | pi_comp : ViewEta (DCC? (Π(f_α, f_β) ∘' g))
  | coup    : ViewEta (DCC? Coup(β))
  | bang    : ViewEta (DCC? !(β))

@[grind, dcc_rel]
def view_eta? (e : GenericExpr τ_c) : Option (ViewEta e) :=
  match e with
  | (DCC? (Π(_f_α, _f_β) _env))  => .some (.pi_type)
  | (DCC? Π(_f_α, _f_β))         => .some .pi
  | (DCC? (Π(_f_α, _f_β) ∘' _g)) => .some .pi_comp
  | (DCC? Coup(_β))              => .some .coup
  | (DCC? !(_β))                 => .some .bang
  | _ => .none

@[grind ., grind =_]
theorem ViewEta.complete (h : ViewEta e) : view_eta? e = .some h := by
  cases h <;> simp [view_eta?]

@[grind =, grind =_]
theorem ViewEta.complete_none (h : ViewEta e → False) : view_eta? e = .none := by
  unfold view_eta?
  split <;> (
    first
    | exact (h (by constructor)).elim
    | grind)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_eta?_none_sound (h : view_eta? e = .none) : ViewEta e → False := fun h => by
  simp_all [h.complete]

theorem IsEtaTm.complete_view_eta (h : IsEtaTm e) : view_eta? e = .none := by
  induction h <;> (simp [view_eta?]; try grind)

@[grind =_, grind .]
theorem ViewCoup.complete (h : ViewCoup e) : view_coup? e = .some h := by
  cases h <;> simp [view_coup?]

@[grind =, grind =_]
theorem ViewCoup.complete_none (h : ViewCoup e → False) : view_coup? e = .none := by
  unfold view_coup?
  split <;> (
    first
    | exact (h (by constructor)).elim
    | grind)

@[aesop safe forward (rule_sets := [DccRel]), dcc_rel]
theorem view_coup?_none_sound (h : view_coup? e = .none) : ViewCoup e → False := fun h => by
  simp_all [h.complete]

open Relation (ReflTransGen)
open GenericExpr (IsNorm decreasing? reduce RedRel reduce_norm reduce_sound norm_unique Complete reduce_complete reduce_complete_fst)

end GenericExpr

namespace NormExpr
open GenericExpr

@[grind, inline]
abbrev arity (e : NormExpr r) : ℕ := e.raw.arity

@[grind, inline]
abbrev tm_arity (e : NormExpr r) : ℕ := e.raw.tm_arity

/-
Note: there will be no apps in the expression
-/

inductive Domain : @NormExpr τ_c RedAff → @NormExpr τ_c RedAff → Type u
  | eql₁     : (hrn : RedAffNorm f_α f_α')
    → Domain f_α' δ
    → Domain ⟨(DCC? Eql(f_α)), fun ⟨_, h⟩ => nomatch h⟩ ⟨(DCC? !(δ.raw)), fun ⟨_, h⟩ =>
    match h with
    | .bang h => δ.is_norm ⟨_, h⟩⟩
  | eql₂     : (hrn : RedAffNorm (DCC? (f_α env)) ⟨τ, hn_τ⟩)
    → Domain ⟨(DCC? (Eql(f_α) &(env))), fun ⟨_, h⟩ => match h with
      | .congrFun h => nomatch h
      | .congrArg h => nomatch h⟩ ⟨(DCC? !(τ)), fun ⟨_, h⟩ => match h with | .bang h => hn_τ ⟨_, h⟩⟩
  | refl₁     : (hrn : RedAffNorm f_α f_α')
    → Domain f_α' δ
    → Domain ⟨(DCC? refl(f_α)), fun ⟨_, h⟩ => nomatch h⟩ ⟨(DCC? !(δ.raw)), fun ⟨_, h⟩ =>
    match h with
    | .bang h => δ.is_norm ⟨_, h⟩⟩
  | refl₂     : (hrn : RedAffNorm (DCC? (f_α env)) ⟨τ, hn_τ⟩)
    → Domain ⟨(DCC? (refl(f_α) &(env))), fun ⟨_, h⟩ => match h with
      | .congrFun h => nomatch h
      | .congrArg h => nomatch h⟩ ⟨(DCC? !(τ)), fun ⟨_, h⟩ => match h with | .bang h => hn_τ ⟨_, h⟩⟩
  | unmap    : (hrn : RedAffNorm f f') → Domain f' α
    → Domain ⟨(DCC? *<f>), fun ⟨_, h⟩ => nomatch h⟩ ⟨(DCC? !(α.raw)), fun ⟨_, h⟩ =>
      match h with
      | .bang h => α.is_norm ⟨_, h⟩⟩
  | unbox    : (hrn : RedAffNorm α ⟨α', hn_α'⟩)
    → Domain ⟨(DCC? *(α)), fun ⟨_, h⟩ => nomatch h⟩ ⟨(DCC? !(α')), fun ⟨_, h⟩ =>
      match h with
      | .bang h => hn_α' ⟨_, h⟩⟩
  | id       : (hrn : RedAffNorm α α') → Domain ⟨(DCC? Id(α)), fun ⟨_, h⟩ => nomatch h⟩ α'
  | fstc     : (hrn : RedAffNorm β ⟨β', hn_β'⟩) → Domain ⟨(DCC? Fstc(β)), fun ⟨_, h⟩ => nomatch h⟩
    ⟨(DCC? Coup(β')), fun ⟨_, h⟩ => match h with
      | .coup h => hn_β' ⟨_, h⟩⟩
  | sndc     : (hrn : RedAffNorm β ⟨β', hn_β'⟩) → Domain ⟨(DCC? Sndc(β)), fun ⟨_, h⟩ => nomatch h⟩
    ⟨(DCC? Coup(β')), fun ⟨_, h⟩ => match h with
      | .coup h => hn_β' ⟨_, h⟩⟩
  | curr₁    : (hrn : RedAffNorm α α') → Domain ⟨(DCC? Λ(α, β, x)), fun ⟨_, h⟩ => nomatch h⟩ α'
  | curr₂    : {y : @NormExpr τ_c RedAff}
    → (hrn : RedAffNorm (DCC? (β y.raw)) τ)
    → Domain ⟨(DCC? (Λ(α, β, x) y.raw)), fun ⟨_, h⟩ =>
      match h with
      | .congrFun h => nomatch h
      | .congrArg h => y.is_norm ⟨_, h⟩⟩ τ
  | curr₁'   : (hrn : RedAffNorm α ⟨α', hn_α'⟩) → Domain ⟨(DCC? !Λ(α, β, x)), fun ⟨_, h⟩ => nomatch h⟩ ⟨DCC? !(α'), fun ⟨_, h⟩ =>
    match h with
    | .bang h => hn_α' ⟨_, h⟩⟩
  | curr₂'   : (hrn : RedAffNorm (DCC? (β y)) τ)
    → Domain ⟨(DCC? (!Λ(α, β, x) &(y))), fun ⟨_, h⟩ =>
      match h with
      | .congrFun h => nomatch h
      | .congrArg h => nomatch h⟩ τ
  | map      : (hrn : RedAffNorm f f') → Domain f' α → Domain ⟨(DCC? !<f>), fun ⟨_, h⟩ => nomatch h⟩ ⟨(DCC? !(α.raw)), fun ⟨_, h⟩ =>
    match h with
    | .bang h => α.is_norm ⟨_, h⟩⟩
  | fmap     : (hrn : RedAffNorm f f') → Domain f' α
    → Domain ⟨(DCC? $<f>), fun ⟨_, h⟩ => nomatch h⟩ ⟨(DCC? !(α.raw)), fun ⟨_, h⟩ =>
    match h with
    | .bang h => α.is_norm ⟨_, h⟩⟩
  | pair     : {M N : GenericExpr τ_c}
    → (hn₁ : IsNorm RedAff M)
    → (hn₂ : IsNorm RedAff N)
    → Domain ⟨M, hn₁⟩ α
    → Domain ⟨(DCC? ⟦β⟧⟨M, N⟩), fun ⟨_, h⟩ =>
    match h with
    | .pairl h => hn₁ ⟨_, h⟩
    | .pairr h => hn₂ ⟨_, h⟩⟩ α
  /-
  TODO: Not sure how to fit Eval in here yet
  | eval     : Val.Domain Val(λ env 2 => f) α → Val.Domain Val(
  | eval     : Apply x y f'
    → Apply f' z e'
    → Apply Val(λ env 1 => Eval(_α, _β, x)) Val(neutral(⟦__β⟧(y, z))) e'-/
  | eval     : (hrn : RedAffNorm β ⟨β', hn_β⟩)
    → Domain ⟨(DCC? Eval(α, β, x)), fun ⟨_, h⟩ => nomatch h⟩ ⟨DCC? Coup(β'), fun ⟨_, h⟩ => match h with | .coup h => hn_β ⟨_, h⟩⟩
  | quot     : (hrn : RedAffNorm β β') → Domain ⟨(DCC? `(β, x)), fun ⟨_, h⟩ => nomatch h⟩ β'
  -- f ∘ g x
  -- again, need to handle second round
  -- can use β-reducer for this.
  | comp'    : (hrn₁ : RedAffNorm g g') → Domain g' α
    → Domain ⟨(DCC? f ∘' g), fun ⟨_, h⟩ => nomatch h⟩ α
  | comp     : (hrn₁ : RedAffNorm g g') → Domain g' α
    → Domain ⟨(DCC? f ∘ g), fun ⟨_, h⟩ => nomatch h⟩ α
  | comp₂    : (hrn₁ : RedAffNorm g g') → Domain g' α
    → Domain ⟨(DCC? f ∘∘ g), fun ⟨_, h⟩ => nomatch h⟩ α
  | pi       : (hn₁ : IsNorm RedAff f_α)
    → (hn₂ : IsNorm RedAff f_β)
    → Domain ⟨f_α, hn₁⟩ δ
    → Domain ⟨(DCC? Π(f_α, f_β)), fun ⟨_, h⟩ => match h with
      | .pil h => hn₁ ⟨_, h⟩
      | .pir h => hn₂ ⟨_, h⟩⟩ δ

inductive Domain₂ : @NormExpr τ_c RedAff → @NormExpr τ_c RedAff → @NormExpr τ_c RedAff → Type u
  | comp'    : (hrn₁ : RedAffNorm f f')
    → (hrn₂ : RedAffNorm g ⟨g', hn_g'⟩)
    → Domain ⟨g', hn_g'⟩ α
    → Domain₂ f' β γ
    → Domain₂ ⟨(DCC? (f ∘' g)), fun ⟨_, h⟩ => nomatch h⟩ α ⟨(DCC? γ.raw ∘' g'), fun ⟨_, h⟩ => nomatch h⟩
  | eql      : (hrn₁ : RedAffNorm f_α ⟨f_α', hn_f_α'⟩) → Domain ⟨f_α', hn_f_α'⟩ ⟨δ, hn_δ⟩
    → Domain₂ ⟨(DCC? Eql(f_α)), fun ⟨_, h⟩ => nomatch h⟩
      ⟨(DCC? !(δ)), fun ⟨_, h⟩ => match h with | .bang h => hn_δ ⟨_, h⟩⟩
      ⟨(DCC? !<f_α'>), fun ⟨_, h⟩ => nomatch h⟩
  | refl      : (hrn₁ : RedAffNorm f_α ⟨f_α', hn_f_α'⟩) → Domain ⟨f_α', hn_f_α'⟩ ⟨δ, hn_δ⟩
    → Domain₂ ⟨(DCC? refl(f_α)), fun ⟨_, h⟩ => nomatch h⟩
      ⟨(DCC? !(δ)), fun ⟨_, h⟩ => match h with | .bang h => hn_δ ⟨_, h⟩⟩
      ⟨(DCC? !<f_α'>), fun ⟨_, h⟩ => nomatch h⟩
  | curr     : (hrn₁ : RedAffNorm α α') → (hrn₂ : RedAffNorm β β')
    → Domain₂ ⟨(DCC? Λ(α, β, x)), fun ⟨_, h⟩ => nomatch h⟩ α' β'
  | curr'    : (hrn₁ : RedAffNorm α ⟨α', hn_α'⟩) → (hrn₂ : RedAffNorm β ⟨β', hn_β'⟩)
    → Domain₂ ⟨(DCC? !Λ(α, β, x)), fun ⟨_, h⟩ => nomatch h⟩
    ⟨DCC? !(α'), fun ⟨_, h⟩ => match h with | .bang h => hn_α' ⟨_, h⟩⟩ ⟨DCC? !<β'>, fun ⟨_, h⟩ => nomatch h⟩

def Domain₂.to_domain (h : Domain₂ f α β) : Domain f α :=
  match h with
  | .comp' _hr₁ hr₂ h_dom₁ _ => .comp' hr₂ h_dom₁
  | .eql hr₁ h_dom => .eql₁ hr₁ h_dom
  | .refl hr₁ h_dom => .refl₁ hr₁ h_dom
  | .curr hr₁ hr₂ => .curr₁ hr₁
  | .curr' hr₁ hr₂ => .curr₁' hr₁

set_option maxHeartbeats 20000000 in
@[grind]
def domain? [DecidableEq τ_c] (e : @NormExpr τ_c RedAff) : Option ((τ : @NormExpr τ_c RedAff) × (Domain e τ)) :=
  match e with
  | ⟨e, hn⟩ =>
    match e with
    | (DCC? Eval(α, β, x)) => .some ⟨_, .eval (aff_sound rfl)⟩
    | (DCC? Eql(f_α)) =>
      match f_α.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .eql₁ (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? (Eql(_f_α) &(_env))) => .some ⟨_, .eql₂ (aff_sound rfl)⟩
    | (DCC? refl(f_α)) =>
      match f_α.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .refl₁ (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? (refl(_f_α) &(_env))) => .some ⟨_, .refl₂ (aff_sound rfl)⟩
    | (DCC? *<f>) =>
      match f.red_aff.domain? with
      | .some ⟨_, h⟩ =>
        .some ⟨_, .unmap (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? *(_α)) => .some ⟨_, .unbox (aff_sound rfl)⟩
    | (DCC? Id(_α)) => .some ⟨_, .id (aff_sound rfl)⟩
    | (DCC? Fstc(_β)) => .some ⟨_, .fstc (aff_sound rfl)⟩
    | (DCC? Sndc(_β)) => .some ⟨_, .sndc (aff_sound rfl)⟩
    | (DCC? Λ(_α, _β, _x)) => .some ⟨_, .curr₁ (aff_sound rfl)⟩
    | (DCC? (Λ(_α, _β, _x) y)) => .some ⟨_, .curr₂
      (y := ⟨y, fun ⟨_, h⟩ => hn ⟨_, .congrArg h⟩⟩) (aff_sound rfl)⟩
    | (DCC? !Λ(_α, _β, _x)) => .some ⟨_, .curr₁' (aff_sound rfl)⟩
    | (DCC? (!Λ(_α, _β, _x) &(_y))) => .some ⟨_, .curr₂' (aff_sound rfl)⟩
    | (DCC? !<f>) =>
      match f.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .map (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? $<f>) =>
      match f.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .fmap (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? ⟦_β⟧⟨M, N⟩) =>
      let M' : @NormExpr τ_c RedAff := ⟨M, (fun ⟨_, h⟩ => hn ⟨_, .pairl h⟩)⟩
      --let N' : @NormExpr τ_c RedAff := ⟨N, (fun ⟨_, h⟩ => hn ⟨_, .pairr h⟩)⟩

      match M'.domain? with
      | .some ⟨α, h⟩ =>
        have hn₁ : IsNorm RedAff M := (fun ⟨_, h⟩ => hn ⟨_, .pairl h⟩)
        have hn₂ : IsNorm RedAff N := (fun ⟨_, h⟩ => hn ⟨_, .pairr h⟩)

        .some ⟨α, .pair hn₁ hn₂ h⟩
      | _ => .none
    | (DCC? `(_β, _x)) => .some ⟨_, .quot (aff_sound rfl)⟩
    | (DCC? _f ∘' g) =>
      match g.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .comp' (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? _f ∘ g) =>
      match g.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .comp (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? _f ∘∘ g) =>
      match g.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .comp₂ (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? Π(f_α, f_β)) =>
      let hn₁ : IsNorm RedAff f_α := fun ⟨_, h⟩ => hn ⟨_, .pil h⟩
      let hn₂ : IsNorm RedAff f_β := fun ⟨_, h⟩ => hn ⟨_, .pir h⟩

      let f_α' : @NormExpr τ_c RedAff := ⟨f_α, hn₁⟩

      match f_α'.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .pi hn₁ hn₂ h⟩
      | _ => .none
    | _ => .none
termination_by e.size
decreasing_by
  all_goals (grind)

def domain₂? (e : @NormExpr τ_c RedAff) : Option ((α β : @NormExpr τ_c RedAff) × (Domain₂ e α β)) :=
  match e with
  | ⟨e, hn⟩ =>
    match e with
    | (DCC? (f ∘' g)) =>
      match g.red_aff.domain?, f.red_aff.domain₂? with
      | .some ⟨_, h₁⟩, .some ⟨_, _, h₂⟩ =>
        .some ⟨_, _, .comp' (aff_sound rfl) (aff_sound rfl) h₁ h₂⟩
      | _, _ => .none
    | (DCC? Eql(f_α)) =>
      match f_α.red_aff.domain? with
      | .some ⟨_, h₁⟩ =>
        .some ⟨_, _, .eql (aff_sound rfl) h₁⟩
      | .none => .none
    | (DCC? refl(f_α)) =>
      match f_α.red_aff.domain? with
      | .some ⟨_, h₁⟩ =>
        .some ⟨_, _, .refl (aff_sound rfl) h₁⟩
      | .none => .none
    | (DCC? Λ(α, β, x)) =>
      .some ⟨_, _, .curr (aff_sound rfl) (aff_sound rfl)⟩
    | (DCC? !Λ(α, β, x)) =>
      .some ⟨_, _, .curr' (aff_sound rfl) (aff_sound rfl)⟩
    | _ => .none
termination_by e.size
decreasing_by
  all_goals (grind)

@[aesop safe forward (rule_sets := [DccReduce]), grind =_, grind ., grind! ., dcc_rel]
theorem Domain.complete (h : Domain e τ) : (domain? (τ_c := τ_c)) e = .some ⟨τ, h⟩ := by
  induction h
  any_goals (
    focus
    try (
      rename_i hr h_dom heq
      have ha := hr.complete
      simp [domain?]
      cases ha
      dcc_simp_all [heq])
    done)
  any_goals (
    focus
    try (
      rename_i hr
      have ha := hr.complete
      simp [domain?]
      cases ha
      dcc_simp_all)
    done)
  all_goals (
    simp [domain?]
    dcc_simp_all)

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
theorem Domain₂.complete
  {e α β : @NormExpr τ_c RedAff} (h : Domain₂ e α β) : e.domain₂? = .some ⟨α, β, h⟩ := by
  induction h with
  | comp' hr₁ hr₂ h_dom h_dom₂ heq =>
    have ha := hr₁.complete
    have hb := hr₂.complete
    simp [domain₂?]
    have hc := h_dom.complete
    --dcc_simp_all
    cases ha; cases hb
    dcc_simp_all
  | refl hr h_domain | eql hr h_domain =>
    have ha := h_domain.complete
    have hb := hr.complete
    simp [domain₂?]
    dcc_simp_all
    cases hb
    dcc_simp_all [ha]
  | curr hrt₁ hrt₂ =>
    have ha := hrt₁.complete
    have hb := hrt₂.complete
    simp [domain₂?]
    dcc_simp_all [ha, hb]
    rw [← ha] at hrt₁
    rw [← hb] at hrt₂
    have hc := hrt₁.eq
    have hd := hrt₂.eq
    cases ha; cases hb
    dcc_simp_all
  | curr' hrt₁ hrt₂ =>
    have ha := hrt₁.complete
    have hb := hrt₂.complete
    simp [domain₂?]
    rw [← ha] at hrt₁
    rw [← hb] at hrt₂
    dcc_simp_all
    have hc := hrt₁.eq
    have hd := hrt₂.eq
    cases ha; cases hb
    dcc_simp_all

@[dcc_force_reduce, aesop safe destruct (rule_sets := [DccRel])]
def Domain.unique {x τ₁ τ₂ : @NormExpr τ_c RedAff} (h₁ : Domain x τ₁) (h₂ : Domain x τ₂) : τ₁ = τ₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all

def Domain.is_norm_aff {e τ : @NormExpr τ_c RedAff} (_h : Domain (τ_c := τ_c) e τ) : IsNorm RedAff τ.raw := τ.is_norm

def Domain₂.is_norm_aff (_h : Domain₂ e α β) : IsNorm RedAff α.raw ∧ IsNorm RedAff β.raw := ⟨α.is_norm, β.is_norm⟩

@[dcc_force_reduce, aesop safe destruct (rule_sets := [DccRel])]
def Domain₂.unique {f τ₁a τ₁b τ₂a τ₂b : @NormExpr τ_c RedAff} (h₁ : Domain₂ f τ₁a τ₁b) (h₂ : Domain₂ f τ₂a τ₂b) : τ₁a = τ₂a ∧ τ₁b = τ₂b := by
  have ha := h₁.complete
  have hb := h₂.complete
  grind

@[dcc_size]
def Domain.size_pos (h : Domain f τ) : 0 < f.size := by
  induction h <;> grind

end NormExpr

open NormExpr in
open GenericExpr in
@[dcc_force_reduce, dcc_force_aff]
instance Domain.instRedRel : GenericExpr.RedRel.{u, u + 1} (α := @NormExpr τ_c RedAff) (Domain (τ_c := τ_c)) size where
  run := fun x => match domain? x with
    | .some ⟨_, h⟩ => .some ⟨_, ⟨h⟩⟩
    | .none => .none
  decreasing := fun h => by
    induction h
    any_goals (
      focus
      try (
        rename_i hr h_dom hlt
        have ha := h_dom.complete
        have hb := hr.decreasing?
        grind)
      done)
    any_goals (
      focus
      try (
        rename_i hr h_dom hlt
        have ha := h_dom.complete
        have hb := hr.decreasing?
        dcc_simp_all [NormExpr.size]
        omega)
      done)
    any_goals (
      focus
      try (
        rename_i hn hr
        have ha := hr.complete
        have hb := hr.decreasing?
        dcc_simp_all [NormExpr.size]
        first | grind)
      done)
    any_goals (grind)

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

namespace RedAff

def cast_red_eta {A B : GenericExpr τ_c} (hr : RedAff A B)
  : RedAff A.expr_to_eta B.expr_to_eta := by
  induction hr <;> (simp_all [expr_to_eta]; constructor <;> simp_all)

def tail_no_hole (hr : RedAff A B) (hn : ¬ A.contains_hole) : ¬ B.contains_hole := by
  induction hr <;> grind

def reflect_eta {A B : GenericExpr (@EtaConst τ_c)} (hr : RedAff A B)
  (hn : ¬ A.contains_hole) : RedAff (A.eta_to_expr hn) (B.eta_to_expr (tail_no_hole hr hn)) := by
  induction hr <;> (
    focus
    rename_i ih
    simp [eta_to_expr]
    first
    | (constructor; exact (ih (by simp_all [contains_hole])))
    | (constructor))

end RedAff

namespace IsNorm

def to_eta {e : GenericExpr τ_c} (hn : GenericExpr.IsNorm RedAff e) : GenericExpr.IsNorm GenericExpr.RedAff
  (e.expr_to_eta (τ_c := τ_c)) := fun ⟨_, h⟩ =>
  hn ⟨_, to_eta_left_inv ▸ (h.reflect_eta GenericExpr.to_eta_no_hole)⟩

--def from_eta₀

def from_eta {e : GenericExpr (@EtaConst τ_c)} (hn₁ : GenericExpr.IsNorm RedAff e) (hn₂ : ¬ e.contains_hole) : GenericExpr.IsNorm GenericExpr.RedAff
  (e.eta_to_expr hn₂) := fun ⟨_, h⟩ =>
  hn₁ ⟨_, to_eta_right_inv hn₂ ▸ h.cast_red_eta⟩

end IsNorm

end GenericExpr

class Pure.Injective.{v, s} (f : Type v → Type s) extends Pure f where
  inj {α : Type v} : Function.Injective (toPure.pure (α := α))

instance : Pure.Injective Option where
  inj {α} := Option.some_injective α

instance : Pure.Injective Id where
  inj {α} := by simp [Id, pure, Function.Injective]

open Monad in
class EtaRel.{v, s, t} {α : Type v} {β : Type s} (r : α → β → Type t)
  {m : (Type (max s t) → Type (max s t))} [hM : Monad m]
  [Pure.Injective m] where
  run           : ∀ (A : α), m ((B : β) × (r A B))
  complete      : ∀ (h : r A B), run A = (pure ⟨B, h⟩)
  sound         : (run A = pure ⟨B, h⟩) → r A B := fun (_heq : run A = pure ⟨B, h⟩) => h
  unique        : ∀ {A : α} {B C : β} (_hr₁ : r A B) (_hr₂ : r A C), B = C := fun hr₁ hr₂ => by
    have h₁ := complete hr₁
    have h₂ := complete hr₂
    rw [h₁] at h₂
    have h := Pure.Injective.inj h₂
    simp_all
  unique'       : ∀ {A : α} {B C : β} (_hrt₁ : r A B) {_hr₂ : r A C}, B = C := unique

namespace GenericExpr

class NormEtaRel.{t} (r : GenericExpr τ_c → GenericExpr τ_c → Type t)
  {m : Type (max u t) → Type (max u t)} [hM : Monad m] [Pure.Injective m]
  extends EtaRel r (m := m) where
  is_norm_aff   : IsNorm RedAff A → r A B → IsNorm RedAff B

open Monad in
class FallibleEtaRel.{v, t} {α : Type v} (r : α → α → Type t)
  {m : Type (max v t) → Type (max v t)} [_hM : AlternativeMonad m] [Pure.Injective m] extends EtaRel r (m := m) where
  none          : ∀ (_h : run A = failure) (_hr : r A B), False
  none_complete : (∀ {B : α}, r A B → False)  → run A = failure

def is_norm_aff {r : GenericExpr τ_c → GenericExpr τ_c → Type u}
  {m : Type u → Type u} [Monad m ] [Pure.Injective m]
  [NormEtaRel (τ_c := τ_c) r (m := m)] : (IsNorm RedAff A) → (r A B) → IsNorm RedAff B := NormEtaRel.is_norm_aff (m := m)

attribute [grind =_, grind ., grind! ., aesop safe apply (rule_sets := [DccRel])] EtaRel.complete
attribute [grind, aesop norm (rule_sets := [DccRel])] EtaRel.run
attribute [grind, aesop safe apply (rule_sets := [DccRel])] EtaRel.sound
attribute [aesop safe apply (rule_sets := [DccRel])] FallibleEtaRel.none
attribute [grind =, aesop safe apply (rule_sets := [DccRel])] FallibleEtaRel.none_complete
attribute [dcc_rel] NormEtaRel.is_norm_aff

@[grind, aesop safe apply (rule_sets := [DccRel])]
def eta_none_elim.{v} {r : GenericExpr τ_c → GenericExpr τ_c → Type u} {m : Type u → Type u} [AlternativeMonad m]
  [Pure.Injective m] [hE : FallibleEtaRel r (m := m)] (h : hE.run A =  failure) (hr : r A B) {C : Sort v} : C :=
  False.elim (hE.none h hr)

open Monad in
class OptionEtaRel.{v, t} {α : Type v} (r : α → α → Type t)
  : Type (max v t) extends (FallibleEtaRel r (m := Option)) where
  none          : ∀ {A B : α} (_h : run A = failure) (_hr : r A B), False := fun heq hr => by
    simp_all [complete hr, failure, pure]
  none_complete := fun hn => by
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, h⟩
    have heq := complete h
    simp_all
    exact hn h
  unique        : ∀ {A B C : α} (_hr₁ : r A B) (_hr₂ : r A C), B = C := fun hr₁ hr₂ => by
    have h₁ := complete hr₁
    have h₂ := complete hr₂
    simp_all
  unique'       : ∀ {A B C : α} (_hrt₁ : r A B) {_hr₂ : r A C}, B = C := unique

class EtaNormRel (r : GenericExpr τ_c → GenericExpr τ_c → Type u)
  : Type u extends (EtaRel r (m := Option)) where

attribute [dcc_rel] EtaRel.unique
attribute [dcc_rel, aesop safe forward (rule_sets := [DccRel])] EtaRel.unique'

end GenericExpr

open GenericExpr in
open NormExpr in
instance Domain.instEtaRel : (EtaRel (β := @NormExpr τ_c RedAff) Domain (m := Option)) where
  run      := domain?
  complete := Domain.complete

open GenericExpr in
open NormExpr in
instance Domain.instFallibleEtaRel : (FallibleEtaRel (Domain (τ_c := τ_c)) (m := Option)) where
  none     := fun heq hr => by
    have h := hr.complete
    simp_all
    grind
  none_complete := fun h => by
    simp [failure]
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, hr⟩
    exact (h hr).elim

open GenericExpr in
open NormExpr in
instance Domain.instOptionEtaRel : OptionEtaRel (Domain (τ_c := τ_c)) where

end
