import Dcc.Ast
import Dcc.Aff.Red
import Dcc.Relation

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

inductive Hole where
  | mk   : ℕ → Hole
  | sort : ℕ → Hole
deriving BEq, Repr, DecidableEq

inductive EtaConst.{u} {τ : Type u} where
  | hole  : Hole → EtaConst
  | const : τ    → EtaConst
deriving BEq, DecidableEq, Repr

gen_dsl "DCCη" for (EtaConst (τ := Unit))

instance Hole.instToFormat : Std.ToFormat Hole := ⟨repr⟩
instance EtaConst.instToFormat.{u} {τ : Type u} [Repr τ] : Std.ToFormat (EtaConst (τ := τ)) := ⟨repr⟩

abbrev EtaExpr.{u} (τ : Type u) := GenericExpr (EtaConst (τ := τ))

namespace GenericExpr

@[aesop norm (rule_sets := [DccReduce]), dcc_reduce, grind]
def contains.{u} {τ : Type u} [DecidableEq τ] (e : GenericExpr (τ := τ))
  (to_find : GenericExpr (τ := τ)) : Bool :=
  match e, to_find with
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
  | .const x₁, .const x₂ => if x₁ = x₂ then true else false
  | _, _ => false

@[aesop norm (rule_sets := [DccReduce]), dcc_reduce, grind]
def contains_hole.{u} {τ : Type u} (e : GenericExpr (τ := (@EtaConst τ))) : Bool :=
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


@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def arity.{u} {τ : Type u} (e : GenericExpr (τ := τ)) : ℕ :=
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
  | DCC[.] *<_α>   => 1
  | DCC[.] &(_x)   => 1
  | DCC[.] !<_x>   => 1
  | DCC[.] $<_x>   => 1
  | DCC[.] (f _x) => f.arity - 1
  | .const _n => 0

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def tm_arity.{u} {τ : Type u} (e : GenericExpr (τ := τ)) : ℕ :=
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
  | DCC[.] *<_α>   => 1
  | DCC[.] &(_x)   => 1
  | DCC[.] !<_x>   => 1
  | DCC[.] $<_x>   => 1
  | DCC[.] (f _x) => f.tm_arity - 1
  | .const _n => 0

@[dcc_reduce]
def is_boxed.{u} {τ : Type u} (e : GenericExpr (τ := τ)) : Option (GenericExpr (τ := τ)) :=
  match e with
  | DCC[.] &(x) => .some x
  | _ => .none

@[dcc_reduce]
def is_bang.{u} {τ : Type u} (e : GenericExpr (τ := τ)) : Option (GenericExpr (τ := τ)) :=
  match e with
  | DCC[.] !(x) => .some x
  | _ => .none

@[dcc_reduce]
def is_bang_map.{u} {τ : Type u} (e : GenericExpr τ) : Option (GenericExpr (τ := τ)) :=
  match e with
  | DCC[.] !<f> => .some f
  | _ => .none

@[dcc_reduce]
def is_box_map.{u} {τ : Type u} (e : GenericExpr τ) : Option (GenericExpr (τ := τ)) :=
  match e with
  | DCC[.] $<f> => .some f
  | _  => .none

@[dcc_reduce]
def is_quote.{u} {τ : Type u} (e : GenericExpr τ) : Option ((β x : GenericExpr τ) × PLift (e = (DCC? `(β, x)))) :=
  match e with
  | DCC[.] `(β, x) => .some ⟨β, x, ⟨rfl⟩⟩
  | _ => .none

@[dcc_reduce]
def is_id.{u} {τ : Type u} (e : GenericExpr τ) : Option ((α : GenericExpr τ) × PLift (e = (DCC? Id(α)))) :=
  match e with
  | DCC[.] Id(_α) => .some ⟨_, ⟨rfl⟩⟩
  | _ => .none

@[dcc_reduce]
def is_type.{u} {τ : Type u} (e : GenericExpr τ) : Option ((n : ℕ) × PLift (e = (DCC? Sort n + 1))) :=
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
theorem hole_size_zero.{u} {τ : Type u} : (GenericExpr.const (τ := EtaConst (τ := τ)) (.hole _m)).size = 0 := by
  grind

@[grind =, grind! ., dcc_size]
theorem coup_hole_zero.{u} {τ : Type u} {β : GenericExpr (τ := EtaConst (τ := τ))} : (DCC? ⟦β⟧(hole(m), hole(n))).size = 0 := by
  grind

end GenericExpr
