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

inductive ViewPi.{u} {τ_c : Type u} : GenericExpr τ_c → Type u
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

inductive ViewCoup.{u} {τ_c : Type u} : GenericExpr τ_c → Type u
  | coup    : ViewCoup (DCC? Coup(β))
  | bang    : ViewCoup (DCC? !(Coup(β)))

@[grind, dcc_rel]
def view_coup? (e : GenericExpr τ_c) : Option (ViewCoup e) :=
  match e with
  | (DCC? Coup(_β))    => .some .coup
  | (DCC? !(Coup(_β))) => .some .bang
  | _ => .none

inductive IsEtaTm.{u} {τ_c : Type u} : GenericExpr τ_c → Type u
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

@[grind, aesop norm (rule_sets := [DccForceReduce])]
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

inductive ViewEta.{u} {τ_c : Type u} : GenericExpr τ_c → Type u
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

inductive Domain.{u} {τ_c : Type u} : GenericExpr τ_c → GenericExpr τ_c → Type u
  | eql₁     : Domain f_α δ → RedAffReflTrans δ δ' → IsNorm RedAff δ' → (DCC? Eql(f_α)).Domain (DCC? !(δ'))
  | eql₂     : RedAffReflTrans (DCC? (f_α &(env))) τ
    → IsNorm RedAff τ
    → Domain (DCC? (Eql(f_α) &(env))) τ
  | refl₁    : Domain f_α δ → RedAffReflTrans δ δ' → IsNorm RedAff δ' → (DCC? refl(f_α)).Domain (DCC? !(δ'))
  | refl₂    : RedAffReflTrans (DCC? (f_α &(env))) τ
    → IsNorm RedAff τ
    → Domain (DCC? (refl(f_α) &(env))) τ
  | unmap    : Domain f α → RedAffReflTrans α α' → IsNorm RedAff α' → Domain (DCC? *<f>) (DCC? !(α'))
  | unbox    : RedAffReflTrans α α' → IsNorm RedAff α' → Domain (DCC? *(α)) (DCC? !(α'))
  | id       : RedAffReflTrans α α' → IsNorm RedAff α' → Domain (DCC? Id(α)) α'
  | fstc     : RedAffReflTrans β β' → IsNorm RedAff β' → Domain (DCC? Fstc(β)) (DCC? Coup(β'))
  | sndc     : RedAffReflTrans β β' → IsNorm RedAff β' → Domain (DCC? Sndc(β)) (DCC? Coup(β'))
  | curr₁    : RedAffReflTrans α α' → IsNorm RedAff α' → Domain (DCC? Λ(α, β, x)) α'
  | curr₂    : RedAffReflTrans (DCC? (β y)) τ
    → IsNorm RedAff τ
    → Domain (DCC? (Λ(α, β, x) y)) τ
  | curr₁'   : RedAffReflTrans α α' → IsNorm RedAff α' → Domain (DCC? !Λ(α, β, x)) (DCC? !(α'))
  | curr₂'   : ReflTransGen RedAff (DCC? (β y)) τ
  → IsNorm RedAff τ
  → Domain (DCC? (!Λ(α, β, x) &(y))) (DCC? !(τ))
  | map      : RedAffReflTrans α α' → IsNorm RedAff α' → Domain f α → Domain (DCC? !<f>) (DCC? !(α'))
  | fmap     : RedAffReflTrans α α' → IsNorm RedAff α' → Domain f α → Domain (DCC? $<f>) (DCC? !(α'))
  | pair     : RedAffReflTrans α α' → IsNorm RedAff α' → Domain M α → Domain (DCC? ⟦β⟧⟨M, N⟩) α'
  /-
  TODO: Not sure how to fit Eval in here yet
  | eval     : Val.Domain Val(λ env 2 => f) α → Val.Domain Val(
  | eval     : Apply x y f'
    → Apply f' z e'
    → Apply Val(λ env 1 => Eval(_α, _β, x)) Val(neutral(⟦__β⟧(y, z))) e'-/
  | quot     : RedAffReflTrans β β' → IsNorm RedAff β' → Domain (DCC? `(β, x)) β'
  -- f ∘ g x
  -- again, need to handle second round
  -- can use β-reducer for this.
  | comp'    : Domain g α   → RedAffReflTrans α α' → IsNorm RedAff α' → Domain (DCC? f ∘' g) α'
  | comp     : Domain g α   → RedAffReflTrans α α' → IsNorm RedAff α' → Domain (DCC? f ∘ g) α'
  | comp₂    : Domain g α   → RedAffReflTrans α α' → IsNorm RedAff α' → Domain (DCC? f ∘∘ g) α'
  | pi       : Domain f_α δ → Domain (DCC? Π(f_α, f_β)) δ

inductive Domain₂.{u} {τ_c : Type u} : GenericExpr τ_c → GenericExpr τ_c → GenericExpr τ_c → Type u
  | comp'    : Domain g α → Domain₂ f β γ → Domain₂ (DCC? (f ∘' g)) α (DCC? γ ∘' g)
  | eql      : Domain f_α δ → (DCC? Eql(f_α)).Domain₂ δ f_α
  | refl     : Domain f_α δ → (DCC? refl(f_α)).Domain₂ δ f_α
  | curr     : Domain₂ (DCC? Λ(α, β, x)) α β
  | curr'    : Domain₂ (DCC? !Λ(α, β, x)) (DCC? !(α)) (DCC? !<β>)

@[dcc_force_reduce, dcc_force_aff]
def domain?.{u} {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr τ_c) : Option ((τ : GenericExpr τ_c) × (PULift.{u + 2, u + 1} (Domain e τ))) :=
  match e with
  | (DCC? Eql(f_α)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.eql₁ h (reduce_sound rfl) (reduce_norm rfl)⟩⟩
    | _ => .none
  | (DCC? (Eql(_f_α) &(_env))) => .some ⟨_, ⟨.eql₂ (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? refl(f_α)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.refl₁ h (reduce_sound rfl) (reduce_norm rfl)⟩⟩
    | _ => .none
  | (DCC? (refl(_f_α) &(_env))) => .some ⟨_, ⟨.refl₂ (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? *<f>) =>
    match f.domain? with
    | .some ⟨_, ⟨h⟩⟩ =>
      .some ⟨_, ⟨.unmap h (reduce_sound rfl) (reduce_norm rfl)⟩⟩
    | _ => .none
  | (DCC? *(_α)) => .some ⟨_, ⟨.unbox (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? Id(_α)) => .some ⟨_, ⟨.id (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? Fstc(_β)) => .some ⟨_, ⟨.fstc (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? Sndc(_β)) => .some ⟨_, ⟨.sndc (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? Λ(_α, _β, _x)) => .some ⟨_, ⟨.curr₁ (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? (Λ(_α, _β, _x) _y)) => .some ⟨_, ⟨.curr₂ (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? !Λ(_α, _β, _x)) => .some ⟨_, ⟨.curr₁' (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? (!Λ(_α, _β, _x) &(_y))) => .some ⟨_, ⟨.curr₂' (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? !<f>) =>
    match f.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.map (reduce_sound rfl) (reduce_norm rfl) h⟩⟩
    | _ => .none
  | (DCC? $<f>) =>
    match f.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.fmap (reduce_sound rfl) (reduce_norm rfl) h⟩⟩
    | _ => .none
  | (DCC? ⟦_β⟧⟨M, _N⟩) =>
    match M.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pair (reduce_sound rfl) (reduce_norm rfl) h⟩⟩
    | _ => .none
  | (DCC? `(_β, _x)) => .some ⟨_, ⟨.quot (reduce_sound rfl) (reduce_norm rfl)⟩⟩
  | (DCC? _f ∘' g) =>
    match g.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp' h (reduce_sound rfl) (reduce_norm rfl)⟩⟩
    | _ => .none
  | (DCC? _f ∘ g) =>
    match g.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp h (reduce_sound rfl) (reduce_norm rfl)⟩⟩
    | _ => .none
  | (DCC? _f ∘∘ g) =>
    match g.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.comp₂ h (reduce_sound rfl) (reduce_norm rfl)⟩⟩
    | _ => .none
  | (DCC? Π(f_α, _f_β)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.pi h⟩⟩
    | _ => .none
  | _ => .none

def domain₂?.{u} {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr τ_c) : Option ((α β : GenericExpr τ_c) × (PULift.{u + 2, u + 1} (Domain₂ e α β))) :=
  match e with
  | DCC? f ∘' g =>
    match g.domain?, f.domain₂? with
    | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, _, ⟨h₂⟩⟩ =>
      .some ⟨_, _, ⟨.comp' h₁ h₂⟩⟩
    | _, _ => .none
  | (DCC? Eql(f_α)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, _, ⟨.eql h⟩⟩
    | _ => .none
  | (DCC? refl(f_α)) =>
    match f_α.domain? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, _, ⟨.refl h⟩⟩
    | _ => .none
  | (DCC? Λ(_α, _β, _x)) => .some ⟨_, _, ⟨.curr⟩⟩
  | (DCC? !Λ(_α, _β, _x)) => .some ⟨_, _, ⟨.curr'⟩⟩
  | _ => none

@[aesop safe forward (rule_sets := [DccReduce]), grind =_, grind ., grind! .]
theorem Domain.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {e τ : GenericExpr τ_c} (h : Domain e τ) : (domain? (τ_c := τ_c)) e = .some ⟨τ, ⟨h⟩⟩ := by
  induction h
  any_goals (
    focus
    dsimp [domain?]
    aesop
    done)
  any_goals (
    rename_i h₁ h₂
    dsimp [domain?]
    have h := reduce_complete (by assumption) (by assumption)
    simp_all
    grind)

@[aesop safe forward (rule_sets := [DccReduce])]
theorem Domain₂.complete.{u} {τ_c : Type u} [DecidableEq τ_c]
  {e α β : GenericExpr τ_c} (h : Domain₂ e α β) : e.domain₂? = .some ⟨α, β, ⟨h⟩⟩ := by
  induction h with
  | comp' h₁ h₂ ih => simp [domain₂?, ih, h₁.complete]
  | refl h_domain | eql h_domain =>
    have h := h_domain.complete
    simp [domain₂?, h]
  | curr | curr' =>
    simp [domain₂?]

@[dcc_force_reduce, dcc_force_aff]
instance Domain.instRedRel.{u} {τ_c : Type u} [DecidableEq τ_c] : GenericExpr.RedRel.{u, u + 1} (α := GenericExpr τ_c) (Domain (τ_c := τ_c)) size where
  run := domain? (τ_c := τ_c)

theorem Domain.deterministic.{u} {τ_c : Type u} {x τ₁ τ₂ : GenericExpr τ_c} (h₁ : Domain (τ_c := τ_c) x τ₁) (h₂ : Domain (τ_c := τ_c) x τ₂) : τ₁ = τ₂ := by
  induction h₁ generalizing τ₂
  any_goals (
    focus
    cases h₂
    aesop
    done)
  any_goals (
    focus
    cases h₂
    rename_i h₁ h₂ h₃ h₄
    have h := norm_unique h₁ h₂ h₄ h₃
    aesop)
  case curr₂' =>
    cases h₂
    rename_i h₁ h₂ _ h₃ h₄
    have h := norm_unique h₁ h₂ h₄ h₃
    aesop
  case eql₁ h_dom hrt₁ hn₁ ih h_dom₂ | refl₁ h_dom hrt₁ hn₁ ih h_dom₂ =>
    cases h₂
    have h := h_dom₂ (by assumption)
    simp_all
    have h := norm_unique hn₁ (by assumption) (by assumption) (by assumption)
    simp_all
  any_goals (
    rename_i h_dom₁ hrt₁ hn₁ ih
    focus
    try (
      cases h₂
      · rename_i hrt₂ hn₂ h_dom₂
        have h := ih (by assumption)
        simp_all
        have h := norm_unique hrt₁ hn₁ hrt₂ hn₂
        simp_all)
    done)
  any_goals (
    focus
    try (
      rename_i hrt₁ hn₁
      cases h₂
      · rename_i hn₂ hrt₂
        have h := norm_unique hrt₁ hn₁ hrt₂ hn₂
        simp_all)
    done)
  any_goals (
    focus
    try (
      rename_i hrt₁ hn₁ h_dom₁ ih
      cases h₂
      rename_i hrt₂ hn₂ h_dom₂
      have ha := ih h_dom₂
      simp_all
      have hb := norm_unique hrt₁ hn₁ hrt₂ hn₂
      simp_all)
    done)
  case pair hrt₁ hn₁ h_dom₁ ih =>
    cases h₂
    case pair h_dom₂ hrt₂ hn₂ =>
      have h := ih h_dom₂
      simp_all
      have h := norm_unique hrt₁ hn₁ hrt₂ hn₂
      simp_all
  any_goals (
    focus
    try(
      rename_i h_dom₁ hrt₁ hn₁ ih
      cases h₂
      · rename_i h_dom₂ hrt₂ hn₂
        have h := ih h_dom₂
        simp_all
        exact norm_unique hrt₁ hn₁ hrt₂ hn₂))

theorem Domain.is_norm_aff (h : Domain e τ) : IsNorm RedAff τ := by
  induction h
  any_goals (
    intro ⟨_, h⟩
    cases h
    grind)
  any_goals (grind)

@[grind]
def eta_to_expr.{u} {τ_c : Type u} (e : GenericExpr (τ := EtaConst (τ := τ_c)))
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
def expr_to_eta.{u} {τ_c : Type u} (e : GenericExpr (τ := τ_c)) : (GenericExpr (τ := EtaConst (τ := τ_c))) :=
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

def to_eta_no_hole.{u} {τ : Type u} {e : GenericExpr τ} : ¬ (expr_to_eta e).contains_hole := by
  induction e <;> (simp_all [expr_to_eta, contains_hole])

def to_eta_left_inv.{u} {τ : Type u}
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

def to_eta_right_inv.{u} {τ : Type u} {e : GenericExpr (@EtaConst τ)} (hn : ¬ e.contains_hole) :
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

def cast_red_eta.{u} {τ_c : Type u} {A B : GenericExpr τ_c} (hr : RedAff A B)
  : RedAff A.expr_to_eta B.expr_to_eta := by
  induction hr <;> (simp_all [expr_to_eta]; constructor <;> simp_all)

def tail_no_hole (hr : RedAff A B) (hn : ¬ A.contains_hole) : ¬ B.contains_hole := by
  induction hr <;> grind

def reflect_eta.{u} {τ_c : Type u} {A B : GenericExpr (@EtaConst τ_c)} (hr : RedAff A B)
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

def to_eta.{u} {τ_c : Type u} {e : GenericExpr τ_c} (hn : GenericExpr.IsNorm RedAff e) : GenericExpr.IsNorm GenericExpr.RedAff
  (e.expr_to_eta (τ_c := τ_c)) := fun ⟨_, h⟩ =>
  hn ⟨_, to_eta_left_inv ▸ (h.reflect_eta GenericExpr.to_eta_no_hole)⟩

--def from_eta₀

def from_eta.{u} {τ_c : Type u} {e : GenericExpr (@EtaConst τ_c)} (hn₁ : GenericExpr.IsNorm RedAff e) (hn₂ : ¬ e.contains_hole) : GenericExpr.IsNorm GenericExpr.RedAff
  (e.eta_to_expr hn₂) := fun ⟨_, h⟩ =>
  hn₁ ⟨_, to_eta_right_inv hn₂ ▸ h.cast_red_eta⟩

end IsNorm

section

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

open Monad in
class EtaRel.{v} (r : GenericExpr τ_c → GenericExpr τ_c → Sort v)
  (m : Type (max u v) → Type (max u v) := Option) [_hM : AlternativeMonad m] where
  is_norm_aff   : IsNorm RedAff A → r A B → IsNorm RedAff B
  run           : ∀ (A : GenericExpr τ_c), m ((B : GenericExpr τ_c) × (PULift.{v + 1, v} (r A B)))
  complete      : ∀ (h : r A B), run A = (pure ⟨B, ⟨h⟩⟩)
  none          : ∀ (_h : run A = failure) (_hr : r A B), False
  sound         : (run A = pure ⟨B, ⟨h⟩⟩) → r A B := fun (_heq : run A = pure ⟨B, ⟨h⟩⟩) => h
  none_complete : (∀ {B : GenericExpr τ_c}, r A B → False)  → run A = failure

attribute [grind =_, grind ., grind! ., aesop safe apply (rule_sets := [DccRel])] EtaRel.complete
attribute [grind] EtaRel.run
attribute [grind] EtaRel.sound
attribute [dcc_rel] EtaRel.is_norm_aff

open EtaRel in
open Monad in
class EtaRelProp (r : GenericExpr τ_c → GenericExpr τ_c → Prop)
  (m : Type (max u 0) → Type (max u 0) := Option) [_hM : AlternativeMonad m] : Type max u v extends (EtaRel.{u, 0} r m) where
  none_complete' : (¬ ∃ B, r A B)  → run A = failure

attribute [grind =] EtaRelProp.none_complete'

open Monad in
class OptionEtaRel.{v} (r : GenericExpr τ_c → GenericExpr τ_c → Sort v)
  : Type max u v extends (EtaRel r Option) where
  none          : ∀ {A B : GenericExpr τ_c} (_h : run A = failure) (_hr : r A B), False := fun heq hr => by
    simp_all [complete hr, failure, pure]
  none_complete := fun hn => by
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, ⟨h⟩⟩
    have heq := complete h
    simp_all
    exact hn h
  unique        : ∀ {A B C : GenericExpr τ_c} (_hr₁ : r A B) (_hr₂ : r A C), B = C := fun hr₁ hr₂ => by
    have h₁ := complete hr₁
    have h₂ := complete hr₂
    simp_all
  unique'       : ∀ {A B C : GenericExpr τ_c} (_hrt₁ : r A B) {_hr₂ : r A C}, B = C := unique

attribute [dcc_rel] OptionEtaRel.unique
attribute [dcc_rel, aesop safe forward (rule_sets := [DccRel])] OptionEtaRel.unique'

end

open OptionEtaRel in
@[grind =]
theorem OptionEtaRel.none_complete'
  (r : GenericExpr τ_c → GenericExpr τ_c → Prop) [hR : OptionEtaRel r] {A : GenericExpr τ_c} : (¬ ∃ B, r A B) → hR.run A = .none := by
  intro hn
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨_, ⟨h⟩⟩
  exact (hn ⟨_, h⟩).elim

end GenericExpr

open GenericExpr in
instance Domain.instEtaRel.{u} {τ_c : Type u} [DecidableEq τ_c] : (EtaRel (τ_c := τ_c) Domain Option) where
  run := domain?
  is_norm_aff := fun h h_dom => by
    have heq := h_dom.complete
    induction h_dom
    any_goals (
      focus
      rename_i ih
      intro ⟨_, h⟩
      cases h
      grind)
    any_goals (grind)
    · rename_i h_dom ih
      exact ih h.pil h_dom.complete
  complete := Domain.complete
  none     := fun heq hr => by dcc_aesop
  none_complete := fun h => by
    simp [failure]
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, ⟨hr⟩⟩
    exact (h hr).elim

open GenericExpr in
instance Domain.instOptionEtaRel.{u} {τ_c : Type u} [DecidableEq τ_c] : OptionEtaRel (τ_c := τ_c) Domain where
