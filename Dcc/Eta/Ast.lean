import Dcc.Ast
import Dcc.Aff.Red
import Dcc.Ast.Mem
import Dcc.Aff.Size
import Dcc.Relation

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
      -> eta-reduces to f₁ ∘' Fst(β)
    2. Base eta (hole := 2), η-reduces to f₁
      -> eta-reduces to f₁ ∘' Snd(β)

- Sort | ⊤ | (Π(f_α, f_β) ...) | (f x)
  Use base

- will need extra cases for Π?
-/

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

abbrev EtaExpr.Norm := NormExpr (τ := @EtaConst τ_c) GenericExpr.RedAff

namespace GenericExpr

@[grind]
def mem_tm (e to_find : GenericExpr (τ := τ_c)) : Bool :=
  (decide (e = to_find)) || (
    match e with
    | DCC? ∗ => False
    | DCC? ⊤ => False
    | DCC? Sort _n => False
    | DCC? ⊥ => False
    | DCC? Π(_x, _y) => False
    | DCC? (x ∘' y)
    | DCC? (x ∘ y)
    | DCC? (x ∘∘ y)
    | DCC? (x y) => x.mem_tm to_find ∨ y.mem_tm to_find
    | DCC? _x = _y => False
    | DCC? Fst(_α)
    | DCC? Snd(_α)
    | DCC? Coup(_α)
    | DCC? Id(_α)
    | DCC? Eql(_α)
    | DCC? refl(_α)
    | DCC? *(_α)
    | DCC? !(_α)
    | DCC? !<_α>
    | DCC? Σ(_α, _β) => False
    | DCC? &(α)
    | DCC? $<α>
    | DCC? *<α> => α.mem_tm to_find
    | DCC? `(_β, x) => x.mem_tm to_find
    | DCC? Eval(_β, _x, y)
    | DCC? !Λ(_β, _x, y)
    | DCC? Λ(_β, _x, y) => y.mem_tm to_find
    | DCC? ⟦_β⟧(x, y)
    | DCC? ⟦_β⟧⟨x, y⟩ => x.mem_tm to_find ∨ y.mem_tm to_find
    | .const _ => False)

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
    | DCC[.] Fst(α)
    | DCC[.] Snd(α)
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
    | DCC[.] Fst(α)
    | DCC[.] Snd(α)
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

def mem_imp_contains_hole (h : hole_mem_tm (τ := τ_c) e) : contains_hole e := by
  induction e
  any_goals (grind)
  case const x =>
    cases x
    · simp [contains_hole]
    · simp_all [hole_mem_tm]

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
  | DCC[.] `(_β, x) => x.arity.succ
  | DCC[.] ⟦__β⟧(_x, _y) => 0
  | DCC[.] Coup(_β) => 0
  | DCC[.] Id((Π(_α, _β) _x_α)) => 2
  | DCC[.] Id(_α)      => 1
  | DCC[.] Fst(_α)    => 1
  | DCC[.] Snd(_α)    => 1
  | DCC[.] Π(_α, _β) => 1
  | DCC[.] (f ∘' g) => (f.arity - 1) + g.arity
  | DCC[.] (f ∘ g)  => (f.arity - 1) + g.arity
  | DCC[.] (f ∘∘ g)  => (f.arity - 1) + g.arity
  | DCC[.] ⟦_β⟧⟨_a, _b⟩   => 1
  | DCC[.] Λ(_α, _β, x) => (x.arity - 1) + 2
  | DCC[.] !Λ(_α, _β, x) => (x.arity - 1) + 2
  | DCC[.] Eval(_α, _β, _x) => 1
  | DCC[.] !(_x)   => 0
  | DCC[.] *(_α)   => 1
  | DCC[.] *<f>    => f.arity
  | DCC[.] &(_x)   => 0
  | DCC[.] !<_x>   => 1
  | DCC[.] $<_x>   => 1
  | DCC[.] (f _x) => f.arity - 1
  | .const _n => 0

@[grind]
def is_fn (e : GenericExpr (τ := τ_c)) : Bool :=
match e with
  | DCC[.] ∗ => False
  | DCC[.] ⊤ => False
  | DCC[.] ⊥ => False
  | DCC[.] _x = _y => False
  | DCC[.] Eql(f_α)  => f_α.is_fn
  | DCC[.] refl(f_α) => f_α.is_fn
  | DCC[.] Sort _m => False
  | DCC[.] Σ(f_α, f_β) => f_α.is_fn ∧ f_β.is_fn
  | DCC[.] `(_β, _x) => True
  | DCC[.] ⟦__β⟧(_x, _y) => False
  | DCC[.] Coup(_β) => False
  | DCC[.] Id(_α)      => True
  | DCC[.] Fst(_α)    => True
  | DCC[.] Snd(_α)    => True
  | DCC[.] Π(f_α, f_β) => f_α.is_fn ∧ f_β.is_fn
  | DCC[.] (f ∘' g) => f.is_fn ∧ g.is_fn
  | DCC[.] (f ∘ g)  => f.is_fn ∧ g.is_fn
  | DCC[.] (f ∘∘ g)  => f.is_fn ∧ g.is_fn
  | DCC[.] ⟦_β⟧⟨a, b⟩   => a.is_fn ∧ b.is_fn
  | DCC[.] Λ(_α, β, x) => β.is_fn ∧ x.is_fn
  | DCC[.] !Λ(_α, β, x) => β.is_fn ∧ x.is_fn
  | DCC[.] Eval(_α, β, x) => β.is_fn ∧ x.is_fn
  | DCC[.] !(_x)   => False
  | DCC[.] *(_α)   => True
  | DCC[.] *<f>    => f.is_fn
  | DCC[.] &(_x)   => False
  | DCC[.] !<x>   => x.is_fn
  | DCC[.] $<x>   => x.is_fn
  | DCC[.] (f _x) =>
    f.is_fn ∧ (0 < f.arity)
  | .const _n => False

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
  | DCC[.] Fst(_α)    => 1
  | DCC[.] Snd(_α)    => 1
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

omit [DecidableEq τ_c] in
@[grind =, grind! ., dcc_size]
theorem coup_hole_zero : (DCC? ⟦hole(m)⟧(hole(n), hole(o))).size (τ := (@EtaConst τ_c)) = 0 := by
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

@[grind, dcc_rel]
def eta_to_expr (e : @EtaExpr τ_c)
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
  | DCC? Fst(x)    =>
    match x.eta_to_expr (by simp_all [contains_hole])with
    | x' => (DCC? Fst(x'))
  | DCC? Snd(x)    =>
    match x.eta_to_expr (by simp_all [contains_hole])with
    | x' => (DCC? Snd(x'))
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

@[grind, dcc_rel]
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
  | DCC? Fst(x)    =>
    match x.expr_to_eta with
    | x' => (DCC? Fst(x'))
  | DCC? Snd(x)    =>
    match x.expr_to_eta with
    | x' => (DCC? Snd(x'))
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

def to_eta_no_mem_hole {e : GenericExpr τ} : ¬ (expr_to_eta e).hole_mem_tm := by
  induction e <;> (simp_all [expr_to_eta, hole_mem_tm])

@[dcc_reduce, dcc_rel]
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

@[dcc_reduce, dcc_rel]
def to_eta_left_inv'
  {e : GenericExpr τ} {hn : ¬e.expr_to_eta.contains_hole = true} : eta_to_expr (expr_to_eta e) hn = e := by
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


@[dcc_reduce, dcc_rel]
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

theorem to_eta_arr_same (h : GenericExpr.arity e = n) : GenericExpr.arity e.expr_to_eta = n := by
  induction e generalizing n
  any_goals (grind)
  case id =>
    unfold expr_to_eta
    simp
    expose_names
    unfold arity
    unfold arity at h
    simp_all
    split at h
    any_goals (grind)
    case _ =>
      expose_names
      cases heq
      split
      any_goals (grind)
      case _ =>
        simp_all
        expose_names
        unfold expr_to_eta at heq
        split at heq
        any_goals (grind)
        try (
          case _ =>
            expose_names
            simp at heq
            cases heq.right
            have hl := heq.left
            unfold expr_to_eta at hl
            split at hl
            any_goals (grind))

@[grind =, grind =_]
theorem to_eta_arr_same' : GenericExpr.arity e = GenericExpr.arity e.expr_to_eta := by
  have h := to_eta_arr_same (e := e) (h := rfl)
  grind

@[grind =, grind =_, grind →, grind! .]
theorem from_eta_arr_same : (GenericExpr.arity (eta_to_expr e hn_mem)) = (GenericExpr.arity e) := by
  induction e
  any_goals (unfold eta_to_expr; grind)
  case id =>
    unfold eta_to_expr
    simp
    expose_names
    unfold arity
    simp_all
    split
    any_goals (grind)
    case _ =>
      expose_names
      simp at heq
      split
      any_goals (grind)
      case _ =>
        simp_all
        expose_names
        unfold eta_to_expr at heq
        split at heq
        any_goals (grind)
        case _ =>
          expose_names
          simp at heq
          cases heq.right
          have hl := heq.left
          unfold eta_to_expr at hl
          split at hl
          any_goals (grind)

@[grind =, grind =_, grind →, grind! ., grind! →]
theorem from_to_size_same : (eta_to_expr e hn).expr_to_eta.size = e.size := by
  induction e
  any_goals (grind)
  · dcc_simp

end GenericExpr
