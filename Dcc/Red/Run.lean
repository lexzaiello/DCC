import Dcc.Red.Rel
import Dcc.Red.RelationProp
import Mathlib.Tactic

namespace Expr

open Dsl

@[dcc_force_reduce, dcc_force_aff, aesop unsafe norm (rule_sets := [DccForceReduce])]
def step_head? (e : Expr) : Option ((e' : Expr) × (PULift.{1, 0} (Red e e'))) :=
  match e with
  | (DCC? ((Dup _B _x) (& _env) (& _y))) => .some ⟨_, ⟨.dup⟩⟩
  | (DCC? ((Map _B _C _f _g) (,__B _x _y))) => .some ⟨_, ⟨.bimap⟩⟩
  | (DCC? ((Assoc _A _B _C) (,_B₁ (,_B₂ _x _y) _z))) => .some ⟨_, ⟨.assoc⟩⟩
  | (DCC? ((𝟚.Rec _motive _x _y) _env 𝟙₂)) =>
    .some ⟨_, ⟨.ind_bool_true⟩⟩
  | (DCC? ((𝟚.Rec _motive _x _y) _env 𝟘₂)) =>
    .some ⟨_, ⟨.ind_bool_false⟩⟩
  | DCC? ((!<> _f) (& _x))                                 => .some ⟨_, ⟨.map⟩⟩
  | DCC? (($<> _f) (& _x))                                 => .some ⟨_, ⟨.fmap⟩⟩
  | DCC? ((* _α) (& _x))                                 => .some ⟨_, ⟨.unbox⟩⟩
  | DCC? ((⟨,⟩_β _M _N) (& _x))                        => .some ⟨_, ⟨.pair⟩⟩
  | (DCC? ((Eval _α _β _x) (,__β _y _z)))            => .some ⟨_, ⟨.evalc⟩⟩
  | (DCC? ((Eql _f_α) _env (,_B _x _y)))              => .some ⟨_, ⟨.eql⟩⟩
  | (DCC? ((`_β _x) _y))                             => .some ⟨_, ⟨.quot⟩⟩
  | (DCC? ((Id _α) _x))                                => .some ⟨_, ⟨.id⟩⟩
  | (DCC? ((Fst _α) (,_γ _a _b)))                     => .some ⟨_, ⟨.fstc⟩⟩
  | (DCC? ((Swap _B _C) (,_B₂ _a _b)))                 => .some ⟨_, ⟨.swap⟩⟩
  | (DCC? ((Snd _α) (,_γ _a _b)))                     => .some ⟨_, ⟨.sndc⟩⟩
  | (DCC? ((∘ _x _y) _z))                              => .some ⟨_, ⟨.comp⟩⟩
  | (DCC? ((!Λ _α _β _x) (& _y) (& _z)))                => .some ⟨_, ⟨.curr'⟩⟩
  | (DCC? ((Λ _α _β _x) _y _z)) => .some ⟨_, ⟨.curr⟩⟩
  | _ => .none

@[dcc_force_reduce, dcc_force_aff, aesop unsafe norm (rule_sets := [DccForceReduce])]
def step? (e : Expr) : Option ((e' : Expr) × (PULift.{1, 0} (Red e e'))) :=
  match step_head? e with
  | .some h => .some h
  | .none =>
    match e.cases_point_arity' with
    | .inl ⟨heq⟩ =>
      match e with
      | DCC? (f x) =>
        match f.step?, x.step? with
        | .some ⟨f', ⟨h₁⟩⟩, _ => .some ⟨(DCC? (f' x)), ⟨.congrFun h₁⟩⟩
        | _, .some ⟨x', ⟨h₁⟩⟩ => .some ⟨(DCC? (f x')), ⟨.congrArg h₁⟩⟩
        | _, _ => .none
      | _ => .none
    | .inr (.inl ⟨heq⟩) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step? with
      | .some ⟨_, ⟨h₁⟩⟩ =>
        .some ⟨_, ⟨.point 0 (by simp [heq]) h₁⟩⟩
      | .none => .none
    | .inr (.inr (.inl ⟨heq⟩)) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step?, (e.points.get ⟨1, by simp [heq]⟩).step? with
      | .some ⟨_, ⟨h₁⟩⟩, _ =>
        .some ⟨_, ⟨.point 0 (by simp [heq]) h₁⟩⟩
      | _, .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.point 1 (by simp [heq]) h₂⟩⟩
      | _, _ => .none
    | .inr (.inr (.inr (.inl ⟨heq⟩))) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step?, (e.points.get ⟨1, by simp [heq]⟩).step? with
      | .some ⟨_, ⟨h₁⟩⟩, _ =>
        .some ⟨_, ⟨.point 0 (by simp [heq]) h₁⟩⟩
      | _, .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.point 1 (by simp [heq]) h₂⟩⟩
      | _, _ =>
        match (e.points.get ⟨2, by simp [heq]⟩).step? with
        | .some ⟨_, ⟨h₃⟩⟩ =>
          .some ⟨_, ⟨.point 2 (by simp [heq]) h₃⟩⟩
        | .none => .none
    | .inr (.inr (.inr (.inr ⟨heq⟩))) =>
      match (e.points.get ⟨0, by simp [heq]⟩).step?, (e.points.get ⟨1, by simp [heq]⟩).step? with
      | .some ⟨_, ⟨h₁⟩⟩, _ =>
        .some ⟨_, ⟨.point 0 (by simp [heq]) h₁⟩⟩
      | _, .some ⟨_, ⟨h₂⟩⟩ =>
        .some ⟨_, ⟨.point 1 (by simp [heq]) h₂⟩⟩
      | _, _ =>
        match (e.points.get ⟨2, by simp [heq]⟩).step?, (e.points.get ⟨3, by simp [heq]⟩).step? with
        | .some ⟨_, ⟨h₃⟩⟩, _ =>
          .some ⟨_, ⟨.point 2 (by simp [heq]) h₃⟩⟩
        | _, .some ⟨_, ⟨h₄⟩⟩ =>
          .some ⟨_, ⟨.point 3 (by simp [heq]) h₄⟩⟩
        | _, _ => .none
termination_by (e.size, sizeOf e)
decreasing_by
  any_goals (grind)

/-@[dcc_force_reduce, dcc_force_aff, aesop unsafe norm (rule_sets := [DccForceReduce])]
def step? (e : GenericExpr τ) : Option ((e' : GenericExpr τ) × (PULift.{u + 1, 0} (RedAff (τ := τ) e e'))) :=
  match e with
  | (DCC? ((Bool.Ind motive x y) env True)) =>
    .some ⟨_, ⟨.ind_bool_true⟩⟩
  | (DCC? ((Bool.Ind motive x y) env False)) =>
    .some ⟨_, ⟨.ind_bool_false⟩⟩
  | (DCC? (Unify τ_A τ_B (Sort (m + 1)) ⊥)) =>
    .some ⟨_, ⟨.unif_bot_sort⟩⟩
  | (DCC? (Unify τ_A τ_B (Sort 0) ⊥)) =>
    .some ⟨_, ⟨.unif_bot_prop⟩⟩
  | (DCC? (((≃.1 f_x B) env₁) ((≃.mk fX fY fidl fidr) env₂))) =>
    .some ⟨_, ⟨.cong_1⟩⟩
  | (DCC? (((≃.2 B f_x) env₁) ((≃.mk fX fY fidl fidr) env₂))) =>
    .some ⟨_, ⟨.cong_2⟩⟩
  | (DCC? (((≃.3 f_x B) env₁) ((≃.mk fX fY fidl fidr) env₂))) =>
    .some ⟨_, ⟨.cong_3⟩⟩
  | (DCC? (((≃.4 B f_x) env₁) ((≃.mk fX fY fidl fidr) env₂))) =>
    .some ⟨_, ⟨.cong_4⟩⟩
  | (DCC? (≃.1 f_x B)) =>
    match f_x.step?, B.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ =>
      .some ⟨_, ⟨.point 0 (by simp [point_arity]) h₁⟩⟩
    | _, .some ⟨_, ⟨h₂⟩⟩ =>
      .some ⟨_, ⟨.point 1 (by simp [point_arity]) h₂⟩⟩
    | _, _ => .none
  | (DCC? (Unify τ_A₁ τ_A₂ A B)) =>
    if heq : A = B then
      heq ▸ .some ⟨_, ⟨RedAff.unif_refl⟩⟩
    else
      match A, B with
      | (DCC? Sort (u + 1)), DCC? ⊥ =>
        .some ⟨_, ⟨.unif_bot_sort⟩⟩
      | (DCC? Sort 0), DCC? ⊥ =>
        .some ⟨_, ⟨.unif_bot_prop⟩⟩
      | A, B =>
        match τ_A₁.step?, τ_A₂.step? with
        | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h₁⟩⟩
        | _, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h₂⟩⟩
        | _, _ =>
          match A.step?, B.step? with
          | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 2 (by simp [point_arity]) h₁⟩⟩
          | _, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.point 3 (by simp [point_arity]) h₂⟩⟩
          | _, _ => .none
  | DCC? (Bool.Ind motive x y) =>
    match motive.step?, x.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h₁⟩⟩
    | _, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h₂⟩⟩
    | _, _ =>
      match y.step? with
      | .some ⟨_, ⟨h₃⟩⟩ => .some ⟨_, ⟨.point 2 (by simp [point_arity]) h₃⟩⟩
      | .none => .none
  | DCC? (≃.Ind motive x) =>
    match motive.step?, x.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h₁⟩⟩
    | _, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h₂⟩⟩
    | _, _ => .none
  | DCC? (≃.mk to_fun inv_fun comp_id id_comp) =>
    match to_fun.step?, inv_fun.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h₁⟩⟩
    | _, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h₂⟩⟩
    | _, _ =>
      match comp_id.step?, id_comp.step? with
      | .some ⟨_, ⟨h₃⟩⟩, _ => .some ⟨_, ⟨.point 2 (by simp [point_arity]) h₃⟩⟩
      | _, .some ⟨_, ⟨h₄⟩⟩ => .some ⟨_, ⟨.point 3 (by simp [point_arity]) h₄⟩⟩
      | _, _ => .none
  | (DCC? (Π f_α f_β)) =>
    match f_α.step?, f_β.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h₁⟩⟩
    | _, _ => .none
  | (DCC? (Σ f_α f_β)) =>
    match f_α.step?, f_β.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h₁⟩⟩
    | _, _ => .none
  | (DCC? ((Eql _f_α) (& _env) (& _x))) => .some ⟨_, ⟨.eql⟩⟩
  | (DCC? (x = y)) =>
    match x.step?, y.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h₁⟩⟩
    | _, _ => .none
  | DCC? (! x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
    | _ => .none
  | DCC? (!<> x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
    | _ => .none
  | DCC? ((!<> _f) (& _x))                                 => .some ⟨_, ⟨.map⟩⟩
  | DCC? (($<> _f) (& _x))                                 => .some ⟨_, ⟨.fmap⟩⟩
  | DCC? ((* _α) (& _x))                                 => .some ⟨_, ⟨.unbox⟩⟩
  | DCC? (* x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
    | _ => .none
  | DCC? ($<> x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
    | _ => .none
  | DCC? (& x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
    | _ => .none
  | DCC? ((⟨,⟩_β M N) (& _x))                        => .some ⟨_, ⟨.pair⟩⟩
  | (DCC? ((Eval _α _β _x) (,__β _y _z)))            => .some ⟨_, ⟨.evalc⟩⟩
  | (DCC? ((`_β _x) _y))                             => .some ⟨_, ⟨.quot⟩⟩
  | (DCC? ((Id _α) _x))                                => .some ⟨_, ⟨.id⟩⟩
  | (DCC? ((Fst _α) (,_γ _a _b)))                     => .some ⟨_, ⟨.fstc⟩⟩
  | (DCC? ((Swap _B _C) (,_B₂ _a _b)))                 => .some ⟨_, ⟨.swap⟩⟩
  | DCC? (Fst B) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
    | _ => .none
  | DCC? (Snd B) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
    | _ => .none
  | DCC? (Swap B C) =>
    match B.step?, C.step? with
    | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
    | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h⟩⟩
    | _, _ => .none
  | DCC? (Eql B) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨ .point 0 (by simp [point_arity]) h⟩⟩
    | _ => .none
  | DCC? (Id A) =>
    match A.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨ .point 0 (by simp [point_arity]) h⟩⟩
    | _ => .none
  | DCC? (refl B) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨ .point 0 (by simp [point_arity]) h⟩⟩
    | _ => .none
  | (DCC? ((Snd _α) (,_γ _a _b)))                     => .some ⟨_, ⟨.sndc⟩⟩
  | (DCC? ((∘ _x _y) _z))                              => .some ⟨_, ⟨.comp⟩⟩
  | DCC? (∘ x  y) =>
    match x.step?, y.step? with
    | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
    | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h⟩⟩
    | _, _ => .none
  | (DCC? ((!Λ _α _β _x) (& _y) (& _z)))                => .some ⟨_, ⟨.curr'⟩⟩
  | DCC? (!Λ A B x) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h⟩⟩
    | .none => match A.step?, x.step? with
      | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
      | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 2 (by simp [point_arity]) h⟩⟩
      | _, _ => .none
  | (DCC? ((Λ _α _β _x) _y _z)) => .some ⟨_, ⟨.curr⟩⟩
  | DCC? (Λ A B x) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h⟩⟩
    | .none => match A.step?, x.step? with
      | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
      | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 2 (by simp [point_arity]) h⟩⟩
      | _, _ => .none
  | DCC? (Eval A B x) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h⟩⟩
    | .none => match A.step?, x.step? with
      | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
      | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 2 (by simp [point_arity]) h⟩⟩
      | _, _ => .none
  | (DCC? ((Σ _f_α _f_β) _env))                        => .some ⟨_, ⟨.sigma⟩⟩
  | DCC? (,β x y) =>
    match β.step? with
    | .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h₁⟩⟩
    | _ =>
      match x.step?, y.step? with
      | .some ⟨x', ⟨h₁⟩⟩, _ => .some ⟨(DCC? (,β x' y)), ⟨.point 1 (by simp [point_arity]) h₁⟩⟩
      | _, .some ⟨y', ⟨h₁⟩⟩ => .some ⟨(DCC? (,β x y')), ⟨.point 2 (by simp [point_arity]) h₁⟩⟩
      | _, _ => .none
  | DCC? (⟨,⟩B x y) =>
    match B.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
    | _ =>
      match x.step?, y.step? with
      | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h⟩⟩
      | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 2 (by simp [point_arity]) h⟩⟩
      | _, _ => .none
  | (DCC? (Σ β)) =>
    match β.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
    | _ => .none
  | DCC? (`B x) =>
    match B.step?, x.step? with
    | .some ⟨_, ⟨h⟩⟩, _ => .some ⟨_, ⟨.point 0 (by simp [point_arity]) h⟩⟩
    | _, .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.point 1 (by simp [point_arity]) h⟩⟩
    | _, _ => .none
  | DCC? (f x) =>
    match f.step?, x.step? with
    | .some ⟨f', ⟨h₁⟩⟩, _ => .some ⟨(DCC? (f' x)), ⟨.congrFun h₁⟩⟩
    | _, .some ⟨x', ⟨h₁⟩⟩ => .some ⟨(DCC? (f x')), ⟨.congrArg h₁⟩⟩
    | _, _ => .none
  | DCC? (Dom (Eql _B)) => .some ⟨_, ⟨.eqlτ₀⟩⟩
  | DCC? (Dom (refl _B)) => .some ⟨_, ⟨.reflτ₀⟩⟩
  | DCC? (Dom (!<> _x)) => .some ⟨_, ⟨.mapτ₀⟩⟩
  | DCC? (Dom ($<> _x)) => .some ⟨_, ⟨.fmapτ₀⟩⟩
  | DCC? (Dom (* _x)) => .some ⟨_, ⟨.unboxτ₀⟩⟩
  | DCC? (Dom (⟨,⟩_B _x _y)) => .some ⟨_, ⟨.pairτ₀⟩⟩
  | DCC? (Dom (Eval _A _B _x)) => .some ⟨_, ⟨.evalcτ₀⟩⟩
  | DCC? (Dom (`_B _x)) => .some ⟨_, ⟨.quotτ₀⟩⟩
  | DCC? (Dom (Id _A)) => .some ⟨_, ⟨.idτ₀⟩⟩
  | DCC? (Dom (Fst _B)) => .some ⟨_, ⟨.fstcτ₀⟩⟩
  | DCC? (Dom (Snd _B)) => .some ⟨_, ⟨.sndcτ₀⟩⟩
  | DCC? (Dom (Swap _B _C)) => .some ⟨_, ⟨.swapτ₀⟩⟩
  | DCC? (Dom (∘ _x _y)) => .some ⟨_, ⟨.compτ₀⟩⟩
  | DCC? (Dom (Λ _A _B _x)) => .some ⟨_, ⟨.currτ₀⟩⟩
  | DCC? (Dom (!Λ _A _B _x)) => .some ⟨_, ⟨.curr'τ₀⟩⟩
  | DCC? (Dom (Σ B C)) => .some ⟨_, ⟨.sigmaτ₀⟩⟩
  | DCC? (Dom (Π B C)) => .some ⟨_, ⟨.piτ₀⟩⟩
  | DCC? (Dom ((Eql _B) (& _x))) => .some ⟨_, ⟨.eqlτ₁⟩⟩
  | DCC? (Dom ((refl _B) (& _x))) => .some ⟨_, ⟨.reflτ₁⟩⟩
  | DCC? (Dom ((Λ _A _B _x) _y)) => .some ⟨_, ⟨.currτ₁⟩⟩
  | DCC? (Dom ((!Λ _A _B _x) (& _y))) => .some ⟨_, ⟨.curr'τ₁⟩⟩
  | DCC? (Dom x) =>
    match x.step? with
    | .some ⟨_, ⟨hr⟩⟩ => .some ⟨_, ⟨.dom₀ hr⟩⟩
    | .none => .none
  | DCC? (Uncoup (Σ x)) => .some ⟨_, ⟨.uncoup⟩⟩
  | DCC? (Unbang (! x)) => .some ⟨_, ⟨.unbang⟩⟩
  | DCC? (Uncoup x) =>
    match x.step? with
    | .some ⟨_, ⟨hr⟩⟩ => .some ⟨_, ⟨.uncoup₀ hr⟩⟩
    | .none => .none
  | DCC? (Unbang x) =>
    match x.step? with
    | .some ⟨_, ⟨hr⟩⟩ => .some ⟨_, ⟨.unbang₀ hr⟩⟩
    | .none => .none
  | DCC? (Dom₂ (Eql B)) => .some ⟨_, ⟨.eqlτ₃⟩⟩
  | DCC? (Dom₂ (refl B)) => .some ⟨_, ⟨.reflτ₃⟩⟩
  | DCC? (Dom₂ (Λ A B x)) => .some ⟨_, ⟨.currτ₃⟩⟩
  | DCC? (Dom₂ (!Λ A B x)) => .some ⟨_, ⟨.curr'τ₃⟩⟩
  | DCC? (Dom₂ x) =>
    match x.step? with
    | .some ⟨_, ⟨hr⟩⟩ => .some ⟨_, ⟨.dom₂₀ hr⟩⟩
    | .none => .none
  | _ => .none-/

set_option maxHeartbeats 10000000 in
@[dcc_force_reduce, dcc_force_aff]
instance Red.instRedRel : RedRel (α := Expr) Red size where
  run := step?
  decreasing := by
    intro x y h
    induction h
    case point =>
      expose_names
      have h := point_size_lt' (n := n) (h := h)
      have h' : p'.size < e.size := by grind
      have h := set_point_size_lt (by assumption) rfl (by assumption)
      simp_all
    any_goals (
      focus
      try dsimp
      try grind
      try simp_all [dcc_rel, dcc_size]
      try grind
      try aesop (rule_sets := [DccRel, DccSize])
      try rfl)

theorem red_aff_sn : ∀ (e : Expr), Acc (fun b a => Red a b) e :=
  Red.instRedRel.sn

theorem red_aff_trans_sn [DecidableEq τ] : ∀ (e : Expr), Acc (fun b a => Relation.TransGen Red a b) e :=
  Red.instRedRel.to_trans.sn

theorem congrFun' {f x f' : Expr} (hr : Relation.ReflTransGen Red f f') : Relation.ReflTransGen Red (DCC? (f x)) (DCC? (f' x)) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := Red.instRedRel.decreasing h₁
    exact .trans (.single (.congrFun h₁)) (congrFun' h₂)
termination_by size f

theorem swap₀' {x x' : Expr} (hr : Relation.ReflTransGen Red x x') : Relation.ReflTransGen Red (DCC? (Swap x _y)) (DCC? (Swap x' _y)) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := Red.instRedRel.decreasing h₁
    exact .trans (.single (.point 0 (by grind) h₁)) (swap₀' (by assumption))
termination_by x.size

theorem swap₁' {x x' : Expr} (hr : Relation.ReflTransGen Red x x') : Relation.ReflTransGen Red (DCC? (Swap _x x)) (DCC? (Swap _x x')) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := Red.instRedRel.decreasing h₁
    exact .trans (.single (.point 1 (by grind) h₁)) (swap₁' (by assumption))
termination_by x.size

theorem congrArg' {x x' : Expr} (hr : Relation.ReflTransGen Red x x') : Relation.ReflTransGen Red (DCC? (f x)) (DCC? (f x')) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    exact .refl
  | .inr ⟨_, h₁, h₂⟩ =>
    have h_dec := Red.instRedRel.decreasing h₁
    exact .trans (.single (.congrArg h₁)) (congrArg' h₂)
termination_by size x

theorem point' (hr : Relation.ReflTransGen Red ((points e).get ⟨n, h⟩) p') : Relation.ReflTransGen Red e (e.set_points ((points e).set n p')) :=
  match hr.cases_head with
  | .inl h => by
    cases h
    have heq := get_set_point (p := ⟨n, h⟩) (e := e) (p' := e.points.get ⟨n, h⟩)
    have heq' := get_set_point' (p := ⟨n, h⟩) (e := e) rfl
    simp [heq']
    exact Relation.ReflTransGen.refl
  | .inr ⟨_, h₁, h₂⟩ => by
    expose_names
    have h_dec := Red.instRedRel.decreasing h₁
    have h_dec₂ := decreasing? _ h₂
    have heq := set_same_point_comp (e := e) (x := w) (p := ⟨n, h⟩) (y := p')
    have hr' := Red.point _ _ h₁
    have hr'' := point_trans' h₁ h₂
    have h_dec₃ := decreasing? _ hr''
    have h_dec₂ : (e.set_points (e.points.set n w h)).size < e.size := by
      have h_dec := Red.instRedRel.decreasing hr'
      grind
    have hrt' := point' hr''
    have heq' := set_same_point_comp (e := e) (x := w) (p := ⟨n, h⟩) (y := p')
    simp [heq'] at hrt'
    exact Relation.ReflTransGen.trans (.single (.point n h h₁)) hrt'
termination_by e.size

syntax "point_arity" : tactic

macro_rules
  | `(tactic| point_arity) => `(tactic|
    first
    | (grind only [points, point_arity])
    | (simp [points, Vector.get, point_arity, set_points]; try (grind only [points, point_arity]); try rfl)
    | (simp_all [points, Vector.get, point_arity, set_points]; try (grind only [points, point_arity]); try rfl))

set_option maxHeartbeats 100000000000 in
theorem aff_mk_point' {x y e : Expr} (hr : Relation.ReflTransGen Red x y) (hn : n < point_arity e := by point_arity) (heq : (points e)[(Fin.mk n hn)] = x := by first | rfl | grind | (dcc_simp; rfl)) : Relation.ReflTransGen Red e (e.set_points ((points e).set n y)) := by
  match hr.cases_head with
  | .inl h =>
    cases h
    unfold point_arity at hn
    split at hn
    any_goals (grind)
    any_goals (
      focus
      try (
        simp at hn
        match n with
        | 0 | 1 | 2 | 3 =>
          simp at heq
          cases heq
          simp [set_points_self_noop]
          exact Relation.ReflTransGen.refl))
  | .inr ⟨_, h₁, h₂⟩ =>
    cases heq
    have h_dec := Red.instRedRel.decreasing h₁
    have hr' := point' hr
    exact hr'

theorem aff_mk_point'' {x y e : Expr} (n : ℕ) (hr : Red x y := by assumption) (hn : n < point_arity e := by point_arity) (heq : (points e)[(Fin.mk n hn)] = x := by first | rfl | grind | (dcc_simp; rfl)) : Relation.ReflTransGen Red e (e.set_points ((points e).set n y)) := aff_mk_point' (.single hr)

end Expr
