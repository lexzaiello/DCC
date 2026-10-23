import Dcc.Aff.Rel
import Dcc.Aff.Complete
import Dcc.Ast

universe u
variable {τ : Type u}

namespace GenericExpr

inductive ViewW : GenericExpr τ → Type u
  | mk : ViewW (open Dsl in (DCC? (((W.Rec A B motive x) env) ((W.Sup A₂ B₂ label y) env₂))))

def view_w (e : GenericExpr τ) : Option (ViewW e) :=
  open Dsl in match e with
  | (DCC? (((W.Rec _A _B _motive _x) _env) ((W.Sup _A₂ _B₂ _label _y) _env₂))) => .some .mk
  | _ => .none

def ViewW.complete (h : ViewW e) : view_w e = .some h := by
  cases h
  simp [view_w]

def view_w_none_complete (hn : ViewW e → False := by assumption) : view_w e = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro h
  exact (hn h).elim

inductive RedW : GenericExpr τ → GenericExpr τ → Type u
  | ind_w     : RedAffNorm (open Dsl in (DCC? (x env (label env₂) (y env₂) (∘ ((W.Rec A B motive x) env) (y env₂))))) ⟨e', hn'⟩
    → (e'.size < (open Dsl in (DCC? (((W.Rec A B motive x) env) ((W.Sup A₂ B₂ label y) env₂)))).size)
    → RedW e' e''
    → RedW (open Dsl in (DCC? (((W.Rec A B motive x) env) ((W.Sup A₂ B₂ label y) env₂)))) e''
  | congr     : (ViewW (DCC? (f x)) → False)
    → RedW f f'
    → RedW x x'
    → RedW (open Dsl in (DCC? (f x))) (open Dsl in (DCC? (f' x')))
  | no_step   : (ViewW e → False)
    → (heq_ar : point_arity e = 0) → RedW e e
  | point₁    : (ViewW e → False)
    → (h : point_arity e = 1)
    → RedW (points e)[0] p'
    → RedW e (e.set_points ⟨#[p'], by grind⟩)
  | point₂    : (ViewW e → False) → (h : point_arity e = 2) → (hr₁ : RedW (points e)[0] p'₁) → (hr₂ : RedW (points e)[1] p'₂) → RedW e (e.set_points ⟨#[p'₁, p'₂], by grind⟩)
  | point₃    : (ViewW e → False) → (h : point_arity e = 3) → (hr₁ : RedW (points e)[0] p'₁) → (hr₂ : RedW (points e)[1] p'₂) → (hr₃ : RedW (points e)[2] p'₃) → RedW e (e.set_points ⟨#[p'₁, p'₂, p'₃], by grind⟩)
  | point₄    : (ViewW e → False) → (h : point_arity e = 4) → (hr₁ : RedW (points e)[0] p'₁) → (hr₂ : RedW (points e)[1] p'₂) → (hr₃ : RedW (points e)[2] p'₃) → (hr₃ : RedW (points e)[3] p'₄) → RedW e (e.set_points ⟨#[p'₁, p'₂, p'₃, p'₄], by simp [h]⟩)

def red_w (e : GenericExpr τ) : Option (Σ' e', RedW e e') :=
  if heq : view_w e = .none then
    have hn : ViewW e → False := fun h => by simp_all [h.complete]
    match cases_point_arity' e with
    | .inl ⟨heq⟩ =>
      .some ⟨_, .no_step hn heq⟩
    | .inr (.inl ⟨heq⟩) => do
      .some ⟨_, .point₁ hn heq (← red_w (e.points.get ⟨0, by grind⟩)).snd⟩
    | .inr (.inr (.inl ⟨heq⟩)) => do
      .some ⟨_, .point₂ hn heq (← red_w (e.points.get ⟨0, by grind⟩)).snd (← red_w (e.points.get ⟨1, by grind⟩)).snd⟩
    | .inr (.inr (.inr (.inl ⟨heq⟩))) => do
      .some ⟨_, .point₃ hn heq (← red_w (e.points.get ⟨0, by grind⟩)).snd
                               (← red_w (e.points.get ⟨1, by grind⟩)).snd
                               (← red_w (e.points.get ⟨2, by grind⟩)).snd⟩
    | .inr (.inr (.inr (.inr ⟨heq⟩))) => do
      .some ⟨_, .point₄ hn heq (← red_w (e.points.get ⟨0, by grind⟩)).snd
                               (← red_w (e.points.get ⟨1, by grind⟩)).snd
                               (← red_w (e.points.get ⟨2, by grind⟩)).snd
                               (← red_w (e.points.get ⟨3, by grind⟩)).snd⟩
  else
    open Dsl in match e with
    | (DCC? (((W.Rec A B motive x) env) ((W.Sup A₂ B₂ label y) env₂))) =>
      if hlt : (reduce RedAff (DCC? (x env (label env₂) (y env₂) (∘ ((W.Rec A B motive x) env) (y env₂))))).fst.size < (DCC? (((W.Rec A B motive x) env) ((W.Sup A₂ B₂ label y) env₂))).size then
        match red_w (reduce RedAff (DCC? (x env (label env₂) (y env₂) (∘ ((W.Rec A B motive x) env) (y env₂))))).fst with
        | .some ⟨_, h⟩ =>
          .some ⟨_, .ind_w ⟨reduce_sound rfl, reduce_norm rfl⟩ hlt h⟩
        | .none => .none
      else .none
    | _ => .none
termination_by e.size
decreasing_by
  any_goals (first | exact point_size_lt | grind)

def RedW.complete (h : RedW A B) : red_w A = .some ⟨B, h⟩ := by
  induction h with
  | ind_w =>
    expose_names
    unfold red_w
    cases a.complete_fst
    simp [view_w, h, a_ih]
    apply RedAffNorm.ext
  | point₁ =>
    expose_names
    unfold red_w
    simp [view_w_none_complete (by assumption)]
    try (simp [point_arity₀_cases (by assumption)])
    try (simp [point_arity₁_cases (by assumption)])
    try (simp [point_arity₂_cases (by assumption)])
    try (simp [point_arity₃_cases (by assumption)])
    try (simp [point_arity₄_cases (by assumption)])
    

/-def red_w (e : GenericExpr τ) : Option (Σ' e', RedW e e') :=
  if heq : view_w e = .none then
    have hn : ViewW e → False := fun h => by simp_all [h.complete]
    match cases_point_arity' e with
    | .inl ⟨heq⟩ =>
      .some ⟨_, .no_step hn heq⟩
    | .inr (.inl ⟨heq⟩) =>
      match red_w (e.points.get ⟨0, by grind⟩) with
      | .some ⟨_, h⟩ => .some ⟨_, .point₁ hn heq h⟩
      | .none => .none
    | .inr (.inr (.inl ⟨heq⟩)) =>
      match red_w (e.points.get ⟨0, by grind⟩), red_w (e.points.get ⟨1, by grind⟩) with
      | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
        .some ⟨_, .point₂ hn heq h₁ h₂⟩
      | _, _ => .none
    | .inr (.inr (.inr (.inl ⟨heq⟩))) =>
      match red_w (e.points.get ⟨0, by grind⟩), red_w (e.points.get ⟨1, by grind⟩), red_w (e.points.get ⟨2, by grind⟩) with
      | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ =>
        .some ⟨_, .point₃ hn heq h₁ h₂ h₃⟩
      | _, _, _ => .none
    | .inr (.inr (.inr (.inr ⟨heq⟩))) =>
      match red_w (e.points.get ⟨0, by grind⟩), red_w (e.points.get ⟨1, by grind⟩), red_w (e.points.get ⟨2, by grind⟩), red_w (e.points.get ⟨3, by grind⟩) with
      | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩, .some ⟨_, h₃⟩, .some ⟨_, h₄⟩ =>
        .some ⟨_, .point₄ hn heq h₁ h₂ h₃ h₄⟩
      | _, _, _, _ => .none
  else
    open Dsl in match e with
    | (DCC? (((W.Rec A B motive x) env) ((W.Sup A₂ B₂ label y) env₂))) =>
      if hlt : (reduce RedAff (DCC? (x env (label env₂) (y env₂) (∘ ((W.Rec A B motive x) env) (y env₂))))).fst.size < (DCC? (((W.Rec A B motive x) env) ((W.Sup A₂ B₂ label y) env₂))).size then
        match red_w (reduce RedAff (DCC? (x env (label env₂) (y env₂) (∘ ((W.Rec A B motive x) env) (y env₂))))).fst with
        | .some ⟨_, h⟩ =>
          .some ⟨_, .ind_w ⟨reduce_sound rfl, reduce_norm rfl⟩ hlt h⟩
        | .none => .none
      else .none
    | _ => .none
termination_by e.size
decreasing_by
  any_goals (first | exact point_size_lt | grind)-/

end GenericExpr
