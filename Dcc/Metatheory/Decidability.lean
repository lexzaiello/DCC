import Dcc.Judge

namespace Expr

theorem eq_is_norm (hn₁ : IsNorm Red A) (hn₂ : IsNorm Red x) (hn₃ : IsNorm Red y) : IsNorm Red (DCC (= A x y)) := fun ⟨_, h⟩ =>
  match h with
  | .point 0 hn h => hn₁ ⟨_, h⟩
  | .point 1 hn h => hn₂ ⟨_, h⟩
  | .point 2 hn h => hn₃ ⟨_, h⟩

theorem mk_is_norm (hn₁ : IsNorm Red B) (hn₂ : IsNorm Red x) (hn₃ : IsNorm Red y) : IsNorm Red (DCC (,B x y)) := fun ⟨_, h⟩ =>
  match h with
  | .point 0 hn h => hn₁ ⟨_, h⟩
  | .point 1 hn h => hn₂ ⟨_, h⟩
  | .point 2 hn h => hn₃ ⟨_, h⟩

open Dsl in
@[grind .] theorem top_is_norm : IsNorm Red (DCC 𝟙) := fun ⟨_, h⟩ => nomatch h

open Dsl in
@[grind .] theorem bot_is_norm : IsNorm Red (DCC 𝟘) := fun ⟨_, h⟩ => nomatch h

open Dsl in
@[grind .] theorem bool_is_norm : IsNorm Red (DCC 𝟚) := fun ⟨_, h⟩ => nomatch h

open Dsl in
@[grind .] theorem true_is_norm : IsNorm Red (DCC 𝟙₂) := fun ⟨_, h⟩ => nomatch h

open Dsl in
@[grind .] theorem false_is_norm : IsNorm Red (DCC 𝟘₂) := fun ⟨_, h⟩ => nomatch h

open Dsl in
@[grind. ] theorem tintro_is_norm : IsNorm Red (DCC ∗) := fun ⟨_, h⟩ => nomatch h

@[grind .]
theorem sort_is_norm : IsNorm Red (DCC (Sort s)) := fun ⟨_, h⟩ => nomatch h

@[grind .] theorem fst_is_norm (hn : IsNorm Red B) : IsNorm Red (DCC (Fst B)) := fun ⟨_, .point 0 _ h⟩ => hn ⟨_, h⟩
@[grind .] theorem snd_is_norm (hn : IsNorm Red B) : IsNorm Red (DCC (Snd B)) := fun ⟨_, .point 0 _ h⟩ => hn ⟨_, h⟩

@[grind .]
theorem eql_is_norm (hn₁ : IsNorm Red x) : IsNorm Red (DCC (Eql x)) := fun ⟨_, .point 0 _ h⟩ => hn₁ ⟨_, h⟩

open Dsl in
@[grind .] theorem map_is_norm (hn : IsNorm Red B) : IsNorm Red (DCC (!<> B)) := fun ⟨_, .point 0 _ h⟩ => hn ⟨_, h⟩

open Dsl in
@[grind .] theorem bang_is_norm (hn : IsNorm Red A) : IsNorm Red (DCC (! A)) := fun ⟨_, .point 0 _ h⟩ => hn ⟨_, h⟩

open Dsl in
@[grind .] theorem box_is_norm (hn : IsNorm Red x) : IsNorm Red (DCC (& x)) := fun ⟨_, .point 0 _ h⟩ => hn ⟨_, h⟩

@[grind .] theorem curr_is_norm (hn₁ : IsNorm Red A) (hn₂ : IsNorm Red B) (hn₃ : IsNorm Red x) : IsNorm Red (DCC (Λ A B x)) := fun ⟨_, h⟩ =>
  match h with
  | .point 0 hn h => hn₁ ⟨_, h⟩
  | .point 1 hn h => hn₂ ⟨_, h⟩
  | .point 2 hn h => hn₃ ⟨_, h⟩

def eval_is_norm (hn₁ : IsNorm Red A) (hn₂ : IsNorm Red B) (hn₃ : IsNorm Red x) : IsNorm Red (DCC (Eval A B x)) := fun ⟨_, h⟩ =>
  match h with
  | .point 0 hn h => hn₁ ⟨_, h⟩
  | .point 1 hn h => hn₂ ⟨_, h⟩
  | .point 2 hn h => hn₃ ⟨_, h⟩

def curr'_is_norm (hn₁ : IsNorm Red A) (hn₂ : IsNorm Red B) (hn₃ : IsNorm Red x) : IsNorm Red (DCC (!Λ A B x)) := fun ⟨_, h⟩ =>
  match h with
  | .point 0 hn h => hn₁ ⟨_, h⟩
  | .point 1 hn h => hn₂ ⟨_, h⟩
  | .point 2 hn h => hn₃ ⟨_, h⟩

def comp_is_norm (hn₁ : IsNorm Red x) (hn₂ : IsNorm Red y) : IsNorm Red (DCC (∘ x y)) := fun ⟨_, h⟩ =>
  match h with
  | .point 0 hn h => hn₁ ⟨_, h⟩
  | .point 1 hn h => hn₂ ⟨_, h⟩

open Dsl in
def pi_is_norm₀ (hn₁ : IsNorm Red B) (hn₂ : IsNorm Red C) : IsNorm Red (DCC (Π B C)) := fun ⟨_, h⟩ =>
  match h with
  | (.point 0 hn h) => hn₁ ⟨_, h⟩
  | (.point 1 hn h) => hn₂ ⟨_, h⟩

open Dsl in
def pi_is_norm (hn₁ : IsNorm Red B) (hn₂ : IsNorm Red C) (hn₃ : IsNorm Red x) : IsNorm Red (DCC ((Π B C) x)) := fun ⟨_, h⟩ =>
  match h with
  | .congrFun (.point 0 hn h) => hn₁ ⟨_, h⟩
  | .congrFun (.point 1 hn h) => hn₂ ⟨_, h⟩
  | .congrArg h => hn₃ ⟨_, h⟩

open Dsl in
def quot_is_norm (hn₁ : IsNorm Red B) (hn₂ : IsNorm Red x) : IsNorm Red (DCC (`B x)) := fun ⟨_, h⟩ =>
  match h with
  | .point 0 hn h => hn₁ ⟨_, h⟩
  | .point 1 hn h => hn₂ ⟨_, h⟩

open Dsl in
@[grind .] theorem sigma_is_norm (hn₁ : IsNorm Red A) (hn₂ : IsNorm Red B) : IsNorm Red (DCC (Σ A B)) := fun ⟨_, h⟩ =>
  match h with
  | (.point 0 hn h) => hn₁ ⟨_, h⟩
  | (.point 1 hn h) => hn₂ ⟨_, h⟩

open Dsl in
@[grind .] theorem sigma'_is_norm (hn₁ : IsNorm Red A) (hn₂ : IsNorm Red B) : IsNorm Red (DCC (Σ' A B)) := fun ⟨_, h⟩ =>
  match h with
  | (.point 0 hn h) => hn₁ ⟨_, h⟩
  | (.point 1 hn h) => hn₂ ⟨_, h⟩

open Dsl in
@[grind .] theorem arr_is_norm (hn₁ : IsNorm Red A) (hn₂ : IsNorm Red B) : IsNorm Red (DCC (→ A B)) := fun ⟨_, h⟩ =>
  match h with
  | .congrFun (.point n hlt h) => by
    simp [point_arity] at hlt
    match n with
    | 0 =>
      simp [points, Vector.get] at h
      match h with
      | .point 0 hn h =>
        nomatch h
      | .point 1 hn h => exact hn₁ ⟨_, h⟩
    | 1 =>
      simp [points, Vector.get] at h
      match h with
      | .point 0 hn h =>
        simp [points, Vector.get] at h
        nomatch h
      | .point 1 hn h =>
        simp [points, Vector.get] at h
        match h with
        | .point 0 hn h => exact hn₁ ⟨_, h⟩
        | .point 1 hn h => exact hn₂ ⟨_, h⟩
  | .congrArg h => nomatch h

namespace Judge

set_option maxHeartbeats 20000000000 in
def complete (h : Judge e τ) : e.infer = .ok ⟨τ, h⟩ := by
  induction h <;> (dsimp [infer]; try (dcc_aesop' [reduce]))

def unique (h₁ : Judge e τ₁) (h₂ : Judge e τ₂) : τ₁ = τ₂ := by
  have heq₁ := h₁.complete
  have heq₂ := h₂.complete
  grind

def is_norm {e τ : Expr} (h : Judge e τ) : IsNorm Red τ := by
  induction h
  any_goals (
    focus
    try (
      intro ⟨_, h⟩
      cases h
      grind)
    done)
  any_goals (
    focus
    apply RedNorm.is_norm
    assumption)
  case quot => exact arr_is_norm (RedNorm.is_norm (by assumption)) (by assumption)
  case eval =>
    expose_names
    have hn_A := a_4.is_norm
    have hn_B := a_5.is_norm
    have hn_C : IsNorm Red C := fun ⟨_, h⟩ => a_ih_2 ⟨_, .congrFun (.point 1 (by grind) (.point 1 (by point_arity) (.point 1 (by change 1 < (B'.pi C).point_arity; point_arity) h)))⟩
    exact pi_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (sigma_is_norm hn_A hn_B)) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (eval_is_norm hn_A hn_B hn_C)) (fun ⟨_, h⟩ => nomatch h)
  case id =>
    exact arr_is_norm (RedNorm.is_norm (by assumption)) (RedNorm.is_norm (by assumption))
  case unbox =>
    apply arr_is_norm
    · intro ⟨_, h⟩
      match h with
      | .point 0 hn h => exact RedNorm.is_norm (by assumption) ⟨_, h⟩
    · exact RedNorm.is_norm (by assumption)
  case box => exact (fun ⟨_, .point 0 hn h⟩ => by dcc_aesop' [force_reduce])
  case sigma' =>
    expose_names
    have ⟨hn₁, _⟩ := a_1.is_norm (by assumption)
    exact arr_is_norm (bang_is_norm hn₁) (fun ⟨_, h⟩ => nomatch h)
  case comp =>
    expose_names
    exact pi_is_norm
      (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (Arrow.is_norm a_1 a_ih).1)
      (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (comp_is_norm (fun ⟨_, h⟩ => a_ih_1 ⟨_, .congrFun (.point 1 (by grind) (.point 1 (by point_arity) h))⟩) a_3.is_norm))
      (fun ⟨_, h⟩ => nomatch h)
  case fmap =>
    expose_names
    have hn₁ : IsNorm Red f_A := fun ⟨_, h⟩ => a_ih ⟨_, .congrFun (.point 0 (by grind) h)⟩
    have hn₂ : IsNorm Red f_B := fun ⟨_, h⟩ => a_ih ⟨_, .congrFun (.point 1 (by grind) h)⟩
    have hn₃ : IsNorm Red x_A := fun ⟨_, h⟩ => a_ih ⟨_, .congrArg h⟩
    exact pi_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (bang_is_norm a_1.is_norm)) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (map_is_norm a_2.is_norm)) (fun ⟨_, h⟩ => nomatch h)
  case map =>
    expose_names
    have ⟨hn_A, _⟩ := a_1.is_norm a_ih
    exact pi_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (bang_is_norm hn_A)) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (quot_is_norm (bang_is_norm hn_A) (fun ⟨_, h⟩ => nomatch h))) (fun ⟨_, h⟩ => nomatch h)
  case swap =>
    expose_names
    exact arr_is_norm (sigma_is_norm a_2.is_norm (quot_is_norm a_2.is_norm a_3.is_norm)) (sigma_is_norm a_3.is_norm (quot_is_norm a_3.is_norm a_2.is_norm))
  case refl =>
    expose_names
    have hn_δ := a_1.is_norm
    exact pi_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (bang_is_norm hn_δ)) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (pi_is_norm₀ (map_is_norm a_2.is_norm) (eql_is_norm a_2.is_norm))) (fun ⟨_, h⟩ => nomatch h)
  case eql =>
    unfold eql.type
    expose_names
    have ⟨hn_δ, _⟩ := Arrow.is_norm a_1 (by assumption)
    exact pi_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (bang_is_norm (by assumption))) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (pi_is_norm₀ (map_is_norm (RedNorm.is_norm (by assumption))) (curr'_is_norm (by assumption) (RedNorm.is_norm (by assumption)) (quot_is_norm (bang_is_norm (sigma_is_norm (by assumption) (RedNorm.is_norm (by assumption)))) (fun ⟨_, h⟩ => nomatch h))))) (fun ⟨_, h⟩ => nomatch h)
  case eq_mk =>
    unfold eq_mk.type
    expose_names
    have ⟨hn_δ, _⟩ := Arrow.is_norm a_1 (by assumption)
    exact pi_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (by assumption)) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (pi_is_norm₀ (RedNorm.is_norm (by assumption)) (curr_is_norm (by assumption) (RedNorm.is_norm (by assumption)) (pi_is_norm₀ (comp_is_norm (RedNorm.is_norm (by assumption)) (fst_is_norm (RedNorm.is_norm (by assumption)))) (curr_is_norm (sigma_is_norm (by assumption) (RedNorm.is_norm (by assumption))) (comp_is_norm (RedNorm.is_norm (by assumption)) (fst_is_norm (RedNorm.is_norm (by assumption)))) (quot_is_norm (sigma_is_norm (sigma_is_norm (by assumption) (RedNorm.is_norm (by assumption))) (comp_is_norm (RedNorm.is_norm (by assumption)) (fst_is_norm (RedNorm.is_norm (by assumption))))) (fun ⟨_, h⟩ => nomatch h))))))) (fun ⟨_, h⟩ => nomatch h)
  case fstc =>
    have hn_A := ArrowSort.is_norm (by assumption)
    exact arr_is_norm (sigma_is_norm hn_A (RedNorm.is_norm (by assumption))) hn_A
  case sndc =>
    unfold sndc.type
    have hn_A := ArrowSort.is_norm (by assumption)
    exact pi_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (sigma_is_norm hn_A (RedNorm.is_norm (by assumption)))) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (comp_is_norm (RedNorm.is_norm (by assumption)) (fst_is_norm (RedNorm.is_norm (by assumption))))) (fun ⟨_, h⟩ => nomatch h)
  case mk =>
    expose_names
    exact sigma_is_norm a_ih (RedNorm.is_norm (by assumption))
  case pair =>
    expose_names
    exact pi_is_norm
      (quot_is_norm
        (by grind)
        (bang_is_norm (fun ⟨_, h⟩ => a_ih ⟨_, .congrFun (.point 0 (by grind) (.point 1 (by point_arity) h))⟩)))
      (quot_is_norm (by grind) (sigma'_is_norm (fun ⟨_, h⟩ => a_ih ⟨_, .congrFun (.point 1 (by point_arity) (.point 1 (by point_arity) h))⟩) a_2.is_norm))
      (by grind)
  case curr =>
    expose_names
    unfold curr.type
    have ⟨hn₁, hn₂, hn₃⟩ := a_5.is_norm (by assumption)
    exact pi_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) a_2.is_norm) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (pi_is_norm₀ hn₂ (curr_is_norm a_2.is_norm hn₂ hn₃))) (fun ⟨_, h⟩ => nomatch h)
  case ind_bool =>
    expose_names
    have ⟨hn_A, _⟩ := a_1.is_norm (by assumption)
    exact pi_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) hn_A) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (pi_is_norm₀ (quot_is_norm hn_A (fun ⟨_, h⟩ => nomatch h)) (RedNorm.is_norm (by assumption)))) (fun ⟨_, h⟩ => nomatch h)
  case ind_bot =>
    expose_names
    have ⟨hn_A, _⟩ := a_1.is_norm a_ih
    exact pi_is_norm (quot_is_norm (by grind) hn_A) (quot_is_norm (by grind) (pi_is_norm₀ (quot_is_norm hn_A (by grind)) a_3.is_norm)) (by grind)
  case pi =>
    expose_names
    have hn_A := a_1.is_norm
    exact arr_is_norm hn_A (by grind)
  case curr' =>
    expose_names
    have ⟨hn₁, hn₂, hn₃⟩ := a_5.is_norm (by assumption)
    exact pi_is_norm (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (bang_is_norm a_2.is_norm)) (quot_is_norm (fun ⟨_, h⟩ => nomatch h) (pi_is_norm₀ (map_is_norm hn₂) (curr'_is_norm a_2.is_norm hn₂ hn₃))) (fun ⟨_, h⟩ => nomatch h)

end Judge

end Expr
