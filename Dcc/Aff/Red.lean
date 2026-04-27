import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Size

namespace Expr

inductive RedAff : Expr → Expr → Prop
  | subst₁   : RedAff (DCC (Subst(x, Fst(f_β)) env ⟦β⟧(y, z))) (DCC (x env y))
  | snd'     : RedAff (DCC (Snd'(_δ, _τ) ⟦β⟧(a, b))) b
  | quot     : RedAff (DCC (`(β, x) y)) x
  | id       : RedAff (DCC (Id(α) x)) x
  | app'     : RedAff (DCC (App'(_α, _β) ⟦δ⟧(env, ⟦β⟧(x, y)))) (DCC (x y))
  | fst      : RedAff (DCC (Fst(_α) _env ⟦β⟧(a, b))) a
  | snd      : RedAff (DCC (Snd(_α) _env ⟦β⟧(a, b))) b
  | comp     : RedAff (DCC ((x ∘ y) z)) (DCC (x (y z)))
  | curr     : RedAff (DCC (Λ(α, β, x) y z)) (DCC (x ⟦β⟧(y, z)))
  | sigl     : RedAff x x' → RedAff (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x', y))
  | sigr     : RedAff y y' → RedAff (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x, y'))
  | congrFun : RedAff f f' → RedAff (DCC (f x)) (DCC (f' x))
  | congrArg : RedAff x x' → RedAff (DCC (f x)) (DCC (f x'))

def step? (e : Expr) : Option ((e' : Expr) × (PULift.{1, 0} (RedAff e e'))) :=
  match e with
  | (DCC (Subst(_x, Fst(_f_β)) _env ⟦_β⟧(_y, _z))) => .some ⟨_, ⟨.subst₁⟩⟩
  | (DCC (Snd'(_α, _τ) ⟦_β⟧(_a, b)))               => .some ⟨b, ⟨.snd'⟩⟩
  | (DCC (`(_β, x) _y))                            => .some ⟨x, ⟨.quot⟩⟩
  | (DCC (Id(_α) x))                               => .some ⟨x, ⟨.id⟩⟩
  | (DCC (App'(_α, _β) ⟦_δ⟧(_env, ⟦_β₂⟧(_x, _y)))) => .some ⟨_, ⟨.app'⟩⟩
  | (DCC (Fst(_α) _env ⟦_γ⟧(a, _b)))               => .some ⟨a, ⟨.fst⟩⟩
  | (DCC (Snd(_α) _env ⟦_γ⟧(_a, b)))               => .some ⟨b, ⟨.snd⟩⟩
  | (DCC ((x ∘ y) z))                              => .some ⟨(DCC (x (y z))), ⟨.comp⟩⟩
  | (DCC (Λ(_α, β, x) y z))                        => .some ⟨(DCC (x ⟦β⟧(y, z))), ⟨.curr⟩⟩
  | DCC ⟦β⟧(x, y) =>
    match x.step?, y.step? with
    | .some ⟨x', ⟨h₁⟩⟩, _ => .some ⟨(DCC ⟦β⟧(x', y)), ⟨.sigl h₁⟩⟩
    | _, .some ⟨y', ⟨h₁⟩⟩ => .some ⟨(DCC ⟦β⟧(x, y')), ⟨.sigr h₁⟩⟩
    | _, _ => .none
  | DCC (f x) =>
    match f.step?, x.step? with
    | .some ⟨f', ⟨h₁⟩⟩, _ => .some ⟨(DCC (f' x)), ⟨.congrFun h₁⟩⟩
    | _, .some ⟨x', ⟨h₁⟩⟩ => .some ⟨(DCC (f x')), ⟨.congrArg h₁⟩⟩
    | _, _ => .none
  | _ => .none

@[simp] instance RedAff.instRedRel : RedRel RedAff Size where
  run := step?

@[simp] instance RedAff.instCongruent : Congruent RedAff where

open Congruent in theorem RedAff.conf (h₁ : RedAff A B) (h₂ : RedAff A C) : ∃ D, RedAff.instRedRel.ReflTrans B D ∧ RedAff.instRedRel.ReflTrans C D := by
  induction h₁ generalizing C with
  | subst₁ =>
    cases h₂ with
    | subst₁ => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, congrFun' (congrArg' (.single h)), .single .subst₁⟩
    | congrArg h => cases h with
      | sigl h => exact ⟨_, congrArg' (.single h), .single .subst₁⟩
      | sigr h => exact ⟨_, .refl, .single .subst₁⟩
  | quot =>
    cases h₂ with
    | quot => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .refl, .single .quot⟩
  | id =>
    cases h₂ with
    | id => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single h, .single .id⟩
  | sigl h ih =>
    cases h₂ with
    | sigl h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, sigl' h₁, sigl' h₂⟩
    | sigr h =>
      exact ⟨_, .single (.sigr h), .single (.sigl (by assumption))⟩
  | sigr h ih =>
    cases h₂ with
    | sigl h =>
      exact ⟨_, .single (.sigl h), .single (.sigr (by assumption))⟩
    | sigr h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, sigr' h₁, sigr' h₂⟩
  | app' =>
    cases h₂ with
    | app' => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h =>
      cases h with
      | sigl h =>
        exact ⟨_, .refl, .single .app'⟩
      | sigr h =>
        cases h with
        | sigl h => exact ⟨_, .single (.congrFun h), .single .app'⟩
        | sigr h => exact ⟨_, .single (.congrArg h), .single .app'⟩
  | fst =>
    cases h₂ with
    | fst => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .refl, .single .fst⟩
    | congrArg h =>
      cases h with
      | sigl h =>
        exact ⟨_, .single h, .single .fst⟩
      | sigr h =>
        exact ⟨_, .refl, .single .fst⟩
  | snd =>
    cases h₂ with
    | snd => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .refl, .single .snd⟩
    | congrArg h =>
      cases h with
      | sigl h =>
        exact ⟨_, .refl, .single .snd⟩
      | sigr h =>
        exact ⟨_, .single h, .single .snd⟩
  | snd' =>
    cases h₂ with
    | snd' => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h =>
      cases h with
      | sigl h =>
        exact ⟨_, .refl, .single .snd'⟩
      | sigr h =>
        exact ⟨_, .single h, .single .snd'⟩
  | comp =>
    cases h₂ with
    | comp => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single (.congrArg (.congrArg (by assumption))), .single .comp⟩
  | curr =>
    cases h₂ with
    | curr => exact ⟨_, .refl, .refl⟩
    | congrFun h =>
      cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single (.congrArg (.sigl h)), .single .curr⟩
    | congrArg h => exact ⟨_, .single (.congrArg (.sigr (by assumption))), .single .curr⟩
  | congrFun h_r ih =>
    cases h₂
    case subst₁ =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .subst₁, congrFun' (congrArg' (.single h))⟩
    case fst =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .fst, .refl⟩
    case snd =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .snd, .refl⟩
    case snd' | quot | id | comp => cases h_r
    case app' => cases h_r
    case curr =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .curr, .single (.congrArg (.sigl (by assumption)))⟩
    case congrFun f f' x f'' h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, congrFun' h₁, congrFun' h₂⟩
    case congrArg f f' x x'' h_x =>
      exact ⟨_, congrArg' (.single h_x), congrFun' (.single h_r)⟩
  | congrArg h_r ih =>
    cases h₂ with
    | subst₁ => cases h_r with
      | sigl h => exact ⟨_, .single .subst₁, congrArg' (.single h)⟩
      | sigr h => exact ⟨_, .single .subst₁, .refl⟩
    | quot => exact ⟨_, .single .quot, .refl⟩
    | id => exact ⟨_, .single .id, .single h_r⟩
    | app' =>
      cases h_r with
      | sigl h => exact ⟨_, .single .app', .refl⟩
      | sigr h =>
        cases h with
        | sigl h => exact ⟨_, .single .app', .single (.congrFun h)⟩
        | sigr h => exact ⟨_, .single .app', .single (.congrArg h)⟩
    | fst =>
      cases h_r with
      | sigl h => exact ⟨_, .single .fst, .single h⟩
      | sigr h =>  exact ⟨_, .single .fst, .refl⟩
    | snd =>
      cases h_r with
      | sigl h => exact ⟨_, .single .snd, .refl⟩
      | sigr h => exact ⟨_, .single .snd, .single h⟩
    | snd' =>
      cases h_r with
      | sigl h => exact ⟨_, .single .snd', .refl⟩
      | sigr h => exact ⟨_, .single .snd', .single h⟩
    | comp  => exact ⟨_, .single .comp, congrArg' (congrArg' (.single (by assumption)))⟩
    | curr  => exact ⟨_, .single .curr, congrArg' (sigr' (.single (by assumption)))⟩
    | congrFun => exact ⟨_, congrFun' (.single (by assumption)), congrArg' (.single (by assumption))⟩
    | congrArg h =>
      have ⟨D, h₁, h₂⟩ := ih h
      exact ⟨_, congrArg' h₁, congrArg' h₂⟩

@[simp] instance RedAff.instConf : Confluent RedAff := ⟨RedAff.conf⟩

@[simp] instance instConfRedAffTrans : Confluent RedAff (m := Relation.ReflTransGen) := RedAff.instRedRel.globally_confluent

def semi_complete {A B : Expr} (hr : A.RedAff B) : ∃ B', ∃ (h : A.RedAff B'), (step? A) = .some ⟨B', ⟨h⟩⟩ := by
  change ∃ _, ∃ _, (step? _) = .some _
  unfold step?
  split
  repeat exact ⟨_, (RedAff.instRedRel.sound rfl).down, rfl⟩
  case h_10 =>
    cases hr with
    | sigl h_x =>
      have ⟨_, hrx', heq'⟩ := semi_complete h_x
      exact ⟨_, .sigl (by assumption), by rw [heq']⟩
    | sigr h_y =>
      rename_i x y _
      have ⟨_, hry', heq'⟩ := semi_complete h_y
      match x.step? with
      | .none =>
        exact ⟨_, .sigr (by assumption), by rw [heq']⟩
      | .some ⟨_, ⟨h_x'⟩⟩ =>
        exact ⟨_, .sigl (by assumption), by rw [heq']⟩
  case h_11 =>
    cases hr with
    | subst₁ =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl).elim
    | congrFun h =>
      have ⟨_, hrf, heqf⟩ := semi_complete h
      exact ⟨_, .congrFun hrf, by rw [heqf]⟩
    | congrArg h =>
      have ⟨_, hrx, heqx⟩ := semi_complete h
      rename_i f x _ _ _ _ _ _ _ _ _ _ _
      match f.step? with
      | .none => exact ⟨_, .congrArg hrx, by simp_all⟩
      | .some ⟨_, ⟨hrf⟩⟩ => exact ⟨_, .congrFun hrf, by simp_all⟩
    | snd | fst =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ rfl rfl rfl rfl rfl).elim
    | snd'  =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ rfl rfl rfl rfl rfl).elim
    | app' =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl).elim
    | quot | id | comp => simp_all
    | curr =>
      rename_i h
      exact (h _ _ _ _ rfl).elim
  case h_12 =>
    simp_all
    cases hr <;> aesop

@[simp] instance RedAff.instSemicomplete : SemiComplete RedAff := ⟨semi_complete⟩

@[simp] instance instComplete : Complete (Relation.ReflTransGen RedAff) (P := IsNorm RedAff) := RedAff.instRedRel.instComplete

end Expr
