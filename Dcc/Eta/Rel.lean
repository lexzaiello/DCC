import Dcc.Eta.Ast
import Mathlib.Data.Option.Basic

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
