import Dcc.Aff.Complete
import Mathlib.Tactic

universe u
variable {τ : Type u}

/-
TOOD:
- hole unification

Unification runs on β-normal forms.
Normalize in Unify recursion.
-/

namespace GenericExpr

/-
((Unify τ₁ τ₂) (? x₁) (? x₂))
-/
--def unif_hole

/-
(Sum.Ind motive case_true case_false) (,... True x) = ((case_true x) : motive True x)
(Sum.Ind motive case_true case_false) (,... False x) = ((case_false x) : motive False x)
-/
open Dsl in
abbrev Sum.Ind (B motive case_true case_false : GenericExpr τ) : GenericExpr τ :=
  (DCC? (Eval Bool B ((Bool.Ind (`⊤ (Π B motive)) (`⊤ (`Bool case_true)) (`⊤ (`Bool case_false))) ∗)))

/-
(× A B) := (Σ (`A B))
-/
open Dsl in
abbrev Prod (A B : GenericExpr τ) : GenericExpr τ :=
  (DCC? (Σ (`A B)))

open Dsl in
abbrev Prod.mk (x y : GenericExpr τ) : GenericExpr τ :=
  (DCC? (,(` (? x) (? y)) x y))

open Dsl in
abbrev Sum (A B : GenericExpr τ) : GenericExpr τ :=
  (DCC? (Σ ((Bool.Ind (`⊤ (`Bool (? A))) (`⊤ (`Bool A)) (`⊤ (`Bool B))) ∗)))

/-
(Bool.Cases case₁ case₂) True  = (case₁ : motive₁)
(Bool.Cases case₁ case₂) False = (case₂ : motive₂)
-/
open Dsl in
abbrev Bool.Cases (case₁ case₂ : GenericExpr τ) : GenericExpr τ :=
  (DCC? ((Bool.Ind (Bool.Ind (`⊤ (`Bool (? (? case₁))))
                             (`⊤ (`Bool (? case₁)))
                             (`⊤ (`Bool (? case₂))))
                   (`⊤ (`Bool case₁))
                   (`⊤ (`Bool case₂)))
         ∗))

syntax "(⊕" gen_dcc+ ")"           : gen_dcc
syntax "(×" gen_dcc+ ")"           : gen_dcc
syntax "(×.mk" gen_dcc+ ")"        : gen_dcc
syntax "(⊕.Ind" gen_dcc+ ")"       : gen_dcc
syntax "(⊕.CasesAnd" gen_dcc+ ")"  : gen_dcc
syntax "(Bool.Cases" gen_dcc+ ")"  : gen_dcc

macro_rules
  | `(DCC[$loc] (⊕ $A:gen_dcc $B:gen_dcc)) => `(Sum (DCC[$loc] $A) (DCC[$loc] $B))
  | `(DCC[$loc] (× $A:gen_dcc $B:gen_dcc)) => `(Prod (DCC[$loc] $A) (DCC[$loc] $B))
  | `(DCC[$loc] (×.mk $x:gen_dcc $y:gen_dcc)) => `(Prod.mk (DCC[$loc] $x) (DCC[$loc] $y))
  | `(DCC[$loc] (Bool.Cases $case_x:gen_dcc $case_y:gen_dcc)) => `(Bool.Cases (DCC[$loc] $case_x) (DCC[$loc] $case_y))
  | `(DCC[$loc] (⊕.Ind $B:gen_dcc $motive:gen_dcc $case_true:gen_dcc $case_false:gen_dcc)) => `(Sum.Ind (DCC[$loc] $B) (DCC[$loc] $motive) (DCC[$loc] $case_true) (DCC[$loc] $case_false))

/-
(⊕.CasesAnd (,... True x) (,... True y) both_true inl_false inl_false) = both_true (×.mk x y)
(⊕.CasesAnd (,... False x) _ both_true inl_false inl_false) = inl_false x
(⊕.CasesAnd (,... True x) (,... False y) both_true inl_false inl_false) = inr_false x
-/
open Dsl in
abbrev Sum.CasesAnd (const_motive τ₁ τ₂ τ₃ τ₄ both_true inl_false inr_false x y : GenericExpr τ) : GenericExpr τ :=
  (DCC? ((⊕.Ind (Bool.Cases τ₁ τ₂)
                (Bool.Cases (`τ₁ const_motive) (`τ₂ const_motive))
                ((⊕.Ind (Bool.Cases τ₃ τ₄)
                        (Bool.Cases (`τ₃ const_motive) (`τ₄ const_motive))
                        (Λ τ₂ (`τ₄ τ₁) (∘ both_true (Swap τ₂ τ₂)))
                        (Λ τ₄ (`τ₄ τ₁) (∘ inr_false (Fst (`τ₄ τ₁)))))
                 y)
                inl_false)
         x))

macro_rules
  | `(DCC[$loc] (⊕.CasesAnd $motive:gen_dcc $τ₁:gen_dcc $τ₂:gen_dcc $τ₃:gen_dcc $τ₄:gen_dcc $both_true:gen_dcc $inl_false:gen_dcc $inr_false:gen_dcc $x:gen_dcc $y:gen_dcc)) => `(Sum.CasesAnd (DCC[$loc] $motive) (DCC[$loc] $τ₁) (DCC[$loc] $τ₂) (DCC[$loc] $τ₃) (DCC[$loc] $τ₄) (DCC[$loc] $both_true) (DCC[$loc] $inl_false) (DCC[$loc] $inr_false) (DCC[$loc] $x) (DCC[$loc] $y))

open Dsl in
def mk_hole (B₁ C₁ x₁ B₂ C₂ x₂ : GenericExpr τ) : GenericExpr τ :=
  .hole ((DCC? ((Π B₁ C₁) x₁)).max_hole + (DCC? ((Π B₂ C₂) x₂)).max_hole)

open Dsl in
def unif_fn (u v : Level) (B₁ C₁ x₁ B₂ C₂ x₂ : GenericExpr τ) (h_unif_dom : GenericExpr τ) (h_unif_cod : GenericExpr τ) : GenericExpr τ :=
  let hole := (mk_hole B₁ C₁ x₁ B₂ C₂ x₂)

  let goal := DCC? (⊕ (≃ ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)) (≃ (≃ ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)) ⊥))

  let conv_prod  := DCC? (× ((((Π B₁ C₁) x₁) : Sort u) → ((Π B₂ C₂) x₂)) ((((Π B₂ C₂) x₂) : Sort u) → ((Π B₁ C₁) x₁)))
  let equiv_prod := (DCC? (× (≃ (B₁ x₁) (B₂ x₂)) (≃ (C₁ x₁ hole) (C₂ x₂ hole))))

  let t_fn₁ := DCC? ((Π B₁ C₁) x₁)
  let t_fn₂ := DCC? ((Π B₂ C₂) x₂)

  DCC? (⊕.CasesAnd goal
                   (≃ (B₁ x₁) (B₂ x₂))
                   (≃ (≃ (B₁ x₁) (B₂ x₂)) ⊥)
                   (≃ (C₁ x₁ hole) (C₂ x₂ hole))
                   (≃ (≃ (C₁ x₁ hole) (C₂ x₂ hole)) ⊥)
                   (∘ ((Λ Bool (`Bool (≃ ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂))) (Id goal)) True)
                      (≃.mk (Λ equiv_prod
                               (`equiv_prod t_fn₁)
                               (Λ (× equiv_prod t_fn₁)
                                  (`(× equiv_prod t_fn₁) (B₂ x₂))
                                  (≃.1.apply ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)))) -- Have ((×.mk (≃ (B₁ x₁) (B₂ x₂)) (≃ (C₁ x₁ hole) (C₂ x₂ hole)), f), x)
                            (Λ equiv_prod
                               (`equiv_prod t_fn₂)
                               (Λ (× equiv_prod t_fn₂)
                                  (`(× equiv_prod t_fn₁) (B₁ x₁))
                                  (≃.2.apply ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂))))
                            (`conv_prod ((refl (Id Sort u)) (& ((Π B₁ C₁) x₁))))
                            (`conv_prod ((refl (Id Sort v)) (& ((Π B₂ C₂) x₂))))))
                   (≃.mk (∘ (Λ (((≃ (B₁ x₁) (B₂ x₂)) : (? (≃ (B₁ x₁) (B₂ x₂)))) → ⊥)
                               (`(((≃ (B₁ x₁) (B₂ x₂)) : (? (≃ (B₁ x₁) (B₂ x₂)))) → ⊥) (≃ t_fn₁ t_fn₂))
                               (∘ (∘ (≃.dom ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂))
                                     (Λ (≃ (B₁ x₁) (B₂ x₂))
                                        (`(≃ (B₁ x₁) (B₂ x₂)) (((≃ (B₁ x₁) (B₂ x₂)) : (? (≃ (B₁ x₁) (B₂ x₂)))) → ⊥))
                                        (∘ (Eval (((≃ (B₁ x₁) (B₂ x₂)) : (? (≃ (B₁ x₁) (B₂ x₂)))) → ⊥)
                                                 (`(((≃ (B₁ x₁) (B₂ x₂)) : (? (≃ (B₁ x₁) (B₂ x₂)))) → ⊥) (≃ (B₁ x₁) (B₂ x₂)))
                                                 (Id (((≃ (B₁ x₁) (B₂ x₂)) : (? (≃ (B₁ x₁) (B₂ x₂)))) → ⊥)))
                                           (Swap (≃ (B₁ x₁) (B₂ x₂)) (`(≃ (B₁ x₁) (B₂ x₂)) (((≃ (B₁ x₁) (B₂ x₂)) : (? (≃ (B₁ x₁) (B₂ x₂)))) → ⊥))))))
                                  (Swap (((≃ (B₁ x₁) (B₂ x₂)) : (? (≃ (B₁ x₁) (B₂ x₂)))) → ⊥) (≃ t_fn₁ t_fn₂))))
                            (≃.1 (≃ (B₁ x₁) (B₂ x₂)) ⊥))
                         (⊥.Ind (`(≃ (≃ (B₁ x₁) (B₂ x₂)) ⊥) (`⊥ ⊥)))
                         (`(≃ (≃ (B₁ x₁) (B₂ x₂)) ⊥) ((refl (Id (? (≃ ((Π B₁ C₁) x₁) ((Π B₁ C₂) x₂))))) (& (≃ ((Π B₁ C₁) x₁) ((Π B₁ C₂) x₂)))))
                         (`(≃ (≃ (B₁ x₁) (B₂ x₂)) ⊥) ((refl (Id (Sort 0))) (& ⊥)))) -- (≃ (B₁ x₁) (B₂ x₂)) ≃ ⊥ ⊢ (≃ (≃ ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)) ⊥)
                   (≃.mk (∘ (Λ (((≃ (C₁ x₁ hole) (C₂ x₂ hole)) : (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) → ⊥)
                               (`(((≃ (C₁ x₁ hole) (C₂ x₂ hole)) : (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) → ⊥) (≃ t_fn₁ t_fn₂))
                               (∘ (∘ (≃.cod ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂))
                                     (Λ (≃ (C₁ x₁ hole) (C₂ x₂ hole))
                                        (`(≃ (C₁ x₁ hole) (C₂ x₂ hole)) (((≃ (C₁ x₁ hole) (C₂ x₂ hole)) : (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) → ⊥))
                                        (∘ (Eval (((≃ (C₁ x₁ hole) (C₂ x₂ hole)) : (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) → ⊥)
                                                 (`(((≃ (C₁ x₁ hole) (C₂ x₂ hole)) : (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) → ⊥) (≃ (C₁ x₁ hole) (C₂ x₂ hole)))
                                                 (Id (((≃ (C₁ x₁ hole) (C₂ x₂ hole)) : (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) → ⊥)))
                                           (Swap (≃ (C₁ x₁ hole) (C₂ x₂ hole)) (`(≃ (C₁ x₁ hole) (C₂ x₂ hole)) (((≃ (C₁ x₁ hole) (C₂ x₂ hole)) : (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) → ⊥))))))
                                  (Swap (((≃ (C₁ x₁ hole) (C₂ x₂ hole)) : (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) → ⊥) (≃ t_fn₁ t_fn₂))))
                            (≃.1 (≃ (B₁ x₁) (B₂ x₂)) ⊥))
                         (⊥.Ind (`(≃ (≃ (C₁ x₁ hole) (C₂ x₂ hole)) ⊥) (`⊥ ⊥)))
                         (`(≃ (≃ (C₁ x₁ hole) (C₂ x₂ hole)) ⊥) ((refl (Id (? (≃ ((Π B₁ C₁) x₁) ((Π B₁ C₂) x₂))))) (& (≃ ((Π B₁ C₁) x₁) ((Π B₁ C₂) x₂)))))
                         (`(≃ (≃ (C₁ x₁ hole) (C₂ x₂ hole)) ⊥) ((refl (Id (Sort 0))) (& ⊥)))) -- ((C₁ x₁ hole) ≃ (C₂ x₂ hole)) ≃ ⊥
                   h_unif_dom
                   h_unif_cod)

/-
A ≃ A. This is due to Id.
-/
open Dsl in
abbrev unif_refl (τ_A₁ τ_A₂ A : GenericExpr τ) : GenericExpr τ :=
  (DCC? (,(`(Bool) (≃ A A)) (≃.mk (`⊤ (Id A)) (`⊤ (Id A)) (`⊤ ((refl (Id τ_A₁)) (&A))) (`⊤ ((refl (Id τ_A₂)) (&A)))) ∗))

/-
(Type u ≃ ⊥) ≃ ⊥
-/
open Dsl in
abbrev unif_bot_type (u : Level) : GenericExpr τ :=
  (DCC? (,(`Bool (≃ (≃ (Sort (u + 1)) ⊥) ⊥))
          False
          ((≃.mk (`⊤ (∘ ((Λ (Sort u + 1)
                         (`(Sort u + 1) ((Sort (u + 1) : Sort u + 2) → ⊥))
                         (∘ (Eval ((Sort (u + 1) : Sort u + 2) → ⊥)
                                  (`((Sort (u + 1) : Sort u + 2) → ⊥) (Sort u + 1))
                                  (Id ((Sort (u + 1) : Sort u + 2) → ⊥)))
                            (Swap (Sort u + 1) ((Sort u : Sort u + 1) → ⊥)))) (Sort u))
                      (≃.1 (Sort (u + 1)) ⊥))) -- (Type u ≃ ⊥), prove ⊥. Grab Type u → ⊥, plug in Sort u
              (⊥.Ind (`⊤ (`⊥ (≃ (Sort (u + 1)) ⊥)))) -- ⊤, ⊥, prove (Type u ≃ ⊥). Use ⊥.Ind
              (`⊤ ((refl (Id (Sort (u + 2)))) (& (Sort (u + 1)))))
              (`⊤ ((refl (Id (Sort 0))) (& ⊥))))
         ∗)))

/-
(Sort 0 ≃ ⊥) ≃ ⊥, this is provable because ⊤ inhabits Sort 0.
-/
open Dsl in
abbrev unif_bot_prop : GenericExpr τ :=
  (DCC? (,(`Bool (≃ (≃ (Sort 0) ⊥) ⊥))
          False
          ((≃.mk (`⊤ (∘ ((Λ (Sort 0)
                            (`(Sort 0) ((Sort 0 : Sort 1) → ⊥))
                            (∘ (Eval ((Sort 0 : Sort 1) → ⊥)
                                     (`((Sort 0 : Sort 1) → ⊥) Sort 0)
                                     (Id ((Sort 0 : Sort 1) → ⊥)))
                               (Swap (Sort 0) ((Sort 0 : Sort 1) → ⊥)))) ⊤)
                         (≃.1 (Sort 0) ⊥)))
                 (⊥.Ind (`⊤ (`⊥ (≃ (Sort 0) ⊥))))
                 (`⊤ ((refl (Id (Sort 1))) (& (Sort 0))))
                 (`⊤ ((refl (Id (Sort 0))) (& ⊥))))
          ∗)))

/-
Need some way to detect loop?

fun (x : B₂ x₂) => (≃.1 ... ... ...) ((Unify ? ? ) (C₁ x₁ ((A₂_to_A₁) x)) (C₂ x₂ x)) f ((A₂_to_A₁) x)

(≃.apply dom₂_to_dom₁ cod_x₁_to_cod_x₂) f x = (≃.1 ... ... ...) ((Unify ? ? ) (C₁ x₁ ((A₂_to_A₁) x)) (C₂ x₂ x)) f ((A₂_to_A₁) x)

Just run Unify and this separately?
Yes.

f is doing actual work.

(Subst ? ?) x = ((Unify ? ?)

Unify / Subst and normal reduction need to be completely separated.
-/

open Dsl in inductive IsUnify : (e : GenericExpr τ) → Type u
  | mk : IsUnify (DCC? (Unify A B X Y))

inductive ViewApp : (e : GenericExpr τ) → Type u
  | mk : ViewApp (DCC? (f x))

def view_app? (e : GenericExpr τ) : Option (ViewApp e) :=
  match e with
  | DCC? (_f _x) => .some .mk
  | _ => .none

def ViewApp.complete (h : ViewApp e) : view_app? e = .some h := by
  cases h
  simp [view_app?]

open Dsl in
inductive ViewUnify : (e : GenericExpr τ) → Type u
  | refl   : ViewUnify (DCC? (Unify A B X X))
  | pi     : (hneq : (DCC? ((Π B₁ C₁) x₁)) ≠  (DCC? ((Π B₂ C₂) x₂))) → ViewUnify (DCC? (Unify (Sort u) (Sort v) ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)))
  | prop   : ViewUnify (DCC? (Unify (Sort 1) (Sort 0) (Sort 0) ⊥))
  | type   : ViewUnify (DCC? (Unify (Sort (u + 2)) (Sort 0) (Sort (u + 1)) ⊥))
  | fn_cod : ViewUnify (DCC? ((≃.cod ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)) ((≃.mk f_to f_from h_id₁ h_id₂) (,B h₁ h₂))))
  | fn_dom : ViewUnify (DCC? ((≃.dom ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)) ((≃.mk f_to f_from h_id₁ h_id₂) (,B h₁ h₂))))

open Dsl in
def is_unif? (e : GenericExpr τ) : Option (IsUnify e) :=
  open Dsl in match e with
  | DCC? (Unify _A _B _X _Y) => .some .mk
  | _ => .none

def IsUnify.complete (h : IsUnify e) : is_unif? e = .some h := by
  cases h
  simp [is_unif?]

open Dsl in
def view_unif? [DecidableEq τ] (e : GenericExpr τ) : Option (ViewUnify e) :=
  match e with
  | DCC? ((≃.cod ((Π _B₁ _C₁) _x₁) ((Π _B₂ _C₂) _x₂)) ((≃.mk _f_to _f_from _h_id₁ _h_id₂) (,_B _h₁ _h₂))) => .some .fn_cod
  | DCC? ((≃.dom ((Π _B₁ _C₁) _x₁) ((Π _B₂ _C₂) _x₂)) ((≃.mk _f_to _f_from _h_id₁ _h_id₂) (,_B _h₁ _h₂))) => .some .fn_dom
  | DCC? (Unify A B X Y) =>
    if heq : X = Y then
      heq ▸ .some .refl
    else
      match heq₂ : DCC? (Unify A B X Y) with
      | DCC? (Unify (Sort _u) (Sort _v) ((Π _B₁ _C₁) _x₁) ((Π _B₂ _C₂) _x₂)) => .some (.pi (by grind))
      | DCC? (Unify (Sort 1) (Sort 0) (Sort 0) ⊥) => .some .prop
      | DCC? (Unify (Sort (u + 2)) (Sort 0) (Sort v) ⊥) =>
        if heq : v = u + 1 then
          heq ▸ .some .type
        else .none
      | _ => .none
  | _ => .none

def ViewUnify.complete {e : GenericExpr τ} [DecidableEq τ] (h : ViewUnify e) : view_unif? e = .some h := by
  cases h
  any_goals simp [view_unif?]
  case pi => grind

inductive RedUnify : (e : GenericExpr τ) → (e' : GenericExpr τ) → Prop
  | refl      : RedAffNorm (unif_refl A B X) ⟨e', hn⟩
    → RedUnify (open Dsl in (DCC? (Unify A B X X))) e'
  | fn        : (hr₁ : RedAffNorm (B₁.app x₁) ⟨τ₁, hn_τ₁⟩)
    → (hr₂ : RedAffNorm (B₂.app x₂) ⟨τ₂, hn_τ₂⟩)
    → (hr₃ : RedAffNorm (DCC? (C₁ x₁ #(mk_hole B₁ C₁ x₁ B₂ C₂ x₂))) ⟨τ₃, hn_τ₃⟩)
    → (hr₄ : RedAffNorm (DCC? (C₂ x₂ #(mk_hole B₁ C₁ x₁ B₂ C₂ x₂))) ⟨τ₄, hn_τ₄⟩)
    → (h_unif_dom : RedUnify (open Dsl in (DCC? (Unify (? τ₁) (? τ₂) τ₁ τ₂))) e₁)
    → (h_unif_cod : RedUnify (open Dsl in (DCC? (Unify (? τ₃) (? τ₄) τ₃ τ₄))) e₂)
    → RedAffNorm (unif_fn u v B₁ C₁ x₁ B₂ C₂ x₂ e₁ e₂) ⟨e', hn⟩
    → (hneq   : (open Dsl in (DCC? ((Π B₁ C₁) x₁))) ≠ (open Dsl in (DCC? ((Π B₂ C₂) x₂))))
    → RedUnify (open Dsl in (DCC? (Unify (Sort u) (Sort v) ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)))) e'
  | fn_dom    : RedAffNorm h₁ ⟨h₁', hn⟩ → RedUnify (open Dsl in (DCC? ((≃.dom ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)) ((≃.mk f_to f_from h_id₁ h_id₂) (,B h₁ h₂))))) h₁'
  | fn_cod    : RedAffNorm h₂ ⟨h₂', hn⟩ → RedUnify (open Dsl in (DCC? ((≃.cod ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)) ((≃.mk f_to f_from h_id₁ h_id₂) (,B h₁ h₂))))) h₂'
  | prop_bot  : RedAffNorm unif_bot_prop ⟨e', hn⟩ → RedUnify (open Dsl in (DCC? (Unify (Sort 1) (Sort 0) (Sort 0) ⊥))) e'
  | type_bot  : RedAffNorm (unif_bot_type u) ⟨e', hn⟩ → RedUnify (open Dsl in (DCC? (Unify (Sort (u + 2)) (Sort 0) (Sort (u + 1)) ⊥))) e'
  | congr     : (ViewUnify (DCC? (f x)) → False) → RedUnify f f' → RedUnify x x' → RedUnify (open Dsl in (DCC? (f x))) (open Dsl in (DCC? (f' x')))
  | no_step   : (IsUnify e → False) → (heq_ar : point_arity e = 0) → (hn_app : ViewApp e → False) → RedUnify e e
  | point₁    : (IsUnify e → False) → (h : point_arity e = 1) → RedUnify (points e)[0] p' → RedUnify e (e.set_points ⟨#[p'], by grind⟩)
  | point₂    : (IsUnify e → False) → (h : point_arity e = 2) → (hr₁ : RedUnify (points e)[0] p'₁) → (hr₂ : RedUnify (points e)[1] p'₂) → RedUnify e (e.set_points ⟨#[p'₁, p'₂], by grind⟩)
  | point₃    : (IsUnify e → False) → (h : point_arity e = 3) → (hr₁ : RedUnify (points e)[0] p'₁) → (hr₂ : RedUnify (points e)[1] p'₂) → (hr₃ : RedUnify (points e)[2] p'₃) → RedUnify e (e.set_points ⟨#[p'₁, p'₂, p'₃], by grind⟩)
  | point₄    : (IsUnify e → False) → (h : point_arity e = 4) → (hr₁ : RedUnify (points e)[0] p'₁) → (hr₂ : RedUnify (points e)[1] p'₂) → (hr₃ : RedUnify (points e)[2] p'₃) → (hr₃ : RedUnify (points e)[3] p'₄) → RedUnify e (e.set_points ⟨#[p'₁, p'₂, p'₃, p'₄], by simp [h]⟩)

def unify_refl? [DecidableEq τ] (e : GenericExpr τ) : Option ((e' : GenericExpr τ) × (PLift (RedUnify e e'))) :=
  open Dsl in match e with
  | (DCC? (Unify _A _B X X₂)) =>
    if heq : X₂ = X then
      heq ▸ .some ⟨_, ⟨.refl ⟨reduce_sound rfl, reduce_norm rfl⟩⟩⟩
    else .none
  | _ => .none

def step_unify_view? [DecidableEq τ] (e : GenericExpr τ) : Option ((e' : GenericExpr τ) × (PLift (RedUnify e e'))) :=
  match unify_refl? e with
  | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨h⟩⟩
  | .none =>
    open Dsl in match e with
    | (DCC? ((≃.dom ((Π _B₁ _C₁) _x₁) ((Π _B₂ _C₂) _x₂)) ((≃.mk _f_to _f_from _h_id₁ _h_id₂) (,_B _h₁ _h₂)))) =>
      .some ⟨_, ⟨.fn_dom ⟨reduce_sound rfl, reduce_norm rfl⟩⟩⟩
    | (DCC? ((≃.cod ((Π _B₁ _C₁) _x₁) ((Π _B₂ _C₂) _x₂)) ((≃.mk _f_to _f_from _h_id₁ _h_id₂) (,_B _h₁ _h₂)))) =>
      .some ⟨_, ⟨.fn_cod ⟨reduce_sound rfl, reduce_norm rfl⟩⟩⟩
    | (DCC? (Unify (Sort 1) (Sort 0) (Sort 0) ⊥)) => .some ⟨_, ⟨.prop_bot ⟨reduce_sound rfl, reduce_norm rfl⟩⟩⟩
    | (DCC? (Unify (Sort (u + 2)) (Sort 0) (Sort (u₂ + 1)) ⊥)) =>
      if heq : u₂ = u then
        heq ▸ .some ⟨_, ⟨.type_bot ⟨reduce_sound rfl, reduce_norm rfl⟩⟩⟩
      else .none
    | _ => .none

/-def size_unify (e : GenericExpr τ) : ℕ :=
  open Dsl in match e with
  | DCC[.] (Dom x) => x.size_unify
  | DCC[.] (Cod x) => x.size_unify
  | DCC[.] (Dom₂ x) => x.size_unify
  | DCC[.] (Unbang x) => x.size_unify
  | DCC[.] (Uncoup x) => x.size_unify
  | DCC[.] ∗ => 1
  | DCC[.] ⊤ => 2
  | DCC[.] ⊥ => 2
  | DCC[.] (= x y) => (x.size_unify + y.size_unify)
  | DCC[.] (≃ A B) => (A.size_unify + B.size_unify)
  | DCC[.] (Unify _τ_A _τ_B A B) => A.size_unify + B.size_unify
  | DCC? (? m) => m.size_unify
  | DCC? True => 0
  | DCC? False => 0
  | DCC? Bool => 0
  | DCC? (≃.1.apply _a _b) => 0
  | DCC? (≃.dom _a _b) => 0
  | DCC? (≃.cod _a _b) => 0
  | DCC? (≃.2.apply _a _b) => 0
  | DCC? (≃.mk a b c d) => a.size_unify + b.size_unify + c.size_unify + d.size_unify
  | DCC? (Bool.Ind motive x y) => motive.size_unify + x.size_unify + y.size_unify
  | DCC? (≃.Ind motive x) => motive.size_unify + x.size_unify
  | DCC? (≃.1 x y) => x.size_unify + y.size_unify
  | DCC? (≃.2 x y) => x.size_unify + y.size_unify
  | DCC? (≃.3 x y) => x.size_unify + y.size_unify
  | DCC? (≃.4 x y) => x.size_unify + y.size_unify
  | DCC? (⊥.Ind motive) => motive.size_unify
  | DCC[.] (Eql α)  => α.size_unify
  | DCC[.] (refl α) => α.size_unify
  | DCC[.] Sort _m => 0
  | DCC[.] (Σ α β) => α.size_unify + β.size_unify
  | DCC[.] (`β x) => β.size_unify + x.size_unify
  | DCC[.] (,β x y) => β.size_unify + x.size_unify + y.size_unify
  | DCC[.] (Σ β) => β.size_unify
  | DCC[.] (Id α)      => α.size_unify
  | DCC[.] (Fst α)    => α.size_unify
  | DCC[.] (Snd α)    => α.size_unify
  | DCC[.] (Swap B C)    => B.size_unify + C.size_unify
  | DCC[.] (Π α β) => 10 * ((100 * (α.size_unify + 5)) + (100 * (β.size_unify + 5)))
  | DCC[.] (∘ f g)  => f.size_unify + f.size_unify + g.size_unify
  | DCC[.] (⟨,⟩β a b)   => β.size_unify + a.size_unify + a.size_unify + b.size_unify
  | DCC[.] (Λ α β x) => α.size_unify + β.size_unify + x.size_unify
  | DCC[.] (!Λ α β x) => α.size_unify + β.size_unify + x.size_unify
  | DCC[.] (Eval α β x) => α.size_unify + β.size_unify + x.size_unify
  | DCC[.] (!x)   => x.size_unify
  | DCC[.] (*x)   => x.size_unify
  | DCC[.] (&x)   => x.size_unify
  | DCC[.] (!<> x)   => x.size_unify + x.size_unify
  | DCC[.] ($<> x)   => x.size_unify
  | DCC[.] (f x) => f.size_unify + x.size_unify + 1
  | .const _ => 0
  | .hole _ => 0-/

theorem size_le {n : Fin (point_arity (τ_c := τ) e)} : (size ((points e)[n])) ≤ size e := by
  induction e
  any_goals (grind [size])

set_option maxHeartbeats 2000000000000 in
def step_unify? [DecidableEq τ] (e : GenericExpr τ) : Option ((e' : GenericExpr τ) × (PLift (RedUnify e e'))) :=
  open Dsl in match step_unify_view? e with
  | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨h⟩⟩
  | .none =>
    match e with
    | DCC? (f x) =>
      if heq : (DCC? (f x)).view_unif? = .none then
        match f.step_unify?, x.step_unify? with
        | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ => .some ⟨_, ⟨.congr (fun h => by simp_all [h.complete]) h₁ h₂⟩⟩
        | _, _ => .none
      else .none
    | (DCC? (Unify (Sort u) (Sort v) ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂))) =>
      if heq : (DCC? ((Π B₁ C₁) x₁)) = (DCC? ((Π B₂ C₂) x₂)) then
        heq ▸ .some ⟨_, ⟨.refl ⟨reduce_sound rfl, reduce_norm rfl⟩⟩⟩
      else
        let hole := (mk_hole B₁ C₁ x₁ B₂ C₂ x₂)
        let τ₁   := (reduce RedAff (DCC? (B₁ x₁))).fst
        let τ₂   := (reduce RedAff (DCC? (B₂ x₂))).fst
        let τ₃   := (reduce RedAff (DCC? (C₁ x₁ hole))).fst
        let τ₄   := (reduce RedAff (DCC? (C₂ x₂ hole))).fst

        have h_dec₁ := decreasing? _ (reduce RedAff (DCC? (B₁ x₁))).snd.down
        have h_dec₂ := decreasing? _ (reduce RedAff (DCC? (B₂ x₂))).snd.down
        have h_dec₃ := decreasing? _ (reduce RedAff (DCC? (C₁ x₁ hole))).snd.down
        have h_dec₄ := decreasing? _ (reduce RedAff (DCC? (C₂ x₂ hole))).snd.down

        match step_unify? (DCC? (Unify (? τ₁) (? τ₂) τ₁ τ₂)), step_unify? (DCC? (Unify (? τ₃)
                                                         (? τ₄)
                                                         τ₃
                                                         τ₄)) with
        | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ =>
          .some ⟨_, ⟨.fn ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         h₁
                         h₂
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         (by grind)⟩⟩
        | _, _ => .none
    | e =>
      if heq₀ : is_unif? e = .none then
        match cases_point_arity' e with
        | .inl ⟨heq⟩ =>
          if heq_app : view_app? e = .none then
            .some ⟨_, ⟨.no_step (fun h => by simp_all [h.complete]) heq (fun h => by simp_all [h.complete])⟩⟩
          else .none
        | .inr (.inl ⟨heq⟩) =>
          have h_dec₀ : sizeOf e.points[0] < sizeOf e := by
            simp [points]
            split
            any_goals (grind)
            any_goals (simp)
          have h_dec : Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) ((e.points[0]).size, sizeOf e.points[0]) (e.size, sizeOf e) := by
            have hle := size_le (n := ⟨0, by grind⟩) (e := e)
            grind
          match e.points[0].step_unify? with
          | .some ⟨_, ⟨h⟩⟩ =>
            .some ⟨_, ⟨.point₁ (fun h => by simp_all [h.complete]) (by grind) h⟩⟩
          | .none => .none
        | .inr (.inr (.inl ⟨heq⟩)) =>
          have h_dec₀ : sizeOf e.points[0] < sizeOf e := by
            simp [points]
            split
            any_goals (grind)
            any_goals (simp; try (grind))
          have h_dec : Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) ((e.points[0]).size, sizeOf e.points[0]) (e.size, sizeOf e) := by
            have hle := size_le (n := ⟨0, by grind⟩) (e := e)
            grind
          have h_dec₀ : sizeOf e.points[1] < sizeOf e := by
            simp [points]
            split
            any_goals (grind)
          have h_dec : Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) ((e.points[1]).size, sizeOf e.points[1]) (e.size, sizeOf e) := by
            have hle := size_le (n := ⟨1, by grind⟩) (e := e)
            grind
          match e.points[0].step_unify?, e.points[1].step_unify? with
          | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ =>
            .some ⟨_, ⟨.point₂ (fun h => by simp_all [h.complete]) (by grind) h₁ h₂⟩⟩
          | _, _ => .none
        | .inr (.inr (.inr (.inl ⟨heq⟩))) =>
          have h_dec₀ : sizeOf e.points[0] < sizeOf e := by
            simp [points]
            split
            any_goals (grind)
            any_goals (simp; try grind)
          have h_dec : Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) ((e.points[0]).size, sizeOf e.points[0]) (e.size, sizeOf e) := by
            have hle := size_le (n := ⟨0, by grind⟩) (e := e)
            grind
          have h_dec₀ : sizeOf e.points[1] < sizeOf e := by
            simp [points]
            split
            any_goals (grind)
          have h_dec : Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) ((e.points[1]).size, sizeOf e.points[1]) (e.size, sizeOf e) := by
            have hle := size_le (n := ⟨1, by grind⟩) (e := e)
            grind
          have h_dec₀ : sizeOf e.points[2] < sizeOf e := by
            simp [points]
            split
            any_goals (grind)
          have h_dec : Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) ((e.points[2]).size, sizeOf e.points[2]) (e.size, sizeOf e) := by
            have hle := size_le (n := ⟨2, by grind⟩) (e := e)
            grind
          match e.points[0].step_unify?, e.points[1].step_unify? with
          | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ =>
            match e.points[2].step_unify? with
            | .some ⟨_, ⟨h₃⟩⟩ =>
              .some ⟨_, ⟨.point₃ (fun h => by simp_all [h.complete]) (by grind) h₁ h₂ h₃⟩⟩
            | .none => .none
          | _, _ => .none
        | .inr (.inr (.inr (.inr ⟨heq⟩))) =>
          have h_dec₀ : sizeOf e.points[0] < sizeOf e := by
            simp [points]
            split
            any_goals (grind)
            any_goals (simp; try grind)
          have h_dec : Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) ((e.points[0]).size, sizeOf e.points[0]) (e.size, sizeOf e) := by
            have hle := size_le (n := ⟨0, by grind⟩) (e := e)
            grind
          have h_dec₀ : sizeOf e.points[1] < sizeOf e := by
            simp [points]
            split
            any_goals (grind)
          have h_dec : Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) ((e.points[1]).size, sizeOf e.points[1]) (e.size, sizeOf e) := by
            have hle := size_le (n := ⟨1, by grind⟩) (e := e)
            grind
          have h_dec₀ : sizeOf e.points[2] < sizeOf e := by
            simp [points]
            split
            any_goals (grind)
          have h_dec : Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) ((e.points[2]).size, sizeOf e.points[2]) (e.size, sizeOf e) := by
            have hle := size_le (n := ⟨2, by grind⟩) (e := e)
            grind
          have h_dec₀ : sizeOf e.points[3] < sizeOf e := by
            simp [points]
            split
            any_goals (grind)
          have h_dec : Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) ((e.points[3]).size, sizeOf e.points[3]) (e.size, sizeOf e) := by
            have hle := size_le (n := ⟨3, by grind⟩) (e := e)
            grind
          match e.points[0].step_unify?, e.points[1].step_unify? with
          | .some ⟨_, ⟨h₁⟩⟩, .some ⟨_, ⟨h₂⟩⟩ =>
            match e.points[2].step_unify?, e.points[3].step_unify? with
            | .some ⟨_, ⟨h₃⟩⟩, .some ⟨_, ⟨h₄⟩⟩ =>
              .some ⟨_, ⟨.point₄ (fun h => by simp_all [h.complete]) (by grind) h₁ h₂ h₃ h₄⟩⟩
            | _, _ => .none
          | _, _ => .none
      else .none
termination_by (e.size, sizeOf e)
decreasing_by any_goals (grind [size, mk_hole])

set_option maxHeartbeats 2000000000000 in
def RedUnify.complete {e e' : GenericExpr τ} [DecidableEq τ] (h : RedUnify e e') : step_unify? e = .some ⟨e', ⟨h⟩⟩ := by
  induction h with
  | fn_cod hrt| fn_dom hrt| prop_bot hrt | type_bot hrt | refl hrt =>
    unfold step_unify?
    unfold step_unify_view?
    simp [unify_refl?, hrt.complete_fst]
    grind
  | fn hrt₁ hrt₂ hrt₃ hrt₄ hr₁ hr₂ hrt hneq ih =>
    unfold step_unify?
    unfold step_unify_view?
    simp [unify_refl?]
    expose_names
    have hneq₁ : ¬ ((B₂ = B₁ ∧ C₂ = C₁) ∧ x₂ = x₁) := fun ⟨⟨h₁, h₂⟩, h₃⟩ => by
      cases h₁
      cases h₂
      cases h₃
      exact (hneq rfl).elim
    have heq_fst := hrt.complete_fst
    have heq := hrt.complete
    have heq_fst₁ := hrt₁.complete_fst
    have heq₁ := hrt₁.complete
    have heq_fst₂ := hrt₂.complete_fst
    have heq₂ := hrt₂.complete
    have heq_fst₃ := hrt₃.complete_fst
    have heq₃ := hrt₃.complete
    have heq_fst₄ := hrt₄.complete_fst
    have heq₄ := hrt₄.complete
    have hneq₂ : ¬ ((B₁ = B₂ ∧ C₁ = C₂) ∧ x₁ = x₂) := by grind
    simp [hneq₁, hneq₂, h_unif_cod_ih]
    cases heq_fst₁
    cases heq_fst₂
    cases heq_fst₃
    cases heq_fst₄
    grind
  | congr =>
    unfold step_unify?
    split
    case h_1 heq =>
      unfold step_unify_view? at heq
      split at heq
      case h_1 =>
        cases heq
        case refl heq' => simp [unify_refl?] at heq'
      case h_2 =>
        expose_names
        cases f
        case cong_fn_cod =>
          cases x
          case app =>
            expose_names
            cases a_2
            case pi =>
              cases a_3
              case app =>
                expose_names
                cases a_4
                case cong_mk => simp at heq
                any_goals (simp at heq)
              any_goals (simp at heq)
            any_goals (simp at heq)
            case cong_mk =>
              cases a_3
              case mkc =>
                cases a
                case app =>
                  expose_names
                  cases a_8
                  case pi =>
                    cases a_1
                    case app =>
                      expose_names
                      cases a_10
                      case pi =>
                        simp at heq
                        exact (h (by constructor)).elim
                      any_goals (simp at heq)
                    any_goals (simp at heq)
                  any_goals (simp at heq)
                any_goals (simp at heq)
              any_goals (simp at heq)
          any_goals (simp at heq)
        case cong_fn_dom =>
          cases x
          case app =>
            expose_names
            cases a_2
            case pi =>
              cases a_3
              case app =>
                expose_names
                cases a_4
                case cong_mk => simp at heq
                any_goals (simp at heq)
              any_goals (simp at heq)
            case cong_mk =>
              cases a_3
              case mkc =>
                cases a
                case app =>
                  expose_names
                  cases a_8
                  case pi =>
                    cases a_1
                    case app =>
                      expose_names
                      cases a_10
                      case pi =>
                        simp at heq
                        exact (h (by constructor)).elim
                      any_goals (simp at heq)
                    any_goals (simp at heq)
                  any_goals (simp at heq)
                any_goals (simp at heq)
              any_goals (simp at heq)
            any_goals (simp at heq)
          any_goals (simp at heq)
        any_goals (simp at heq)
    case h_2 =>
      simp
      refine ⟨by
        apply Option.eq_none_iff_forall_ne_some.mpr
        expose_names
        intro h'
        exact (h h').elim, ?_⟩
      expose_names
      simp_all
  | no_step =>
    unfold step_unify?
    expose_names
    unfold step_unify_view?
    unfold unify_refl?
    split
    case h_1 heq' =>
      split at heq'
      case h_1 heq'' =>
        split at heq''
        case h_1 =>
          split at heq''
          case isTrue heq_X =>
            cases heq_X
            exact (h .mk).elim
          · grind
        · grind
      case h_2 =>
        unfold point_arity at heq_ar
        split at heq_ar
        any_goals (grind)
        case h_50 =>
          exact (hn_app .mk).elim
    case h_2 heq' =>
      split
      case h_1 =>
        exact (hn_app .mk).elim
      case h_2 =>
        exact (h .mk).elim
      case h_3 =>
        have heq : e_1.is_unif? = none := by
          apply Option.eq_none_iff_forall_ne_some.mpr
          intro h'
          exact (h h').elim
        have heq₂ : e_1.view_app? = none := by
          apply Option.eq_none_iff_forall_ne_some.mpr
          intro h'
          exact (hn_app h').elim
        simp [heq]
        split
        case h_1 =>
          simp [heq₂]
        any_goals (grind)
  | point₃ | point₂ | point₁ =>
    unfold step_unify?
    expose_names
    unfold step_unify_view?
    unfold unify_refl?
    split
    case h_1 heq' =>
      split at heq'
      case h_1 heq'' =>
        split at heq''
        case h_1 =>
          split at heq''
          case isTrue heq_X =>
            cases heq_X
            exact (h .mk).elim
          · grind
        · grind
      case h_2 =>
        unfold point_arity at h_1
        split at h_1
        any_goals (grind)
        try (any_goals (exact (h .mk).elim))
    case h_2 heq' =>
      split
      case h_1 => grind only [point_arity]
      case h_2 =>
        exact (h .mk).elim
      case h_3 =>
        have heq : e_1.is_unif? = none := by
          apply Option.eq_none_iff_forall_ne_some.mpr
          intro h'
          exact (h h').elim
        have heq₂ : e_1.view_app? = none := by
          apply Option.eq_none_iff_forall_ne_some.mpr
          intro h'
          cases h'
          grind only [point_arity]
        simp [heq]
        split
        any_goals (grind)
        case _ => simp_all
  | point₄ =>
    unfold step_unify?
    expose_names
    unfold step_unify_view?
    unfold unify_refl?
    split
    case h_1 heq' =>
      split at heq'
      case h_1 heq'' =>
        split at heq''
        case h_1 =>
          split at heq''
          case isTrue heq_X =>
            cases heq_X
            exact (h .mk).elim
          · grind
        · grind
      case h_2 =>
        unfold point_arity at h_1
        split at h_1
        any_goals (grind)
    case h_2 heq' =>
      split
      case h_1 => grind only [point_arity]
      case h_2 =>
        exact (h .mk).elim
      case h_3 =>
        have heq : e_1.is_unif? = none := by
          apply Option.eq_none_iff_forall_ne_some.mpr
          intro h'
          exact (h h').elim
        have heq₂ : e_1.view_app? = none := by
          apply Option.eq_none_iff_forall_ne_some.mpr
          intro h'
          cases h'
          grind only [point_arity]
        simp [heq]
        split
        any_goals (grind)
        case _ => simp_all

end GenericExpr

/-
(Unify (Sort u) (Sort v) ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂))
solve by

toFun := fun (f : ((Π B₁ C₁) x₁)) (x : (B₂ x₂)) =>
  let x' := (Unify ? ? (B₁ x₁) (B₂ x₂)).2 x
  let y  := f x'
  (Unify ? ? (C₁ x₁ x') (C₂ x₂ x)).1 y

Two issues:
- decreasing size (solvable by second inductive, second size argument)
  - But we're just doing structural recursion
    - Do this with simpler size measure, just AST nodes + branches
- Unify takes its arguments as points
  - Or Unify can just be indexed by an environment.
    - Size does not decrease here though.
    - Size should decrease for the rules we have so far.
- Solve this with Unify'?

- How will hole unification work?
  - Transitivity obviously leads to absurdity.
  - And there is no proof either.
  - Index it by the unique term.

Unify should accept a linear x.

How are we going to run Unify inside Judge?
We will have to type-check it. Leaving it as a decision
procedure increases complexity, but it allows using
in Judge without type-checking it necessarily.

All Unify should be in Unify.lean.

Move all Unify to Unify.lean so we don't have to keep updating
Conf.lean.

| unif_bot_sort : RedAff (DCC? ((Unify (Sort (u + 2)) (Sort 0)) ((Sort u + 1) ≃ ⊥) ⊥)) (unif_bot_type u)
| unif_bot_prop : RedAff (DCC? ((Unify (Sort 1) (Sort 0)) ((Sort 0) ≃ ⊥) ⊥)) unif_bot_prop

Use hole instead of x.
This is kinda cheating but only by a little.

Still have not done hole unification.

(Unify (
-/
