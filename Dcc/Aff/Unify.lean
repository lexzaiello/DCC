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
syntax "(×.mk" gen_dcc+ ")"        : gen_dcc
syntax "(⊕.Ind" gen_dcc+ ")"       : gen_dcc
syntax "(⊕.CasesAnd" gen_dcc+ ")"  : gen_dcc
syntax "(Bool.Cases" gen_dcc+ ")"  : gen_dcc

macro_rules
  | `(DCC[$loc] (⊕ $A:gen_dcc $B:gen_dcc)) => `(Sum (DCC[$loc] $A) (DCC[$loc] $B))
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
def mk_hole_sigma (B₁ B₂ : GenericExpr τ) : GenericExpr τ :=
  .hole ((DCC? (Σ B₁)).max_hole + (DCC? (Σ B₂)).max_hole)

/-
Note: this is safe since unify is a decision procedure, and the only former of ≃, and coincides with refl, and since ≃ unification is baked into DefEq.


(≃ (= ((Π B C) x) f _f) (= ((Π B C) x) g _g))
-/

open Dsl in
def unif_eq_fn_hole (B₁ C₁ x₁ B₂ C₂ x₂ f _f g _g : GenericExpr τ) : GenericExpr τ :=
  GenericExpr.hole ((DCC? (= ((Π B₁ C₁) x₁) f _f)).max_hole + (DCC? (= ((Π B₂ C₂) x₂) g _g)).max_hole)

open Dsl in
def unif_eq_fn_preimage (C₁ x₁ C₂ x₂ f _f g _g hole : GenericExpr τ) : GenericExpr τ :=
  DCC? (Unify (Sort 0) (Sort 0) (= (C₁ x₁ hole) (f hole) (_f hole)) (= (C₂ x₂ hole) (g hole) (_g hole)))

open Dsl in
def unif_eq_fn (B₁ C₁ x₁ B₂ C₂ x₂ f _f g _g hole h_unif : GenericExpr τ) : GenericExpr τ :=
  let goal := DCC? (⊕ (≃ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g)) (≃ (≃ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g)) ⊥))

  let t_can_unify := DCC? (≃ (= (C₁ x₁ hole) (f hole) (f hole)) (= (C₂ x₂ hole) (g hole) (g hole)))
  let t_cannot_unify := DCC? (≃ (≃ (= (C₁ x₁ hole) (f hole) (f hole)) (= (C₂ x₂ hole) (g hole) (g hole))) ⊥)

  let to_fn_cannot_unify := DCC? (→ (: (≃ (= (C₁ x₁ hole) (f hole) (f hole)) (= (C₂ x₂ hole) (g hole) (g hole))) (? ((Π B₁ C₁) x₁))) ⊥)

  DCC? ((⊕.Ind (Bool.Cases t_can_unify t_cannot_unify)
               (Bool.Cases (`t_can_unify goal) (`t_cannot_unify goal))
               (∘ ((Λ Bool (`Bool (≃ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g))) (Id (Σ (`Bool (≃ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g)))))) True)
                  (≃.mk (`t_can_unify (`(= ((Π B₁ C₁) x₁) f _f) (((refl (Id (? ((Π B₂ C₂) x₂)))) (& ((Π B₂ C₂) x₂)) (& g)))))
                     (`t_can_unify (`(= ((Π B₁ C₁) x₁) g _g) (((refl (Id (? ((Π B₁ C₁) x₁)))) (& ((Π B₁ C₁) x₁)) (& f)))))
                     (`(! t_can_unify) ((refl (Id Sort 0)) (& (! (= ((Π B₁ C₁) x₁) f _f)))))
                     (`(! t_can_unify) ((refl (Id Sort 0)) (& (! (= ((Π B₂ C₂) x₂) g _g)))))))
               (∘ ((Λ Bool (`Bool (≃ (≃ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g)) ⊥)) (Id (Σ (`Bool (≃ (≃ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g)) ⊥))))) False)
                  (≃.mk (∘ (Λ to_fn_cannot_unify
                           (`to_fn_cannot_unify (≃ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g)))
                           (∘ (Eval to_fn_cannot_unify
                                    (`to_fn_cannot_unify (≃ (= (C₁ x₁ hole) (f hole) (f hole)) (= (C₂ x₂ hole) (g hole) (g hole))))
                                    (Id to_fn_cannot_unify))
                              (Map to_fn_cannot_unify
                                   (≃ (= (C₁ x₁ hole) (f hole) (f hole)) (= (C₂ x₂ hole) (g hole) (g hole)))
                                   (Id to_fn_cannot_unify)
                                   (≃.env (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g)))))
                        (≃.1 (≃ (= (C₁ x₁ hole) (f hole) (f hole)) (= (C₂ x₂ hole) (g hole) (g hole))) ⊥))
                     (⊥.Ind (`t_cannot_unify (`⊥ (≃ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g)))))
                     (`(! t_cannot_unify) ((refl (Id (? (≃ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g))))) (& (≃ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g)))))
                     (`(! t_cannot_unify) ((refl (Id (Sort 0))) (& ⊥))))))
        h_unif)

open Dsl in
def unif_bang (A B A₁ A₂ : GenericExpr τ) (h_unif_A : GenericExpr τ) : GenericExpr τ :=
  let goal := DCC? (⊕ (≃ (! A₁) (! A₂)) (≃ (≃ (! A₁) (! A₂)) ⊥))

  DCC? ((⊕.Ind (Bool.Cases (! (≃ A₁ A₂)) (! (≃ (≃ A₁ A₂) ⊥)))
               (Bool.Cases (`(! (≃ A₁ A₂)) goal) (`(! (≃ (≃ A₁ A₂) ⊥)) goal))
               (≃.mk (Λ' (≃ A₁ A₂)
                         (`(≃ A₁ A₂) A₁)
                         ($<> (Eval (≃ A₁ A₂)
                                    (`(≃ A₁ A₂) A₁)
                                    (≃.1 A₁ A₂))))
                     (Λ' (≃ A₁ A₂)
                         (`(≃ A₁ A₂) A₂)
                         ($<> (Eval (≃ A₁ A₂)
                                    (`(≃ A₁ A₂) A₂)
                                    (≃.2 A₁ A₂))))
                     (`(! (≃ A₁ A₂)) ((refl (Id A)) (& (! A₁))))
                     (`(! (≃ A₁ A₂)) ((refl (Id B)) (& (! A₂))))) -- have (≃ A₁ A₂)
               (≃.mk (Λ (! (≃ (≃ A₁ A₂) ⊥))
                        (`(! (≃ (≃ A₁ A₂) ⊥)) (≃ (! A₁) (! A₂)))
                        (∘ (Eval (→ (: (≃ A₁ A₂) (? (≃ A₁ A₂))) ⊥)
                                 (`(→ (: (≃ A₁ A₂) (? (≃ A₁ A₂))) ⊥) (≃ A₁ A₂))
                                 (Id (→ (: (≃ A₁ A₂) (? (≃ A₁ A₂))) ⊥)))
                           (Map (→ (: (≃ A₁ A₂) (? (≃ A₁ A₂))) ⊥)
                                (≃ A₁ A₂)
                                (∘ (≃.1 (≃ A₁ A₂) ⊥) (* (≃ (≃ A₁ A₂) ⊥)))
                                (∘ (* (! (≃ A₁ A₂)))
                                   (≃.env (! A₁) (! A₂))))))
                     (⊥.Ind (`(! (≃ (≃ A₁ A₂) ⊥)) (`⊥ (≃ (! A₁) (! A₂)))))
                     (`(! (! (≃ (≃ A₁ A₂) ⊥))) ((refl (Id (? (≃ (! A₁) (! A₂))))) (& (≃ (! A₁) (! A₂)))))
                     (`(! ⊥) ((refl (Id (Sort 0))) (& ⊥)))) /- Have (! (≃ (≃ A₁ A₂) ⊥)) -/)
        ((⟨,⟩(`(⊕ (≃ A₁ A₂) (≃ (≃ A₁ A₂) ⊥))
               ((Bool.Ind (`⊤ (`Bool (? (! (≃ A₁ A₂)))))
                          (`⊤ (`Bool (! (≃ A₁ A₂))))
                          (`⊤ (`Bool (! (≃ (≃ A₁ A₂) ⊥)))))
                ∗)) (∘ (Fst ((Bool.Ind (`⊤ (`Bool (? (≃ A₁ A₂))))
                                       (`⊤ (`Bool (≃ A₁ A₂)))
                                       (`⊤ (`Bool (≃ (≃ A₁ A₂) ⊥)))) ∗))
                  (* (! (⊕ (≃ A₁ A₂) ((≃ A₁ A₂) ⊥)))))
               (Λ (! (⊕ (≃ A₁ A₂) ((≃ A₁ A₂) ⊥)))
                  (`(! (⊕ (≃ A₁ A₂) ((≃ A₁ A₂) ⊥))) Bool)
                  (∘ ($<> (Snd ((Bool.Ind (`⊤ (`Bool (? (≃ A₁ A₂))))
                                  (`⊤ (`Bool (≃ A₁ A₂)))
                                  (`⊤ (`Bool (≃ (≃ A₁ A₂) ⊥)))) ∗)))
                     (Fst (`(! (⊕ (≃ A₁ A₂) ((≃ A₁ A₂) ⊥))) Bool))))) (& (& h_unif_A))))

/-
(Unify _ _ (Σ B₁) (Σ B₂))
- Unify (Dom B₁) (Dom B₂)
- Unify (B₁ hole) (B₂ hole)

transport pointwise

Do this with

f : (x : τ₁) → A            g : (x : τ₂) → B
--------------------------------------------

---------------------------------------------
(Map A B f g) (,_B x y) = (,(`A B) (f x) (g y))

Jsut assoc?

(, (, f g) (, x y))
-/
open Dsl in
def unif_sigma (A B B₁ B₂ : GenericExpr τ) (h_unif_fst : GenericExpr τ) (h_unif_snd : GenericExpr τ) : GenericExpr τ :=
  let hole := (mk_hole_sigma B₁ B₂)

  let goal := DCC? (⊕ (≃ (Σ B₁) (Σ B₂)) (≃ (≃ (Σ B₁) (Σ B₂)) ⊥))

  let equiv_prod := (DCC? (× (≃ (Dom B₁) (Dom B₂)) (≃ (B₁ hole) (B₂ hole))))

  let t_sig₁ := DCC? (Σ B₁)
  let t_sig₂ := DCC? (Σ B₂)

  DCC? (⊕.CasesAnd goal
                   (≃ (Dom B₁) (Dom B₂))
                   (≃ (≃ (Dom B₁) (Dom B₂)) ⊥)
                   (≃ (B₁ hole) (B₂ hole))
                   (≃ (≃ (B₂ hole) (B₂ hole)) ⊥)
                   (∘ ((Λ Bool (`Bool (≃ (Σ B₁) (Σ B₂))) (Id goal)) True)
                      (≃.mk (Λ equiv_prod
                               (`equiv_prod t_sig₁)
                               (∘ (∘ (∘ (∘ (∘ (∘ (∘ (Swap (B₂ hole) (Dom B₂))
                                                    (Map (B₂ hole)
                                                         (Dom B₂)
                                                         (Id (B₂ hole))
                                                         (Eval (→ (: (Dom B₁) (? (Dom B₁))) (Dom B₂))
                                                               (`(→ (: (Dom B₁) (? (Dom B₁))) (Dom B₂)) (Dom B₁))
                                                               (Id (→ (: (Dom B₁) (? (Dom B₁))) (Dom B₂))))))
                                                 (Assoc (B₂ hole)
                                                        (→ (: (Dom B₁) (? (Dom B₁))) (Dom B₂))
                                                        (Dom B₁))) -- have (, (, y' ((Dom B₁) → (Dom B₂))) x)
                                              (Swap (Dom B₁)
                                                    (× (B₂ hole) (→ (: (Dom B₁) (? (Dom B₁))) (Dom B₂))))) -- have (, x (, y' ((Dom B₁) → (Dom B₂))))
                                           (Assoc (Dom B₁) (B₂ hole) (→ (: (Dom B₁) (? (Dom B₁))) (Dom B₂)))) -- have (, (, x y') ((Dom B₁) → (Dom B₂)))
                                        (Swap (→ (: (Dom B₁) (? (Dom B₁))) (Dom B₂)) (× (Dom B₁) (B₂ hole)))) -- have (, ((Dom B₁) → (Dom B₂)) (, x y'))
                                     (Map (→ (: (Dom B₁) (? (Dom B₁))) (Dom B₂))
                                          (× (Dom B₁) (B₂ hole))
                                          (≃.1 (Dom B₁) (Dom B₂))
                                          (∘ (∘ (Map (Dom B₁)
                                                     (B₂ hole)
                                                     (Id (Dom B₁))
                                                     (∘ (Eval (→ (: (B₁ hole) (? (B₁ hole))) (B₂ hole))
                                                              (`(→ (: (B₁ hole) (? (B₁ hole))) (B₂ hole)) (B₁ hole))
                                                              (Id (→ (: (B₁ hole) (? (B₁ hole))) (B₂ hole))))
                                                        (Swap (B₁ hole) (→ (: (B₁ hole) (? (B₁ hole))) (B₂ hole)))))-- have (, x (, y ((B₁ hole) → (B₂ hole))))
                                                 (∘ (Map (Dom B₁)
                                                        (Id (Dom B₁))
                                                        (× (B₁ hole) (→ (: (B₁ hole) (? (B₁ hole))) (B₂ hole)))
                                                        (Map (B₁ hole)
                                                             (→ (: (B₁ hole) (? (B₁ hole))) (B₂ hole))
                                                             (Id (B₁ hole))
                                                             (≃.1 (B₁ hole) (B₂ hole)))) -- Have (x (, y (≃ (B₁ hole) (B₂ hole))))
                                                   (Assoc (Dom B₁) (B₁ hole) (≃ (B₁ hole) (B₂ hole))))) -- Have ((, x y) (≃ (B₁ hole) (B₂ hole)))
                                             (Swap (≃ (B₁ hole) (B₂ hole)) (Σ B₁))))) -- Have (,(≃ (Dom B₁) (Dom B₂)) (, (≃ (B₁ hole) (B₂ hole))) (, x y))
                                  (Assoc (≃ (Dom B₁) (Dom B₂)) (≃ (B₁ hole) (B₂ hole)) (Σ B₁)))) -- Have (,(×.mk (≃ (Dom B₁) (Dom B₂)) (≃ (B₁ hole) (B₂ hole))) (, x y))
                            (Λ equiv_prod
                               (`equiv_prod t_sig₂)
                               (∘ (∘ (∘ (∘ (∘ (∘ (∘ (Swap (B₁ hole) (Dom B₁))
                                                    (Map (B₁ hole)
                                                         (Dom B₁)
                                                         (Id (B₁ hole))
                                                         (Eval (→ (: (Dom B₂) (? (Dom B₂))) (Dom B₁))
                                                               (`(→ (: (Dom B₂) (? (Dom B₂))) (Dom B₁)) (Dom B₂))
                                                               (Id (→ (: (Dom B₂) (? (Dom B₂))) (Dom B₁))))))
                                                 (Assoc (B₁ hole)
                                                        (→ (: (Dom B₂) (? (Dom B₂))) (Dom B₁))
                                                        (Dom B₂))) -- have (, (, y' ((Dom B₁) → (Dom B₂))) x)
                                              (Swap (Dom B₂)
                                                    (× (B₁ hole) (→ (: (Dom B₂) (? (Dom B₂))) (Dom B₁))))) -- have (, x (, y' ((Dom B₁) → (Dom B₂))))
                                           (Assoc (Dom B₂) (B₁ hole) (→ (: (Dom B₂) (? (Dom B₂))) (Dom B₁)))) -- have (, (, x y') ((Dom B₁) → (Dom B₂)))
                                        (Swap (→ (: (Dom B₂) (? (Dom B₂))) (Dom B₁)) (× (Dom B₂) (B₁ hole)))) -- have (, ((Dom B₁) → (Dom B₂)) (, x y'))
                                     (Map (→ (: (Dom B₂) (? (Dom B₂))) (Dom B₁))
                                          (× (Dom B₂) (B₁ hole))
                                          (≃.2 (Dom B₁) (Dom B₂))
                                          (∘ (∘ (Map (Dom B₂)
                                                     (B₁ hole)
                                                     (Id (Dom B₂))
                                                     (∘ (Eval (→ (: (B₂ hole) (? (B₂ hole))) (B₁ hole))
                                                              (`(→ (: (B₂ hole) (? (B₂ hole))) (B₁ hole)) (B₂ hole))
                                                              (Id (→ (: (B₂ hole) (? (B₂ hole))) (B₁ hole))))
                                                        (Swap (B₂ hole) (→ (: (B₂ hole) (? (B₂ hole))) (B₁ hole)))))-- have (, x (, y ((B₁ hole) → (B₂ hole))))
                                                 (∘ (Map (Dom B₂)
                                                        (Id (Dom B₂))
                                                        (× (B₂ hole) (→ (: (B₂ hole) (? (B₂ hole))) (B₁ hole)))
                                                        (Map (B₂ hole)
                                                             (→ (: (B₂ hole) (? (B₂ hole))) (B₁ hole))
                                                             (Id (B₂ hole))
                                                             (≃.2 (B₁ hole) (B₂ hole)))) -- Have (x (, y (≃ (B₁ hole) (B₂ hole))))
                                                   (Assoc (Dom B₂) (B₂ hole) (≃ (B₁ hole) (B₂ hole))))) -- Have ((, x y) (≃ (B₁ hole) (B₂ hole)))
                                             (Swap (≃ (B₁ hole) (B₂ hole)) (Σ B₁))))) -- Have (,(≃ (Dom B₁) (Dom B₂)) (, (≃ (B₁ hole) (B₂ hole))) (, x y))
                                  (Assoc (≃ (Dom B₁) (Dom B₂)) (≃ (B₁ hole) (B₂ hole)) (Σ B₁))))
                            (`(! equiv_prod) ((refl (Id A)) (& (Σ B₁))))
                            (`(! equiv_prod) ((refl (Id B)) (& (Σ B₂))))))
                   (≃.mk (Λ' (≃ (≃ (Dom B₁) (Dom B₂)) ⊥)
                             (≃ (Σ B₁) (Σ B₂))
                             (∘ (Eval' (→ (: (≃ (Dom B₁) (Dom B₂)) (? (≃ (Dom B₁) (Dom B₂)))) ⊥)
                                        (≃ (Dom B₁) (Dom B₂))
                                        (Id (→ (: (≃ (Dom B₁) (Dom B₂)) (? (≃ (Dom B₁) (Dom B₂)))) ⊥)))
                                (Map (→ (: (≃ (Dom B₁) (Dom B₂)) (? (≃ (Dom B₁) (Dom B₂)))) ⊥)
                                     (≃ (Dom B₁) (Dom B₂))
                                     (≃.1 (≃ (Dom B₁) (Dom B₂)) ⊥)
                                     (∘ (Fst (`(≃ (Dom B₁) (Dom B₂)) (≃ (B₁ hole) (B₂ hole))))
                                        (≃.env (Σ B₁) (Σ B₂)))) /- (≃ (Dom B₁) (Dom B₂))-/))
                         (⊥.Ind (`(≃ (Dom B₁) (Dom B₂)) (`⊥ (≃ (Σ B₁) (Σ B₂)))))
                         (`(! (≃ (≃ (Dom B₁) (Dom B₂)) ⊥)) ((refl (Id Sort 0)) (& ⊥)))
                         (`(! (≃ (≃ (Dom B₁) (Dom B₂)) ⊥)) ((refl (Id (? ((≃ (Σ B₁) (Σ B₂)))))) (& ((≃ (Σ B₁) (Σ B₂))))))) -- (≃ (Dom B₁) (Dom B₂)) ≃ ⊥ ⊢ (≃ (≃ (Σ B₁) (Σ B₂)) ⊥)
                   (≃.mk (Λ' (≃ (≃ (B₁ hole) (B₂ hole)) ⊥)
                             (≃ (Σ B₁) (Σ B₂))
                             (∘ (Eval' (→ (: (≃ (B₁ hole) (B₂ hole)) (? (≃ (B₁ hole) (B₂ hole)))) ⊥)
                                        (≃ (B₁ hole) (B₂ hole))
                                        (Id (→ (: (≃ (B₁ hole) (B₂ hole)) (? (≃ (B₁ hole) (B₂ hole)))) ⊥)))
                                (Map (→ (: (≃ (B₁ hole) (B₂ hole)) (? (≃ (B₁ hole) (B₂ hole)))) ⊥)
                                     (≃ (B₁ hole) (B₂ hole))
                                     (≃.1 (≃ (B₁ hole) (B₂ hole)) ⊥)
                                     (∘ (Snd (`(≃ (Dom B₁) (Dom B₂)) (≃ (B₁ hole) (B₂ hole))))
                                        (≃.env (Σ B₁) (Σ B₂)))) /- (≃ (Dom B₁) (Dom B₂))-/))
                         (⊥.Ind (`(≃ (Dom B₁) (Dom B₂)) (`⊥ (≃ (Σ B₁) (Σ B₂)))))
                         (`(! (≃ (≃ (Dom B₁) (Dom B₂)) ⊥)) ((refl (Id Sort 0)) (& ⊥)))
                         (`(! (≃ (≃ (Dom B₁) (Dom B₂)) ⊥)) ((refl (Id (? ((≃ (Σ B₁) (Σ B₂)))))) (& ((≃ (Σ B₁) (Σ B₂))))))) -- (≃ (B₁ hole) (B₂ hole)) ≃ ⊥ ⊢ (≃ (≃ (Σ B₁) (Σ B₂)) ⊥)
                   h_unif_fst
                   h_unif_snd)

/-
(≃.1.apply ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)) (, (, (, (a : (≃ (B₁ x₁) (B₂ x₂))) (b : (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) f) x) = b.1 (f (a.2 x))
-/
open Dsl in
def equiv_apply₁ (B₁ C₁ x₁ B₂ C₂ x₂ hole : GenericExpr τ) : GenericExpr τ :=
  let t_to_fun   := DCC? (→ (: (B₂ x₂) (? (B₂ x₂))) (B₁ x₁))
  let t_from_fun := DCC? (→ (: (C₁ x₁ hole) (? (C₁ x₁ hole))) (C₂ x₂ hole))

  let t_f        := (DCC? ((Π B₁ C₁) x₁))

  (DCC? (∘ (∘ (∘ (∘ (∘ (∘ (Eval t_from_fun (`t_from_fun (C₁ x₁ hole)) (Id t_from_fun))
                          (Map t_from_fun
                               (B₁ x₁ hole)
                               (Id t_from_fun)
                               (Eval t_f (`t_f (B₁ x₁)) (Id t_f))))
                       (Assoc t_from_fun t_f (B₁ x₁)))
                    (Map (× t_from_fun t_f)
                         (B₁ x₁)
                         (Id (× t_from_fun t_f))
                         (Eval t_to_fun (`t_to_fun (B₂ x₂)) (Id t_to_fun))))
                 (Assoc (× t_from_fun t_f)
                        t_to_fun
                        (B₂ x₂))) -- have (, (, (, b.1 f) a.2) x), make (, (, b.1 f) (, a.2 x))
              (Map (× (× t_from_fun t_f) t_to_fun)
                      (B₂ x₂)
                      (∘ (Swap (t_from_fun) (× t_to_fun t_f))
                         (Assoc t_from_fun t_to_fun t_f))
                      (Id (B₂ x₂)))) -- have (, (, (, a.2 b.1) f) x), make (, (, a.2 (, b.1 f)) x), make (, (, (, b.1 f) a.2) x), assoc make (, (, b.1 f) (Eval ∘ (, a.2 x)))
           (Map (× (× t_to_fun t_from_fun) t_f)
                (B₂ x₂)
                (Map t_to_fun
                     t_from_fun
                     (≃.2 (B₁ x₁) (B₂ x₂))
                     (≃.1 (C₁ x₁ hole) (C₂ x₂ hole)))
                (Id (B₂ x₂)))))

/-
(≃.2.apply ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)) (, (, (, (a : (≃ (B₁ x₁) (B₂ x₂))) (b : (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) f) x) = b.2 (f (a.1 x))
-/
open Dsl in
def equiv_apply₂ (B₁ C₁ x₁ B₂ C₂ x₂ hole : GenericExpr τ) : GenericExpr τ :=
  let t_to_fun   := DCC? (→ (: (B₁ x₁) (? (B₁ x₁))) (B₂ x₂))
  let t_from_fun := DCC? (→ (: (C₂ x₂ hole) (? (C₂ x₂ hole))) (C₁ x₁ hole))

  let t_f        := (DCC? ((Π B₂ C₂) x₂))

  (DCC? (∘ (∘ (∘ (∘ (∘ (∘ (Eval t_from_fun (`t_from_fun (C₂ x₂ hole)) (Id t_from_fun))
                          (Map t_from_fun
                               (B₂ x₂ hole)
                               (Id t_from_fun)
                               (Eval t_f (`t_f (B₂ x₂)) (Id t_f))))
                       (Assoc t_from_fun t_f (B₂ x₂)))
                    (Map (× t_from_fun t_f)
                         (B₂ x₂)
                         (Id (× t_from_fun t_f))
                         (Eval t_to_fun (`t_to_fun (B₁ x₁)) (Id t_to_fun))))
                 (Assoc (× t_from_fun t_f)
                        t_to_fun
                        (B₁ x₁))) -- have (, (, (, b.1 f) a.2) x), make (, (, b.1 f) (, a.2 x))
              (Map (× (× t_from_fun t_f) t_to_fun)
                      (B₁ x₁)
                      (∘ (Swap (t_from_fun) (× t_to_fun t_f))
                         (Assoc t_from_fun t_to_fun t_f))
                      (Id (B₁ x₁)))) -- have (, (, (, a.2 b.1) f) x), make (, (, a.2 (, b.1 f)) x), make (, (, (, b.1 f) a.2) x), assoc make (, (, b.1 f) (Eval ∘ (, a.2 x)))
           (Map (× (× t_to_fun t_from_fun) t_f)
                (B₁ x₁)
                (Map t_to_fun
                     t_from_fun
                     (≃.1 (B₁ x₁) (B₂ x₂))
                     (≃.2 (C₁ x₁ hole) (C₂ x₂ hole)))
                (Id (B₁ x₁)))))

open Dsl in
def unif_fn (τ₁ τ₂ B₁ C₁ x₁ B₂ C₂ x₂ : GenericExpr τ) (h_unif_dom : GenericExpr τ) (h_unif_cod : GenericExpr τ) : GenericExpr τ :=
  let hole := (mk_hole B₁ C₁ x₁ B₂ C₂ x₂)

  let goal := DCC? (⊕ (≃ ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)) (≃ (≃ ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)) ⊥))

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
                                  #(equiv_apply₁ B₁ C₁ x₁ B₂ C₂ x₂ hole))) -- Have ((×.mk (≃ (B₁ x₁) (B₂ x₂)) (≃ (C₁ x₁ hole) (C₂ x₂ hole)), f), x)
                            (Λ equiv_prod
                               (`equiv_prod t_fn₂)
                               (Λ (× equiv_prod t_fn₂)
                                  (`(× equiv_prod t_fn₁) (B₁ x₁))
                                  #(equiv_apply₂ B₁ C₁ x₁ B₂ C₂ x₂ hole)))
                            (`(! equiv_prod) ((refl (Id τ₁)) (& ((Π B₁ C₁) x₁))))
                            (`(! equiv_prod) ((refl (Id τ₂)) (& ((Π B₂ C₂) x₂))))))
                   (≃.mk (∘ (Λ (→ (: (≃ (B₁ x₁) (B₂ x₂)) (? (≃ (B₁ x₁) (B₂ x₂)))) ⊥)
                               (`(→ (: (≃ (B₁ x₁) (B₂ x₂)) (? (≃ (B₁ x₁) (B₂ x₂)))) ⊥) (≃ t_fn₁ t_fn₂))
                               (∘ (∘ (∘ (Fst (`(≃ (B₁ x₁) (B₂ x₂)) ((C₁ x₁ hole) (C₂ x₂ hole)))) (≃.env ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)))
                                     (Λ (≃ (B₁ x₁) (B₂ x₂))
                                        (`(≃ (B₁ x₁) (B₂ x₂)) (→ (: (≃ (B₁ x₁) (B₂ x₂)) (? (≃ (B₁ x₁) (B₂ x₂)))) ⊥))
                                        (∘ (Eval (→ (: (≃ (B₁ x₁) (B₂ x₂)) (? (≃ (B₁ x₁) (B₂ x₂)))) ⊥)
                                                 (`(→ (: (≃ (B₁ x₁) (B₂ x₂)) (? (≃ (B₁ x₁) (B₂ x₂)))) ⊥) (≃ (B₁ x₁) (B₂ x₂)))
                                                 (Id (→ (: (≃ (B₁ x₁) (B₂ x₂)) (? (≃ (B₁ x₁) (B₂ x₂)))) ⊥)))
                                           (Swap (≃ (B₁ x₁) (B₂ x₂)) (`(≃ (B₁ x₁) (B₂ x₂)) (→ (: (≃ (B₁ x₁) (B₂ x₂)) (? (≃ (B₁ x₁) (B₂ x₂)))) ⊥))))))
                                  (Swap (→ (: (≃ (B₁ x₁) (B₂ x₂)) (? (≃ (B₁ x₁) (B₂ x₂)))) ⊥) (≃ t_fn₁ t_fn₂))))
                            (≃.1 (≃ (B₁ x₁) (B₂ x₂)) ⊥))
                         (⊥.Ind (`(≃ (≃ (B₁ x₁) (B₂ x₂)) ⊥) (`⊥ ⊥)))
                         (`(! (≃ (≃ (B₁ x₁) (B₂ x₂)) ⊥)) ((refl (Id (? (≃ ((Π B₁ C₁) x₁) ((Π B₁ C₂) x₂))))) (& (≃ ((Π B₁ C₁) x₁) ((Π B₁ C₂) x₂)))))
                         (`(! (≃ (≃ (B₁ x₁) (B₂ x₂)) ⊥)) ((refl (Id (Sort 0))) (& ⊥)))) -- (≃ (B₁ x₁) (B₂ x₂)) ≃ ⊥ ⊢ (≃ (≃ ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)) ⊥)
                   (≃.mk (∘ (Λ (→ (: (≃ (C₁ x₁ hole) (C₂ x₂ hole)) (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) ⊥)
                               (`(→ (: (≃ (C₁ x₁ hole) (C₂ x₂ hole)) (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) ⊥) (≃ t_fn₁ t_fn₂))
                               (∘ (∘ (∘ (Snd (`(≃ (B₁ x₁) (B₂ x₂)) ((C₁ x₁ hole) (C₂ x₂ hole)))) (≃.env ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)))
                                     (Λ (≃ (C₁ x₁ hole) (C₂ x₂ hole))
                                        (`(≃ (C₁ x₁ hole) (C₂ x₂ hole)) (→ (: (≃ (C₁ x₁ hole) (C₂ x₂ hole)) (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) ⊥))
                                        (∘ (Eval (→ (: (≃ (C₁ x₁ hole) (C₂ x₂ hole)) (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) ⊥)
                                                 (`(→ (: (≃ (C₁ x₁ hole) (C₂ x₂ hole)) (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) ⊥) (≃ (C₁ x₁ hole) (C₂ x₂ hole)))
                                                 (Id (→ (: (≃ (C₁ x₁ hole) (C₂ x₂ hole)) (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) ⊥)))
                                           (Swap (≃ (C₁ x₁ hole) (C₂ x₂ hole)) (`(≃ (C₁ x₁ hole) (C₂ x₂ hole)) (→ (: (≃ (C₁ x₁ hole) (C₂ x₂ hole)) (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) ⊥))))))
                                  (Swap (→ (: (≃ (C₁ x₁ hole) (C₂ x₂ hole)) (? (≃ (C₁ x₁ hole) (C₂ x₂ hole)))) ⊥) (≃ t_fn₁ t_fn₂))))
                            (≃.1 (≃ (B₁ x₁) (B₂ x₂)) ⊥))
                         (⊥.Ind (`(≃ (≃ (C₁ x₁ hole) (C₂ x₂ hole)) ⊥) (`⊥ ⊥)))
                         (`(! (≃ (≃ (C₁ x₁ hole) (C₂ x₂ hole)) ⊥)) ((refl (Id (? (≃ ((Π B₁ C₁) x₁) ((Π B₁ C₂) x₂))))) (& (≃ ((Π B₁ C₁) x₁) ((Π B₁ C₂) x₂)))))
                         (`(! (≃ (≃ (C₁ x₁ hole) (C₂ x₂ hole)) ⊥)) ((refl (Id (Sort 0))) (& ⊥)))) -- ((C₁ x₁ hole) ≃ (C₂ x₂ hole)) ≃ ⊥
                   h_unif_dom
                   h_unif_cod)

/-
A ≃ A. This is due to Id.
-/
open Dsl in
abbrev unif_refl (τ_A₁ τ_A₂ A : GenericExpr τ) : GenericExpr τ :=
  (DCC? (,(`(Bool) (≃ A A)) True ((≃.mk (`⊤ (Id A)) (`⊤ (Id A)) (`(! ⊤) ((refl (Id τ_A₁)) (&A))) (`(! ⊤) ((refl (Id τ_A₂)) (&A)))) ∗)))

/-
(Type u ≃ ⊥) ≃ ⊥
-/
open Dsl in
abbrev unif_bot_type (u : Level) : GenericExpr τ :=
  (DCC? (,(`Bool (≃ (≃ (Sort (u + 1)) ⊥) ⊥))
          False
          ((≃.mk (`⊤ (∘ ((Λ (Sort u + 1)
                         (`(Sort u + 1) (→ (: (Sort (u + 1)) Sort u + 2) ⊥))
                         (∘ (Eval (→ (: (Sort (u + 1)) Sort u + 2) ⊥)
                                  (`(→ (: (Sort (u + 1)) Sort u + 2) ⊥) (Sort u + 1))
                                  (Id (→ (: (Sort (u + 1)) Sort u + 2) ⊥)))
                            (Swap (Sort u + 1) (→ (: (Sort u) Sort u + 1) ⊥)))) (Sort u))
                      (≃.1 (Sort (u + 1)) ⊥))) -- (Type u ≃ ⊥), prove ⊥. Grab Type u → ⊥, plug in Sort u
              (⊥.Ind (`⊤ (`⊥ (≃ (Sort (u + 1)) ⊥)))) -- ⊤, ⊥, prove (Type u ≃ ⊥). Use ⊥.Ind
              (`(! ⊤) ((refl (Id (Sort (u + 2)))) (& (Sort (u + 1)))))
              (`(! ⊤) ((refl (Id (Sort 0))) (& ⊥))))
         ∗)))

/-
(Sort 0 ≃ ⊥) ≃ ⊥, this is provable because ⊤ inhabits Sort 0.
-/
open Dsl in
abbrev unif_bot_prop : GenericExpr τ :=
  (DCC? (,(`Bool (≃ (≃ (Sort 0) ⊥) ⊥))
          False
          ((≃.mk (`⊤ (∘ ((Λ (Sort 0)
                            (`(Sort 0) (→ (: (Sort 0) Sort 1) ⊥))
                            (∘ (Eval (→ (: (Sort 0) Sort 1) ⊥)
                                     (`(→ (: (Sort 0) Sort 1) ⊥) Sort 0)
                                     (Id (→ (: (Sort 0) Sort 1) ⊥)))
                               (Swap (Sort 0) (→ (: (Sort 0) Sort 1) ⊥)))) ⊤)
                         (≃.1 (Sort 0) ⊥)))
                 (⊥.Ind (`⊤ (`⊥ (≃ (Sort 0) ⊥))))
                 (`(! ⊤) ((refl (Id (Sort 1))) (& (Sort 0))))
                 (`(! ⊤) ((refl (Id (Sort 0))) (& ⊥))))
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
deriving Repr

inductive ViewApp : (e : GenericExpr τ) → Type u
  | mk : ViewApp (DCC? (f x))
deriving Repr

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
  | pi     : (hneq : (DCC? ((Π B₁ C₁) x₁)) ≠  (DCC? ((Π B₂ C₂) x₂))) → ViewUnify (DCC? (Unify A B ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂)))
  | sigma  : (hneq : (DCC? (Σ B₁)) ≠ (DCC? (Σ B₂))) → ViewUnify (DCC? (Unify _A _B (Σ B₁) (Σ B₂)))
  | eq     : (DCC? (= A X₁ Y₁)) ≠ (DCC? (= B X₂ Y₂)) → ViewUnify (DCC? (Unify τ₁ τ₂ (= A X₁ Y₁) (= B X₂ Y₂)))
  | prop   : ViewUnify (DCC? (Unify (Sort 1) (Sort 0) (Sort 0) ⊥))
  | type   : ViewUnify (DCC? (Unify (Sort (u + 2)) (Sort 0) (Sort (u + 1)) ⊥))
  | env    : ViewUnify (DCC? ((≃.env τ₁ τ₂) ((≃.mk f_to f_from h_id₁ h_id₂) x)))
deriving Repr

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
  | DCC? ((≃.env _τ₁ _τ₂) ((≃.mk _f_to _f_from _h_id₁ _h_id₂) _x)) => .some .env
  | DCC? (Unify A B X Y) =>
    if heq : X = Y then
      heq ▸ .some .refl
    else
      match heq₂ : DCC? (Unify A B X Y) with
      | DCC? (Unify _A _B ((Π _B₁ _C₁) _x₁) ((Π _B₂ _C₂) _x₂)) => .some (.pi (by grind))
      | DCC? (Unify τ₁ τ₂ (= A X₁ Y₁) (= B X₂ Y₂)) => .some (.eq (by grind))
      | DCC? (Unify _A _B (Σ _B₁) (Σ _B₂)) => .some (.sigma (by grind))
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
  case pi | sigma | eq => grind

inductive RedUnify : (e : GenericExpr τ) → (e' : GenericExpr τ) → Type u
  | refl      : RedAffNorm X₁ ⟨X, hn_x₁⟩
    → RedAffNorm X₂ ⟨X, hn_x₂⟩
    → RedAffNorm (unif_refl A B X) ⟨e', hn⟩
    → RedUnify (open Dsl in (DCC? (Unify A B X₁ X₂))) e'
  | fn_eq     : RedAffNorm X₁ ⟨(open Dsl in (DCC? (= ((Π B₁ C₁) x₁) f _f))), hn_x₁⟩
    → RedAffNorm X₂ ⟨(open Dsl in (DCC? (= ((Π B₂ C₂) x₂) g _g))), hn_x₂⟩
    → (h_unify : RedUnify (unif_eq_fn_preimage C₁ x₁ C₂ x₂ f _f g _g (unif_eq_fn_hole B₁ C₁ x₁ B₂ C₂ x₂ f _f g _g)) e₁)
    → RedAffNorm (unif_eq_fn B₁ C₁ x₁ B₂ C₂ x₂ f _f g _g (unif_eq_fn_hole B₁ C₁ x₁ B₂ C₂ x₂ f _f g _g) e₁) ⟨e', hn⟩
    → (hneq : (open Dsl in (DCC? (= ((Π B₁ C₁) x₁) f _f))) ≠ (open Dsl in (DCC? (= ((Π B₂ C₂) x₂) g _g))))
    → RedUnify (open Dsl in (DCC? (Unify τ₁ τ₂ X₁ X₂))) e'
  | bang      : RedAffNorm X₁ ⟨(open Dsl in (DCC? (! A₁))), hn_x₁⟩
    → RedAffNorm X₂ ⟨(open Dsl in (DCC? (! A₂))), hn_x₂⟩
    → (hr₁ : RedAffNorm A₁ ⟨τ₁, hn_τ₁⟩)
    → (hr₂    : RedAffNorm A₂ ⟨τ₂, hn_τ₂⟩)
    → (h_unif : RedUnify (open Dsl in (DCC? (Unify (? τ₁) (? τ₂) τ₁ τ₂))) e₁)
    → RedAffNorm A ⟨A', hn_A⟩
    → RedAffNorm B ⟨B', hn_B⟩
    → RedAffNorm (unif_bang A' B' τ₁ τ₂ e₁) ⟨e', hn⟩
    → (hneq : (open Dsl in (DCC? (! A₁))) ≠ (open Dsl in (DCC? (! A₂))))
    → RedUnify (open Dsl in (DCC? (Unify A B X₁ X₂))) e'
  | fn        : RedAffNorm X₁ ⟨(open Dsl in (DCC? ((Π B₁ C₁) x₁))), hn_x₁⟩
    → RedAffNorm X₂ ⟨(open Dsl in (DCC? ((Π B₂ C₂) x₂))), hn_x₂⟩
    → (hr₁ : RedAffNorm (B₁.app x₁) ⟨τ₁, hn_τ₁⟩)
    → (hr₂ : RedAffNorm (B₂.app x₂) ⟨τ₂, hn_τ₂⟩)
    → (hr₃ : RedAffNorm (DCC? (C₁ x₁ #(mk_hole B₁ C₁ x₁ B₂ C₂ x₂))) ⟨τ₃, hn_τ₃⟩)
    → (hr₄ : RedAffNorm (DCC? (C₂ x₂ #(mk_hole B₁ C₁ x₁ B₂ C₂ x₂))) ⟨τ₄, hn_τ₄⟩)
    → (h_unif_dom : RedUnify (open Dsl in (DCC? (Unify (? τ₁) (? τ₂) τ₁ τ₂))) e₁)
    → (h_unif_cod : RedUnify (open Dsl in (DCC? (Unify (? τ₃) (? τ₄) τ₃ τ₄))) e₂)
    → RedAffNorm A ⟨A', hn_A⟩
    → RedAffNorm B ⟨B', hn_B⟩
    → RedAffNorm (unif_fn A' B' B₁ C₁ x₁ B₂ C₂ x₂ e₁ e₂) ⟨e', hn⟩
    → (hneq   : (open Dsl in (DCC? ((Π B₁ C₁) x₁))) ≠ (open Dsl in (DCC? ((Π B₂ C₂) x₂))))
    → RedUnify (open Dsl in (DCC? (Unify A B X₁ X₂))) e'
  | sigma     : RedAffNorm X₁ ⟨(open Dsl in (DCC? (Σ B₁))), hn_x₁⟩
    → RedAffNorm X₂ ⟨(open Dsl in (DCC? (Σ B₂))), hn_x₂⟩
    → (hr₁ : RedAffNorm B₁ ⟨τ₁, hn_τ₁⟩)
    → (hr₂ : RedAffNorm B₂ ⟨τ₂, hn_τ₂⟩)
    → (hr₃ : RedAffNorm (DCC? (B₁ #(mk_hole_sigma B₁ B₂))) ⟨τ₃, hn_τ₃⟩)
    → (hr₄ : RedAffNorm (DCC? (B₂ #(mk_hole_sigma B₁ B₂))) ⟨τ₄, hn_τ₄⟩)
    → (h_unif_fst : RedUnify (open Dsl in (DCC? (Unify (? τ₁) (? τ₂) τ₁ τ₂))) e₁)
    → (h_unif_snd : RedUnify (open Dsl in (DCC? (Unify (? τ₃) (? τ₄) τ₃ τ₄))) e₂)
    → RedAffNorm A ⟨A', hn_A⟩
    → RedAffNorm B ⟨B', hn_B⟩
    → RedAffNorm (unif_sigma A' B' B₁ B₂ e₁ e₂) ⟨e', hn⟩
    → (hneq   : (open Dsl in (DCC? (Σ B₁))) ≠ (open Dsl in (DCC? (Σ B₂))))
    → RedUnify (open Dsl in (DCC? (Unify A B X₁ X₂))) e'
  -- ≃ is always formed by ≃.mk. fst and snd fetch the respective proof environment components
  | env       : RedAffNorm x ⟨x', hn⟩ → RedUnify (open Dsl in (DCC? ((≃.env _τ₁ _τ₂) ((≃.mk f_to f_from h_id₁ h_id₂) x)))) x'
  | prop_bot  : RedAffNorm X₁ ⟨DCC? Sort 0, hn_x₁⟩
    → RedAffNorm X₂ ⟨DCC? ⊥, hn_x₂⟩
    → RedAffNorm unif_bot_prop ⟨e', hn⟩ → RedUnify (open Dsl in (DCC? (Unify τ₁ τ₂ X₁ X₂))) e'
  | type_bot  : RedAffNorm X₁ ⟨DCC? Sort (u + 1), hn_x₁⟩
    → RedAffNorm X₂ ⟨DCC? ⊥, hn_x₂⟩
    → RedAffNorm (unif_bot_type u) ⟨e', hn⟩ → RedUnify (open Dsl in (DCC? (Unify τ₁ τ₂ X₁ X₂))) e'
  | congr     : (ViewUnify (DCC? (f x)) → False) → RedUnify f f' → RedUnify x x' → RedUnify (open Dsl in (DCC? (f x))) (open Dsl in (DCC? (f' x')))
  | no_step   : (IsUnify e → False) → (heq_ar : point_arity e = 0) → (hn_app : ViewApp e → False) → RedUnify e e
  | point₁    : (IsUnify e → False) → (h : point_arity e = 1) → RedUnify (points e)[0] p' → RedUnify e (e.set_points ⟨#[p'], by grind⟩)
  | point₂    : (IsUnify e → False) → (h : point_arity e = 2) → (hr₁ : RedUnify (points e)[0] p'₁) → (hr₂ : RedUnify (points e)[1] p'₂) → RedUnify e (e.set_points ⟨#[p'₁, p'₂], by grind⟩)
  | point₃    : (IsUnify e → False) → (h : point_arity e = 3) → (hr₁ : RedUnify (points e)[0] p'₁) → (hr₂ : RedUnify (points e)[1] p'₂) → (hr₃ : RedUnify (points e)[2] p'₃) → RedUnify e (e.set_points ⟨#[p'₁, p'₂, p'₃], by grind⟩)
  | point₄    : (IsUnify e → False) → (h : point_arity e = 4) → (hr₁ : RedUnify (points e)[0] p'₁) → (hr₂ : RedUnify (points e)[1] p'₂) → (hr₃ : RedUnify (points e)[2] p'₃) → (hr₃ : RedUnify (points e)[3] p'₄) → RedUnify e (e.set_points ⟨#[p'₁, p'₂, p'₃, p'₄], by simp [h]⟩)
deriving Repr

def unify_refl? [DecidableEq τ] (e : GenericExpr τ) : Option ((e' : GenericExpr τ) × RedUnify e e') :=
  open Dsl in match e with
  | (DCC? (Unify _A _B X X₂)) =>
    if heq : (reduce RedAff X₂).fst = (reduce RedAff X).fst then
      .some ⟨_, .refl ⟨reduce_sound rfl, reduce_norm rfl⟩ (RedAffNorm.mk (reduce_sound_fst heq) (reduce_norm_fst heq)) ⟨reduce_sound rfl, reduce_norm rfl⟩⟩
    else .none
  | _ => .none

def step_unify_view? [DecidableEq τ] (e : GenericExpr τ) : Option ((e' : GenericExpr τ) × (RedUnify e e')) :=
  match unify_refl? e with
  | .some ⟨_, h⟩ => .some ⟨_, h⟩
  | .none =>
    open Dsl in match e with
    | (DCC? ((≃.env _τ₁ _τ₂) ((≃.mk _f_to _f_from _h_id₁ _h_id₂) _x))) => .some ⟨_, .env ⟨reduce_sound rfl, reduce_norm rfl⟩⟩
    | DCC? (Unify _τ₁ _τ₂ A B) =>
      match heq₁ : (reduce RedAff A).fst with
      | DCC? (Sort 0) =>
        match heq₂ : (reduce RedAff B).fst with
        | DCC? ⊥ =>
          .some ⟨_, .prop_bot ⟨reduce_sound_fst heq₁, reduce_norm_fst heq₁⟩ ⟨reduce_sound_fst heq₂, reduce_norm_fst heq₂⟩ ⟨reduce_sound rfl, reduce_norm rfl⟩⟩
        | _ => .none
      | DCC? (Sort (_u + 1)) =>
        match heq₂ : (reduce RedAff B).fst with
        | DCC? ⊥ =>
          .some ⟨_, .type_bot ⟨reduce_sound_fst heq₁, reduce_norm_fst heq₁⟩ ⟨reduce_sound_fst heq₂, reduce_norm_fst heq₂⟩ ⟨reduce_sound rfl, reduce_norm rfl⟩⟩
        | _ => .none
      | _ => .none
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
  | DCC? (≃.env.1 _a _b) => 0
  | DCC? (≃.env.2 _a _b) => 0
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
def step_unify? [DecidableEq τ] (e : GenericExpr τ) : Option ((e' : GenericExpr τ) × (RedUnify e e')) :=
  open Dsl in match step_unify_view? e with
  | .some ⟨_, h⟩ => .some ⟨_, h⟩
  | .none =>
    match e with
    | DCC? (f x) =>
      if heq : (DCC? (f x)).view_unif? = .none then
        match f.step_unify?, x.step_unify? with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ => .some ⟨_, .congr (fun h => by simp_all [h.complete]) h₁ h₂⟩
        | _, _ => .none
      else .none
    | DCC? (Unify τ₁ τ₂ A B) =>
      if heq_refl : (reduce RedAff A).fst = (reduce RedAff B).fst then
        .some ⟨_, .refl (RedAffNorm.mk (reduce_sound_fst heq_refl) (reduce_norm_fst heq_refl)) ⟨reduce_sound rfl, reduce_norm rfl⟩ ⟨reduce_sound rfl, reduce_norm rfl⟩⟩
      else match heq₁ : (reduce RedAff A).fst with
      | DCC? (= ((Π B₁ C₁) x₁) f _f) =>
        match heq₂ : (reduce RedAff B).fst with
        | DCC? (= ((Π B₂ C₂) x₂) g _g) =>
          have h_size_eq₁ : (unif_eq_fn_hole B₁ C₁ x₁ B₂ C₂ x₂ f _f g _g).size = 0 := by
            unfold unif_eq_fn_hole
            grind
          have h_dec₁ : (unif_eq_fn_preimage C₁ x₁ C₂ x₂ f _f g _g (unif_eq_fn_hole B₁ C₁ x₁ B₂ C₂ x₂ f _f g _g)).size < (DCC? (Unify τ₁ τ₂ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g))).size := by
            unfold unif_eq_fn_preimage
            simp [size, h_size_eq₁]
            grind
          match step_unify? (unif_eq_fn_preimage C₁ x₁ C₂ x₂ f _f g _g (unif_eq_fn_hole B₁ C₁ x₁ B₂ C₂ x₂ f _f g _g)) with
          | .some ⟨_, h₁⟩ =>
            .some ⟨_, .fn_eq ⟨reduce_sound_fst heq₁, reduce_norm_fst heq₁⟩
                             ⟨reduce_sound_fst heq₂, reduce_norm_fst heq₂⟩
                             h₁
                             ⟨reduce_sound rfl, reduce_norm rfl⟩
                             (by grind)⟩
          | .none => .none
        | _ => .none
      | DCC? (! A₁) =>
        match heq₂ : (reduce RedAff B).fst with
        | DCC? (! A₂) =>
          let τ₁ := (reduce RedAff A₁).fst
          let τ₂ := (reduce RedAff A₂).fst
          have h_dec₁ := decreasing? _ (reduce RedAff A₁).snd.down
          have h_dec₂ := decreasing? _ (reduce RedAff A₂).snd.down
          match step_unify? (DCC? (Unify (? τ₁) (? τ₂) τ₁ τ₂)) with
          | .some ⟨_, h₁⟩ =>
            .some ⟨_, .bang ⟨reduce_sound_fst heq₁, reduce_norm_fst heq₁⟩
                            ⟨reduce_sound_fst heq₂, reduce_norm_fst heq₂⟩
                            ⟨reduce_sound rfl, reduce_norm rfl⟩
                            ⟨reduce_sound rfl, reduce_norm rfl⟩
                            h₁
                            ⟨reduce_sound rfl, reduce_norm rfl⟩
                            ⟨reduce_sound rfl, reduce_norm rfl⟩
                            ⟨reduce_sound rfl, reduce_norm rfl⟩
                            (by grind)⟩
          | .none => .none
        | _ => .none
      | DCC? ((Π B₁ C₁) x₁) =>
        match heq₂ : (reduce RedAff B).fst with
        | DCC? ((Π B₂ C₂) x₂) =>
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
          | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
            .some ⟨_, .fn ⟨reduce_sound_fst heq₁, reduce_norm_fst heq₁⟩
                          ⟨reduce_sound_fst heq₂, reduce_norm_fst heq₂⟩
                          ⟨reduce_sound rfl, reduce_norm rfl⟩
                          ⟨reduce_sound rfl, reduce_norm rfl⟩
                          ⟨reduce_sound rfl, reduce_norm rfl⟩
                          ⟨reduce_sound rfl, reduce_norm rfl⟩
                          h₁
                          h₂
                          ⟨reduce_sound rfl, reduce_norm rfl⟩
                          ⟨reduce_sound rfl, reduce_norm rfl⟩
                          ⟨reduce_sound rfl, reduce_norm rfl⟩
                          (by grind)⟩
          | _, _ => .none
        | _ => .none
      | DCC? (Σ B₁) =>
        match heq₂ : (reduce RedAff B).fst with
        | DCC? (Σ B₂) =>
          let hole := (mk_hole_sigma B₁ B₂)
          let τ₁   := (reduce RedAff B₁).fst
          let τ₂   := (reduce RedAff B₂).fst
          let τ₃   := (reduce RedAff (DCC? (B₁ hole))).fst
          let τ₄   := (reduce RedAff (DCC? (B₂ hole))).fst

          have h_dec₁ := decreasing? _ (reduce RedAff B₁).snd.down
          have h_dec₂ := decreasing? _ (reduce RedAff B₂).snd.down
          have h_dec₃ := decreasing? _ (reduce RedAff (DCC? (B₁ hole))).snd.down
          have h_dec₄ := decreasing? _ (reduce RedAff (DCC? (B₂ hole))).snd.down

          match step_unify? (DCC? (Unify (? τ₁) (? τ₂) τ₁ τ₂)), step_unify? (DCC? (Unify (? τ₃)
                                                           (? τ₄)
                                                           τ₃
                                                           τ₄)) with
          | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
            .some ⟨_, .sigma ⟨reduce_sound_fst heq₁, reduce_norm_fst heq₁⟩
                             ⟨reduce_sound_fst heq₂, reduce_norm_fst heq₂⟩
                             ⟨reduce_sound rfl, reduce_norm rfl⟩
                             ⟨reduce_sound rfl, reduce_norm rfl⟩
                             ⟨reduce_sound rfl, reduce_norm rfl⟩
                             ⟨reduce_sound rfl, reduce_norm rfl⟩
                             h₁
                             h₂
                             ⟨reduce_sound rfl, reduce_norm rfl⟩
                             ⟨reduce_sound rfl, reduce_norm rfl⟩
                             ⟨reduce_sound rfl, reduce_norm rfl⟩
                             (by grind)⟩
          | _, _ => .none
        | _ => .none
      | _ => .none
    /-| DCC? (Unify τ₁ τ₂ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g)) =>
      if heq : (reduce RedAff (DCC? (= ((Π B₁ C₁) x₁) f _f))).fst = (reduce RedAff (DCC? (= ((Π B₂ C₂) x₂) g _g))).fst then
        .some ⟨_, .refl (RedAffNorm.mk (reduce_sound_fst heq) (reduce_norm_fst heq)) ⟨reduce_sound rfl, reduce_norm rfl⟩ ⟨reduce_sound rfl, reduce_norm rfl⟩⟩
      else
        have h_size_eq₁ : (unif_eq_fn_hole B₁ C₁ x₁ B₂ C₂ x₂ f _f g _g).size = 0 := by
          unfold unif_eq_fn_hole
          grind
        have h_dec₁ : (unif_eq_fn_preimage C₁ x₁ C₂ x₂ f _f g _g (unif_eq_fn_hole B₁ C₁ x₁ B₂ C₂ x₂ f _f g _g)).size < (DCC? (Unify τ₁ τ₂ (= ((Π B₁ C₁) x₁) f _f) (= ((Π B₂ C₂) x₂) g _g))).size := by
          unfold unif_eq_fn_preimage
          simp [size, h_size_eq₁]
          grind
        match step_unify? (unif_eq_fn_preimage C₁ x₁ C₂ x₂ f _f g _g (unif_eq_fn_hole B₁ C₁ x₁ B₂ C₂ x₂ f _f g _g)) with
        | .some ⟨_, h₁⟩ =>
          .some ⟨_, .fn_eq h₁ ⟨reduce_sound rfl, reduce_norm rfl⟩ (by grind)⟩
        | .none => .none
    | DCC? (Unify A B (! A₁) (! A₂)) =>
      if heq : (reduce RedAff (DCC? (! A₁))).fst = (reduce RedAff (DCC? (! A₂))).fst then
        .some ⟨_, .refl (RedAffNorm.mk (reduce_sound_fst heq) (reduce_norm_fst heq)) ⟨reduce_sound rfl, reduce_norm rfl⟩ ⟨reduce_sound rfl, reduce_norm rfl⟩⟩
      else
        let τ₁ := (reduce RedAff A₁).fst
        let τ₂ := (reduce RedAff A₂).fst
        have h_dec₁ := decreasing? _ (reduce RedAff A₁).snd.down
        have h_dec₂ := decreasing? _ (reduce RedAff A₂).snd.down
        match step_unify? (DCC? (Unify (? τ₁) (? τ₂) τ₁ τ₂)) with
        | .some ⟨_, h₁⟩ =>
          .some ⟨_, .bang ⟨reduce_sound rfl, reduce_norm rfl⟩
                          ⟨reduce_sound rfl, reduce_norm rfl⟩
                          h₁
                          ⟨reduce_sound rfl, reduce_norm rfl⟩
                          ⟨reduce_sound rfl, reduce_norm rfl⟩
                          ⟨reduce_sound rfl, reduce_norm rfl⟩
                          (by grind)⟩
        | .none => .none
    | (DCC? (Unify A B ((Π B₁ C₁) x₁) ((Π B₂ C₂) x₂))) =>
      if heq : (reduce RedAff (DCC? ((Π B₁ C₁) x₁))).fst = (reduce RedAff (DCC? ((Π B₂ C₂) x₂))).fst then
        .some ⟨_, .refl (RedAffNorm.mk (reduce_sound_fst heq) (reduce_norm_fst heq)) ⟨reduce_sound rfl, reduce_norm rfl⟩ ⟨reduce_sound rfl, reduce_norm rfl⟩⟩
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
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
          .some ⟨_, .fn ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         h₁
                         h₂
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         (by grind)⟩
        | _, _ => .none
    | (DCC? (Unify A B (Σ B₁) (Σ B₂))) =>
      if heq : (reduce RedAff (DCC? (Σ B₁))).fst = (reduce RedAff (DCC? (Σ B₂))).fst then
        .some ⟨_, .refl (RedAffNorm.mk (reduce_sound_fst heq) (reduce_norm_fst heq)) ⟨reduce_sound rfl, reduce_norm rfl⟩ ⟨reduce_sound rfl, reduce_norm rfl⟩⟩
      else
        let hole := (mk_hole_sigma B₁ B₂)
        let τ₁   := (reduce RedAff B₁).fst
        let τ₂   := (reduce RedAff B₂).fst
        let τ₃   := (reduce RedAff (DCC? (B₁ hole))).fst
        let τ₄   := (reduce RedAff (DCC? (B₂ hole))).fst

        have h_dec₁ := decreasing? _ (reduce RedAff B₁).snd.down
        have h_dec₂ := decreasing? _ (reduce RedAff B₂).snd.down
        have h_dec₃ := decreasing? _ (reduce RedAff (DCC? (B₁ hole))).snd.down
        have h_dec₄ := decreasing? _ (reduce RedAff (DCC? (B₂ hole))).snd.down

        match step_unify? (DCC? (Unify (? τ₁) (? τ₂) τ₁ τ₂)), step_unify? (DCC? (Unify (? τ₃)
                                                         (? τ₄)
                                                         τ₃
                                                         τ₄)) with
        | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
          .some ⟨_, .sigma ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         h₁
                         h₂
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         ⟨reduce_sound rfl, reduce_norm rfl⟩
                         (by grind)⟩
        | _, _ => .none-/
    | e =>
      if heq₀ : is_unif? e = .none then
        match cases_point_arity' e with
        | .inl ⟨heq⟩ =>
          if heq_app : view_app? e = .none then
            .some ⟨_, .no_step (fun h => by simp_all [h.complete]) heq (fun h => by simp_all [h.complete])⟩
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
          | .some ⟨_, h⟩ =>
            .some ⟨_, .point₁ (fun h => by simp_all [h.complete]) (by grind) h⟩
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
          | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
            .some ⟨_, .point₂ (fun h => by simp_all [h.complete]) (by grind) h₁ h₂⟩
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
          | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
            match e.points[2].step_unify? with
            | .some ⟨_, h₃⟩ =>
              .some ⟨_, .point₃ (fun h => by simp_all [h.complete]) (by grind) h₁ h₂ h₃⟩
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
          | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
            match e.points[2].step_unify?, e.points[3].step_unify? with
            | .some ⟨_, h₃⟩, .some ⟨_, h₄⟩ =>
              .some ⟨_, .point₄ (fun h => by simp_all [h.complete]) (by grind) h₁ h₂ h₃ h₄⟩
            | _, _ => .none
          | _, _ => .none
      else .none
termination_by (e.size, sizeOf e)
decreasing_by
  any_goals (grind [size, mk_hole, mk_hole_sigma])

theorem RedAffNorm.heq (h₁ : RedAffNorm A B) (h₂ : RedAffNorm A C) : h₁ ≍ h₂ := by
  have heq₁ := h₁.complete
  have heq₂ := h₂.complete
  cases h₁.out_eq
  cases h₂.out_eq
  have heq₃ := h₁.eq
  have heq₄ := h₂.eq
  cases heq₃
  cases heq₄
  grind

@[dcc_reduce]
def RedAffNorm.eq' {e : GenericExpr τ} (hr : RedAffNorm e (red_aff e)) : hr = ⟨reduce_sound rfl, reduce_norm rfl⟩ :=
  match hr with
  | ⟨hr, hn⟩ => by
    have heq := reduce_complete hr hn
    grind

/-def RedUnify.complete {e e' : GenericExpr τ} [DecidableEq τ] (h : RedUnify e e') : step_unify? e = .some ⟨e', h⟩ := by
  unfold step_unify?
  split
  case h_1 heq =>
    simp [step_unify_view?] at heq
    split at heq
    case h_1 =>
      sorry
    case h_2 =>
      split at heq
      case h_1 =>
        cases heq
        cases h
        · expose_names
          cases a.complete_fst
          simp
          apply RedAffNorm.ext
        any_goals (
          focus
          try (
            rename_i hn
            exact (hn (by constructor)).elim)
          done)
        any_goals (grind)
      case h_2 =>
        split at heq
        case h_1 | h_2 =>
          split at heq
          case h_1 =>
            cases h
            any_goals (
              focus
              try (
                expose_names
                cases a.complete_fst.symm.trans heq_2
                try (cases a_1.complete_fst.symm.trans heq_3)))
            any_goals (
              focus
              try (
                expose_names
                cases a_2.complete_fst.symm.trans heq_2)
              done)
            any_goals(
              focus
              try (
                cases heq
                cases a_2.complete_fst
                congr! <;> apply RedAffNorm.ext)
              done)
            any_goals (
              focus
              try (
                expose_names
                exact (h_1 (by constructor)).elim))
          · grind
        · grind
      · grind
  case h_2 heq' =>
    
    split
    case h_1 =>
      
      sorry
    · split
      case isTrue heq' =>
        
        sorry
      case isFalse hneq =>
        sorry -/

set_option maxHeartbeats 2000000000000 in
def RedUnify.complete {e e' : GenericExpr τ} [DecidableEq τ] (h : RedUnify e e') : step_unify? e = .some ⟨e', h⟩ := by
  induction h with
  | refl =>
    expose_names
    unfold step_unify?
    unfold step_unify_view?
    simp [unify_refl?, a.complete_fst, a_1.complete_fst]
    cases a.complete_fst
    cases a_2.complete_fst
    simp
    simp [a.eq', a_2.eq']
    apply RedAffNorm.ext
  | env hrt  =>
    unfold step_unify?
    unfold step_unify_view?
    simp [unify_refl?, hrt.complete_fst]
    cases hrt.complete_fst
    congr!
    apply RedAffNorm.ext
  | prop_bot hrta hrtb hrt =>
    unfold step_unify?
    unfold step_unify_view?
    have h₁ := hrta.complete_fst
    have h₂ := hrtb.complete_fst
    have h₃ := hrt.complete_fst
    simp [unify_refl?, hrta.complete_fst, hrtb.complete_fst]
    split
    case h_1 heq' =>
      split at heq'
      · split at heq'
        case h_1 =>
          cases heq'
          simp [h₃]
          congr!
          · apply RedAffNorm.ext
          · apply RedAffNorm.ext
          · apply RedAffNorm.heq
        · grind
      · grind
      · grind
    case h_2 heq' =>
      split at heq'
      case h_1 =>
        split at heq'
        · grind
        · grind
      · grind
      · grind
  | type_bot hrta hrtb hrt =>
    unfold step_unify?
    unfold step_unify_view?
    have h₁ := hrta.complete_fst
    have h₂ := hrtb.complete_fst
    have h₃ := hrt.complete_fst
    simp [unify_refl?, hrta.complete_fst, hrtb.complete_fst]
    split
    case h_1 heq' =>
      split at heq'
      · grind
      · split at heq'
        case h_1 heq₁ heq₂ =>
          cases heq'
          cases heq₁.symm.trans h₁
          simp [h₃]
          congr!
          · apply RedAffNorm.ext
          · apply RedAffNorm.ext
          · apply RedAffNorm.heq
        · grind
      · grind
    case h_2 heq' =>
      split at heq'
      case h_1 =>
        split at heq'
        · grind
        · grind
      · grind
      · grind
  | fn_eq hr₁ hrt ih =>
    unfold step_unify?
    unfold step_unify_view?
    simp [unify_refl?]
    expose_names
    have hneq : ¬ ((reduce RedAff X₂).fst = (reduce RedAff X₁).fst) := fun h => by
      have h₁ := hr₁.complete_fst
      have h₂ := hrt.complete_fst
      grind
    simp [hneq]
    have hneq₂ : ¬ ((reduce RedAff X₁).fst = (reduce RedAff X₂).fst) := fun h => by
      grind
    simp [hneq₂]
    cases a.complete_fst
    simp [a.eq']
    have h₁ := hr₁.complete_fst
    have h₂ := hrt.complete_fst
    have h₃ := hr₁.complete
    have h₃ := hrt.complete
    simp [h₁, h₂]
    split
    case h_1 heq' =>
      cases heq'.symm.trans h₁
      split
      case h_1 heq' =>
        cases heq'.symm.trans h₂
        · simp [h_unify_ih]
          constructor <;> apply RedAffNorm.ext
      grind
    any_goals (grind)
  | bang hrt₁ hrt₂ hr₁ hrt₃ hrt₄ hrt₅ hneq ih =>
    unfold step_unify?
    unfold step_unify_view?
    simp [unify_refl?]
    expose_names
    have hneq₁ : (reduce RedAff X₂).fst ≠ (reduce RedAff X₁).fst := fun h => by
      have h₁ := hrt₁.complete_fst
      have h₂ := hrt₂.complete_fst
      grind
    have hneq₂ : (reduce RedAff X₁).fst ≠ (reduce RedAff X₂).fst := fun h => by
      grind
    simp [hneq₁, hneq₂]
    split
    case h_1 heq' =>
      split at heq'
      · cases hrt₁.complete_fst.symm.trans (by assumption)
      · cases hrt₁.complete_fst.symm.trans (by assumption)
      · grind
    case h_2 =>
      split
      case h_1 => cases hrt₁.complete_fst.symm.trans (by assumption)
      case h_2 =>
        cases hrt₁.complete_fst.symm.trans (by assumption)
        split
        · cases hrt₂.complete_fst.symm.trans (by assumption)
          have heq₁ : τ₁ = (reduce RedAff A₁).fst := by
            have h := hr₁.complete
            grind
          have heq₂ : τ₂ = (reduce RedAff A₂).fst := by
            have h := hrt₃.complete
            grind
          have heq₃ : A' = (reduce RedAff A).fst := by
            have h := hrt₅.complete
            grind
          have heq₄ : B' = (reduce RedAff B).fst := by
            have h := hneq.complete
            grind
          subst heq₁
          subst heq₂
          subst heq₃
          subst heq₄
          simp [h_unif_ih, ih.complete_fst]
          congr!
          · exact ih.complete_fst
          any_goals (apply RedAffNorm.ext)
          · cases ih.out_eq
            simp [ih.eq]
            apply RedAffNorm.ext
        case h_2 hn =>
          exact (hn _ (RedAffNorm.complete_fst (by assumption))).elim
      case h_3 | h_4 =>
        cases hrt₁.complete_fst.symm.trans (by assumption)
      case h_5 hn₁ hn₂ hn₃ => exact (hn₁ _ (RedAffNorm.complete_fst (by assumption))).elim
    /-
    simp [ih]
    simp [hrt₁.eq', hrt₂.eq', hrt₃.eq', hrt₄.eq', hrt₅.eq']-/
  | fn hrt₁ hrt₂ hrt₃ hrt₄ hr₁ hr₂ hrta hrtb hrt hneq ih =>
    unfold step_unify?
    unfold step_unify_view?
    simp [unify_refl?]
    expose_names
    have hneq₁ : (reduce RedAff X₂).fst ≠ (reduce RedAff X₁).fst := fun h => by
      have h₁ := hrt₁.complete_fst
      have h₂ := hrt₂.complete_fst
      grind
    have hneq₂ : (reduce RedAff X₁).fst ≠ (reduce RedAff X₂).fst := fun h => by
      grind
    simp [hneq₁, hneq₂]
    split
    case h_1 heq' =>
      split at heq'
      · cases hrt₁.complete_fst.symm.trans (by assumption)
      · cases hrt₁.complete_fst.symm.trans (by assumption)
      · grind
    case h_2 =>
      split
      case h_1 => cases hrt₁.complete_fst.symm.trans (by assumption)
      case h_2 => cases hrt₁.complete_fst.symm.trans (by assumption)
      case h_3 =>
        cases hrt₁.complete_fst.symm.trans (by assumption)
        split
        · cases hrt₂.complete_fst.symm.trans (by assumption)
          have heq₁ : τ₁ = (reduce RedAff (B₁.app x₁)).fst := by
            have h := hrt₃.complete
            grind
          have heq₂ : τ₂ = (reduce RedAff (B₂.app x₂)).fst := by
            have h := hrt₄.complete
            grind
          have heq₃ : A' = (reduce RedAff A).fst := by
            have h := hrt.complete
            grind
          have heq₄ : B' = (reduce RedAff B).fst := by
            have h := hneq.complete
            grind
          have heq₅ : τ₃ = (reduce RedAff ((C₁.app x₁).app (B₁.mk_hole C₁ x₁ B₂ C₂ x₂))).fst := by
            have h := hr₁.complete
            grind
          have heq₆ : τ₄ = (reduce RedAff ((C₂.app x₂).app (B₁.mk_hole C₁ x₁ B₂ C₂ x₂))).fst := by
            have h := hr₂.complete
            grind
          subst heq₁
          subst heq₂
          subst heq₃
          subst heq₄
          subst heq₅
          subst heq₆
          simp [h_unif_dom_ih, h_unif_cod_ih, ih.complete_fst]
          congr!
          · exact ih.complete_fst
          any_goals (apply RedAffNorm.ext)
          · cases ih.out_eq
            simp [ih.eq]
            apply RedAffNorm.ext
        case h_2 hn =>
          exact (hn _ _ _ (RedAffNorm.complete_fst (by assumption))).elim
      case h_4 =>
        cases hrt₁.complete_fst.symm.trans (by assumption)
      case h_5 hn₁ hn₂ hn₃ => exact (hn₂ _ _ _ (RedAffNorm.complete_fst (by assumption))).elim
  | sigma hrt₁ hrt₂ hrt₃ hrt₄ hr₁ hr₂ hrt hrta hrtb hneq ih =>
    unfold step_unify?
    unfold step_unify_view?
    simp [unify_refl?]
    expose_names
    have hneq₁ : (reduce RedAff X₂).fst ≠ (reduce RedAff X₁).fst := fun h => by
      have h₁ := hrt₁.complete_fst
      have h₂ := hrt₂.complete_fst
      grind
    have hneq₂ : (reduce RedAff X₁).fst ≠ (reduce RedAff X₂).fst := fun h => by
      grind
    simp [hneq₁, hneq₂]
    split
    case h_1 heq' =>
      split at heq'
      · cases hrt₁.complete_fst.symm.trans (by assumption)
      · cases hrt₁.complete_fst.symm.trans (by assumption)
      · grind
    case h_2 =>
      split
      case h_1 | h_2 | h_3 => cases hrt₁.complete_fst.symm.trans (by assumption)
      case h_4 =>
        cases hrt₁.complete_fst.symm.trans (by assumption)
        split
        · cases hrt₂.complete_fst.symm.trans (by assumption)
          have heq₁ : τ₁ = (reduce RedAff B₁).fst := by
            have h := hrt₃.complete
            grind
          have heq₂ : τ₂ = (reduce RedAff B₂).fst := by
            have h := hrt₄.complete
            grind
          have heq₃ : A' = (reduce RedAff A).fst := by
            have h := hrtb.complete
            grind
          have heq₄ : B' = (reduce RedAff B).fst := by
            have h := hneq.complete
            grind
          have heq₅ : τ₃ = (reduce RedAff (B₁.app (B₁.mk_hole_sigma B₂))).fst := by
            have h := hr₁.complete
            grind
          have heq₆ : τ₄ = (reduce RedAff (B₂.app (B₁.mk_hole_sigma B₂))).fst := by
            have h := hr₂.complete
            grind
          subst heq₁
          subst heq₂
          subst heq₃
          subst heq₄
          subst heq₅
          subst heq₆
          simp [h_unif_fst_ih, h_unif_snd_ih, ih.complete_fst]
          congr!
          · exact ih.complete_fst
          any_goals (apply RedAffNorm.ext)
          · cases ih.out_eq
            simp [ih.eq]
            apply RedAffNorm.ext
        case h_2 hn =>
          exact (hn _ (RedAffNorm.complete_fst (by assumption))).elim
      case h_5 hn₁ hn₂ hn₃ => exact (hn₃ _ (RedAffNorm.complete_fst (by assumption))).elim
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
        case cong_env =>
          cases x
          case app =>
            expose_names
            cases a_4
            case cong_mk => exact (h (by constructor)).elim
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
            exact (h .mk).elim
          · grind
        · grind
      case h_2 =>
        unfold point_arity at heq_ar
        split at heq_ar
        any_goals (grind)
        case _ =>
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
      case h_2 => exact (h .mk).elim
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

inductive Unify : (e : GenericExpr τ) → (e' : GenericExpr τ) → Type u
  | step : RedUnify e e' → Unify e e'
  | refl : (∀ ⦃e'⦄, RedUnify e e' → False) → Unify e e
deriving Repr

def reduce_unify [DecidableEq τ] (e : GenericExpr τ) : ((e' : GenericExpr τ) × Unify e e') :=
  match heq : step_unify? e with
  | .some ⟨_, h⟩ => ⟨_, .step h⟩
  | .none => ⟨_, .refl (fun _ h => by simp_all [h.complete])⟩

def Unify.complete [DecidableEq τ] {e e' : GenericExpr τ} (h : Unify e e') : reduce_unify e = ⟨e', h⟩ := by
  cases h with
  | step h =>
    have heq := h.complete
    simp [reduce_unify]
    grind
  | refl hn =>
    have heq : step_unify? e = .none := by
      apply Option.eq_none_iff_forall_ne_some.mpr
      intro ⟨_, h'⟩
      exact (hn h').elim
    simp [reduce_unify]
    grind

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

To match any arrow:
(Unify ((Π B₁ C₁) x₁) (Π B₁ (`(Dom B₁) (`(B₁ x₁) (C₁ x₁ hole))))

No hole unification needed really.
-/
