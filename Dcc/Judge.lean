import Dcc.Ast
import Dcc.Red
import Dcc.Types

inductive DefEqError where
  /-| pi_left  (expected actual : Expr)  : DefEqError A B
  | pi_right (expected actual : Expr)  : DefEqError A B
  | bang     (inner_errr      : DefEqError τ₁ τ₂) : DefEqError (DCC !(τ₁)) (DCC !(τ₂))
  | coup     (inner_errr      : DefEqError τ₁ τ₂) : DefEqError (DCC Coup(τ₁)) (DCC Coup(τ₂))-/
  | tm       (expected actual : Expr)  : DefEqError
deriving DecidableEq, Repr

def DefEqError.toFormat (err : DefEqError) : Std.Format :=
  match err with
  | .tm A B => A.toFormat ++ " ≠ " ++ (.nest 2 <| B.toFormat)
  /-"- " ++ (.nest 2 <| (Std.format A) ++ " ≠ " ++ (.indentD (Std.format B)) ++ .line ++
  (match err with
  /-| .pi_left expected actual => "because Π domains are not def-eq. Expected: " ++ (.indentD (Std.format expected)) ++ "but found: " ++ (.indentD (Std.format actual))
  | .pi_right expected actual => "because Π codomains are not def-eq. Expected: " ++ (.indentD (Std.format expected)) ++ "but found: " ++ (.indentD (Std.format actual))
  | .bang inner_err => "because bang types are not def-eq because: " ++ inner_err.toFormat
  | .coup inner_err => "because coup types are not def-eq because: " ++ inner_err.toFormat-/
  | .tm expected actual => "because terms are not def-eq. Expected: " ++ (.indentD (Std.format expected)) ++ .line ++ "but found: " ++ (.indentD (Std.format actual))))-/

instance : Std.ToFormat (DefEqError) := ⟨DefEqError.toFormat⟩
instance : ToString (DefEqError) := ⟨toString ∘ Std.format⟩

inductive TypeError : (e : Expr) → Type where
  | mismatch (expected actual at_e : Expr) : TypeError e
  | unexpected (found at_e : Expr) : TypeError e
  | sub (at_e : Expr) (err : TypeError at_e) : TypeError e
  | def_eq (err : DefEqError) : TypeError e
  | mark (n : ℕ) (ε : TypeError e) : TypeError e
deriving Repr

def TypeError.toFormat (err : TypeError e) : Std.Format :=
  "- Term is not well-typed:" ++ (Std.Format.indentD
    (match err with
    | .mismatch expected actual at_e => (Std.Format.text "terms are mismatched at: ")
      ++ (Std.Format.indentD (Std.format at_e)) ++ Std.Format.line
      ++ "because: " ++ (Std.format expected) ++ " ≠ " ++ (Std.Format.indentD (Std.format actual))
    | .unexpected found at_e => "because an unexpected term was found at: "
      ++ (Std.Format.indentD (Std.format at_e)) ++ Std.Format.line
      ++ "found: " ++ (.indentD (Std.format found))
    | .sub at_e inner_err => "because of a sub-error at: "
      ++ (Std.Format.indentD (Std.format at_e)) ++ (.indentD inner_err.toFormat)
    | .def_eq inner_err => "because terms were not def-eq: " ++ (.indentD (Std.format inner_err))
    | .mark n ε => (Std.Format.text s!"[{n}] ") ++ ε.toFormat
  )
  ++ .line ++ "at term: " ++ (Std.format e))

instance {e : Expr} : Std.ToFormat (TypeError e) := ⟨TypeError.toFormat⟩
instance {e : Expr} : ToString (TypeError e) := ⟨toString ∘ Std.format⟩
instance {e : Expr} : Repr (TypeError e) := ⟨fun e _n => TypeError.toFormat e⟩

namespace Dsl

open Expr

syntax gen_dcc "→ᵦ" gen_dcc : term

macro_rules
  | `($A:gen_dcc →ᵦ $B:gen_dcc) => `(RedNorm (DCC $A) (DCC $B))

end Dsl

namespace Expr

@[inline, dcc_force_reduce]
abbrev reduce_all (e : Expr) : Expr :=
  (reduce Red e).fst

def reduce_reduces {A B : Expr} (h : reduce_all A = B) : A →ᵦ B := by
  simp [reduce_all] at h
  exact ⟨h ▸ reduce_sound rfl, h ▸ reduce_norm rfl⟩

def RedNorm.eq' (h : RedNorm A (reduce Red A).fst) : reduce_reduces heq₀ = h := by
  simp [reduce_reduces]

/-
Need an inductive to detect quotation that also includes
∘ quot
-/

open Dsl in
inductive QuotSort : Expr → Expr → Level → Type
  | mk   : QuotSort (DCC (`B (Sort u))) B u
  | nest : QuotSort x B u → QuotSort (DCC (∘ x y)) B u
deriving Repr

def QuotSort.app (h : QuotSort e B u) : RedNorm (DCC (e x)) (DCC (Sort u)) :=
  match h with
  | .mk => ⟨.single .quot, fun ⟨_, h⟩ => nomatch h⟩
  | .nest (x := f) (y := g) h =>
    have h := h.app (x := (g.app x))
    ⟨.trans (.single .comp) h.1, h.2⟩

def QuotSort.is_norm (h : QuotSort e B u) (hn : IsNorm Red e) : IsNorm Red B :=
  match h with
  | .mk => fun ⟨_, h⟩ => hn ⟨_, .point 0 (by grind) h⟩
  | .nest h₀ => h₀.is_norm (fun ⟨_, h⟩ => hn ⟨_, .point 0 (by grind) h⟩)

def read_quot_sort (e : Expr) : Except (TypeError e) (Σ (B : Expr) (u : Level), QuotSort e B u) :=
  open Dsl in match e with
  | DCC (`_B (Sort _u)) => .ok ⟨_, _, .mk⟩
  | DCC (∘ x _y) =>
    match x.read_quot_sort with
    | .ok ⟨_, _, h⟩ => .ok ⟨_, _, .nest h⟩
    | .error e => .error (.sub x e)
  | e => .error (.unexpected e e)

def view_quot_sort (e B : Expr) : Except (TypeError e) (Σ (u : Level), QuotSort e B u) :=
  match read_quot_sort e with
  | .ok ⟨B', _u, h⟩ =>
    if heq : B' = B then
      .ok ⟨_, heq ▸ h⟩
    else .error (.mismatch B B' e)
  | .error e => .error e

def QuotSort.complete (h : QuotSort e B u) : read_quot_sort e = .ok ⟨B, u, h⟩ := by
  induction h with
  | mk => simp [read_quot_sort]
  | nest h ih => simp [read_quot_sort, ih]

def QuotSort.complete₁ (h : QuotSort e B u) : view_quot_sort e B = .ok ⟨u, h⟩ := by
  have heq := h.complete
  simp [view_quot_sort, heq]

#eval Std.format <| pair.β.type (DCC (Sort 30)) 10 20

-- For checking arguments under apps
open Dsl in inductive DefEq : Expr → Expr → Type
  | tm : (τ₁ →ᵦ τ₃) → (τ₂ →ᵦ τ₃) → DefEq τ₁ τ₂
deriving Repr

syntax gen_dcc "≡" gen_dcc : term
macro_rules
  | `(term| $A:gen_dcc ≡ $B:gen_dcc) => `(DefEq (DCC $A) (DCC $B))

def DefEq.push_head {A B : Expr} (h : A ≡ C) (hr : Red A B) : B ≡ C :=
  match h with
  | ⟨hr₁, hr₂⟩ =>
    ⟨.push_head hr₁ hr, hr₂⟩

def DefEq.symm {A B : Expr} (h₁ : A ≡ B) : B ≡ A :=
  match h₁ with
  | ⟨hr₁, hr₂⟩ => ⟨hr₂, hr₁⟩

def DefEq.trans {A B C : Expr} (h₁ : A ≡ B) (h₂ : B ≡ C) : A ≡ C :=
  match h₁, h₂ with
  | ⟨hr₁, hr₂⟩, ⟨hr₃, hr₄⟩ => ⟨hr₁, RedNorm.unique hr₂ hr₃ ▸ hr₄⟩

-- Reduces A B → DefEq A B

def def_eq? (τ₁ τ₂ : Expr) : Except (DefEqError) (DefEq τ₁ τ₂) :=
  if heq : reduce_all τ₁ = reduce_all τ₂ then
    .ok ⟨reduce_reduces heq, reduce_reduces rfl⟩
  else .error (.tm τ₁ τ₂)

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def DefEq.complete {τ₁ τ₂ : Expr} (h : DefEq τ₁ τ₂) : def_eq? τ₁ τ₂ = .ok h := by
  induction h
  case tm hr₁ hr₂ =>
    expose_names
    have heq₁ := RedNorm.complete hr₁
    have heq₂ := RedNorm.complete hr₂
    simp [def_eq?, reduce_all, heq₁, heq₂]
    constructor <;> apply RedNorm.heq

open Dsl in
inductive Arrow : Expr → Expr → Expr → Type
  | simple : A →ᵦ A' → B →ᵦ B' → Arrow A' B' (DCC (→ A B))
deriving Repr

open Dsl in
inductive ArrowSort : Expr → Level → Expr → Type
  | mk : (B xA) →ᵦ A' → (C xA (hole (C.max_hole))) →ᵦ (Sort v) → ArrowSort A' v (DCC ((Π B C) xA))
deriving Repr

def ArrowSort.is_norm (h : ArrowSort A u τ) : IsNorm Red A :=
  match h with
  | ⟨h₁, h₂⟩ => h₁.is_norm

def read_arrow_sort (τ : Expr) : Except (TypeError τ) (Σ (A : Expr) (v : Level), ArrowSort A v τ) :=
  open Dsl in match τ with
  | (DCC ((Π _B C) x)) =>
    match heq₁ : (reduce_all (DCC (C x (hole C.max_hole)))) with
    | DCC Sort _v =>
      .ok ⟨_, _, (reduce_reduces rfl), (reduce_reduces heq₁)⟩
    | τ₀ => .error (.unexpected τ₀ τ)
  | τ => .error (.unexpected τ τ)

def view_arrow_sort₁ (τ A : Expr) : Except (TypeError τ) (Σ (v : Level), ArrowSort A v τ) :=
  match read_arrow_sort τ with
  | .ok ⟨A', _v, h⟩ =>
    if heq : A' = A then
      .ok ⟨_, heq ▸ h⟩
    else
      .error (.sub τ (.mismatch A' A τ))
  | .error e => .error e

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
def ArrowSort.read_complete (h : ArrowSort A v τ) : read_arrow_sort τ = .ok ⟨A, v, h⟩ := by
  cases h with
  | mk hrt₁ hrt₂ =>
    have h₁ := hrt₁.complete_fst
    have h₂ := hrt₂.complete_fst
    simp [read_arrow_sort, reduce_all]
    split
    case h_1 heq' =>
      cases heq'.symm.trans h₂
      cases h₁
      simp [reduce_reduces]
    case h_2 hn =>
      exact (hn _ (by assumption)).elim

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
def ArrowSort.view_complete (h : ArrowSort A v τ) : view_arrow_sort₁ τ A = .ok ⟨v, h⟩ := by
  have heq := ArrowSort.read_complete h
  cases h with
  | mk hrt₁ hrt₂ =>
    have h₁ := hrt₁.complete_fst
    have h₂ := hrt₂.complete_fst
    cases h₁
    simp [view_arrow_sort₁, heq]

open Dsl in
inductive Arrow' : Expr → Expr → Expr → Type
  | simple : A →ᵦ A' → B →ᵦ B' → Arrow' A' B' (DCC (→ A B))
  | curr   : (fB xA) →ᵦ A' → B →ᵦ B' → Arrow' A' B' (DCC ((Π fB (Λ τA fB (`(Σ τA fB) B))) xA))
deriving Repr

open Dsl in
inductive Sigma'.C.type : Expr → Expr → Level → Expr → Type
  | mk : QuotSort C (DCC (Σ A B)) s → Sigma'.C.type A B s (DCC ((Π (`𝟙 A) (`𝟙 (Π B (Λ A B C)))) ∗))
deriving Repr

open Dsl in
def Sigma'.C.type.is_norm (h : Sigma'.C.type A B s τ) (hn : IsNorm Red τ) : (IsNorm Red A) ×' (IsNorm Red B) :=
  match h with
  | .mk _h_quot => ⟨fun ⟨_, h⟩ => hn ⟨_, .congrFun (.point 0 (by point_arity) (.point 1 (by point_arity) h))⟩, fun ⟨_, h⟩ => hn ⟨_, .congrFun (.point 1 (by point_arity) (.point 1 (by point_arity) (.point 0 (by change 0 < point_arity (DCC (Π B (Λ A B (`(Σ A B) (Sort s))))); grind) h)))⟩⟩

def read_sigma'_C_type (τ : Expr) : Except (TypeError τ) ((A : Expr) × (B : Expr) × (u : Level) × Sigma'.C.type A B u τ) :=
  open Dsl in match τ with
  | (DCC ((Π (`𝟙 A) (`𝟙 (Π B (Λ __A __B C)))) ∗)) =>
    if heq : (DCC ((Π (`𝟙 A) (`𝟙 (Π B (Λ __A __B C)))) ∗)) = (DCC ((Π (`𝟙 A) (`𝟙 (Π B (Λ A B C)))) ∗)) then
      match C.view_quot_sort (DCC (Σ A B)) with
      | .ok ⟨_, h_quot⟩ =>
        .ok ⟨_, _, _, heq ▸ (Sigma'.C.type.mk h_quot)⟩
      | .error e => .error (.sub C e)
    else
      .error (.unexpected τ (DCC ((Π (`𝟙 A) (`𝟙 (Π B (Λ __A __B C)))) ∗)))
  | τ => .error (.unexpected τ τ)

def view_sigma'_C_type (τ A B : Expr) : Except (TypeError τ) ((u : Level) × Sigma'.C.type A B u τ) :=
  match read_sigma'_C_type τ with
  | .ok ⟨A', B', _u, h⟩ =>
    if heq₁ : A = A' then
      if heq₂ : B = B' then
        .ok ⟨_, heq₁ ▸ heq₂ ▸ h⟩
      else .error (.mismatch B B' τ)
    else
      .error (.mismatch A A' τ)
  | .error e => .error e

def view_sigma'_C_type₁ (τ B : Expr) : Except (TypeError τ) ((A : Expr) × (u : Level) × Sigma'.C.type A B u τ) :=
  match read_sigma'_C_type τ with
  | .ok ⟨_A, B', _u, h⟩ =>
    if heq₁ : B = B' then
      .ok ⟨_, _, heq₁ ▸ h⟩
    else .error (.mismatch B B' τ)
  | .error e => .error e

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
def Sigma'.C.type.complete₂ (h : Sigma'.C.type A B s τ) : view_sigma'_C_type τ A B = .ok ⟨s, h⟩ := by
  match h with
  | ⟨h⟩ => simp [view_sigma'_C_type, read_sigma'_C_type, h.complete₁]

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
def Sigma'.C.type.complete₁ (h : Sigma'.C.type A B s τ) : view_sigma'_C_type₁ τ B = .ok ⟨A, s, h⟩ := by
  match h with
  | ⟨h⟩ => simp [view_sigma'_C_type₁, read_sigma'_C_type, h.complete₁]

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
def Sigma'.C.type.complete₀ (h : Sigma'.C.type A B s τ) : read_sigma'_C_type τ = .ok ⟨A, B, s, h⟩ := by
  match h with
  | ⟨h⟩ => simp [read_sigma'_C_type, h.complete₁]

def Arrow.is_norm (h : Arrow A B τ) (hn : IsNorm Red τ) : (IsNorm Red A) ×' (IsNorm Red B) :=
  match h with
  | .simple h₁ h₂ => ⟨h₁.is_norm, h₂.is_norm⟩

def Arrow'.is_norm (h : Arrow' A B τ) (hn : IsNorm Red τ) : (IsNorm Red A) ×' (IsNorm Red B) :=
  match h with
  | .simple h₁ h₂ => ⟨h₁.is_norm, h₂.is_norm⟩
  | .curr h₁ h₂ => ⟨h₁.is_norm, h₂.is_norm⟩

def Arrow.to_arrow' (h : Arrow A B τ) : Arrow' A B τ :=
  match h with
  | ⟨h₁, h₂⟩ => .simple h₁ h₂

open Dsl in
@[dcc_judge, inline]
def read_arrow (τ : Expr) : Except (TypeError τ) ((A B : Expr) × (Arrow A B τ)) :=
  open Dsl in match τ with
  | DCC ((Π (`𝟙 A) (`𝟙 (`_A B))) ∗) =>
    if heq : (DCC ((Π (`𝟙 A) (`𝟙 (`_A B))) ∗)) = (DCC (→ A B)) then
      heq ▸ .ok ⟨_, _, reduce_reduces rfl, reduce_reduces rfl⟩
    else .error (.unexpected τ τ)
  | _ => .error (.unexpected τ τ)

open Dsl in
@[dcc_judge, inline]
def read_arrow' (τ : Expr) : Except (TypeError τ) ((A B : Expr) × (Arrow' A B τ)) :=
  open Dsl in match τ with
  | DCC ((Π (`𝟙 A) (`𝟙 (`_A B))) ∗) =>
    if heq : (DCC ((Π (`𝟙 A) (`𝟙 (`_A B))) ∗)) = (DCC (→ A B)) then
      heq ▸ .ok ⟨_, _, .simple (reduce_reduces rfl) (reduce_reduces rfl)⟩
    else .error (.unexpected τ τ)
  | (DCC ((Π fB (Λ τA _fB (`(Σ _τA __fB) B))) xA)) =>
    if heq : (DCC ((Π fB (Λ τA _fB (`(Σ _τA __fB) B))) xA)) = (DCC ((Π fB (Λ τA fB (`(Σ τA fB) B))) xA)) then
      heq ▸ .ok ⟨_, _, .curr (reduce_reduces rfl) (reduce_reduces rfl)⟩
    else .error (.unexpected τ (DCC ((Π fB (Λ τA _fB (`(Σ _τA __fB) B))) xA)))
  | _ => .error (.unexpected τ τ)

open Dsl in
@[dcc_judge, inline]
def read_arrow₁ (τ A : Expr) : Except (TypeError τ) ((B : Expr) × (Arrow A B τ)) :=
  match read_arrow τ with
  | .ok ⟨A', _B', h⟩ =>
    if heq : A' = A then
      .ok ⟨_, heq ▸ h⟩
    else
      .error (.mismatch A A' τ)
  | .error e => .error e

open Dsl in
@[dcc_judge, inline]
def read_arrow'₁ (τ A : Expr) : Except (TypeError τ) ((B : Expr) × (Arrow' A B τ)) :=
  match read_arrow' τ with
  | .ok ⟨A', _B', h⟩ =>
    if heq : A' = A then
      .ok ⟨_, heq ▸ h⟩
    else
      .error (.mismatch A A' τ)
  | .error e => .error e

def DefEq.elim_norml {A B : Expr} (h : A ≡ B) (hn : IsNorm Red A) : B →ᵦ A :=
  match h with
  | ⟨hr₁, hr₂⟩ => RedNorm.elim_norm hr₁ hn ▸ hr₂

def DefEq.elim_normr {A B : Expr} (h : A ≡ B) (hn : IsNorm Red B) : A →ᵦ B :=
  match h with
  | ⟨hr₁, hr₂⟩ => RedNorm.elim_norm hr₂ hn ▸ hr₁

def read_arrow₃ (τ A B : Expr) : Except (TypeError τ) (Arrow A B τ) :=
  match read_arrow τ with
  | .ok ⟨A', B', h⟩ =>
    if heq₁ : A' = A then
      if heq₂ : B' = B then
          .ok <| heq₁ ▸ heq₂ ▸ h
      else
        .error (.mismatch A A' τ)
    else
      .error (.mismatch B B' τ)
  | .error e => .error e

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow'.complete (h : Arrow' A B τ) : τ.read_arrow' = .ok ⟨A, B, h⟩ := by
  cases h
  <;> (
    expose_names
    simp only [read_arrow']
    have heq₁ := a.complete_fst
    have heq₂ := a_1.complete_fst
    unfold reduce_all
    aesop)

open Dsl in
@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.read₁_complete {A B τ : Expr} (h : Arrow A B τ) : τ.read_arrow₁ A = .ok ⟨B, h⟩ := by
  cases h
  · expose_names
    simp [read_arrow₁, read_arrow, reduce_all, RedNorm.complete_fst a, RedNorm.complete_fst a_1, reduce_reduces]
    congr!
    · simp [RedNorm.complete_fst a]
    · simp [RedNorm.complete_fst a_1]

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow'.read₁_complete (h : Arrow' A B τ) : τ.read_arrow'₁ A = .ok ⟨B, h⟩ := by
  have heq := h.complete
  cases h
  <;> (
    simp [read_arrow'₁]
    grind)

open Dsl in
@[dcc_judge, inline]
def view_arrow (τ A B : Expr) : Except (TypeError τ) (Arrow A B τ) :=
  match read_arrow τ with
  | .ok ⟨A', B', h⟩ =>
    if heq₁ : A' = A then
      if heq₂ : B' = B then
        .ok (heq₁ ▸ heq₂ ▸ h)
      else
        .error (.mismatch A A' τ)
    else
      .error (.mismatch B B' τ)
  | .error e => .error e

open Dsl in
inductive Pi.C.type' : Expr → Expr → Level → Expr → Type
  | mk : (B xA) →ᵦ A'
    → (C xA (hole (C.max_hole.succ))) →ᵦ ((Π B₂ C₂) xA₂)
    → (C₂ xA₂ (hole (C₂.max_hole.succ))) →ᵦ (Sort v)
    → Pi.C.type' A' B₂ v (DCC ((Π B C) xA))
deriving Repr

def read_pi_C_type (τ : Expr) : Except (TypeError τ) (Σ (A B : Expr) (v : Level), Pi.C.type' A B v τ) :=
  open Dsl in
  match τ with
  | DCC ((Π _B C) xA) =>
    match heq₁ : reduce_all (DCC (C xA (hole (C.max_hole.succ)))) with
    | (DCC ((Π _B₂ C₂) xA₂)) =>
      match heq₂ : reduce_all (DCC (C₂ xA₂ (hole (C₂.max_hole.succ)))) with
      | DCC Sort _v =>
        .ok ⟨_, _, _, .mk (reduce_reduces rfl) (reduce_reduces heq₁) (reduce_reduces heq₂)⟩
      | τ' => .error (.unexpected τ τ')
    | τ' => .error (.unexpected τ τ')
  | τ' => .error (.unexpected τ τ')

def view_pi_C_type (τ A B : Expr) : Except (TypeError τ) (Σ (v : Level), Pi.C.type' A B v τ) :=
  match read_pi_C_type τ with
  | .ok ⟨A', B', _s, h⟩ =>
    if heq₁ : A' = A then
      if heq₂ : B' = B then
        .ok ⟨_, heq₁ ▸ heq₂ ▸ h⟩
      else .error (.mismatch B B' τ)
    else .error (.mismatch A A' τ)
  | .error e => .error e

@[dcc_force_reduce, aesop safe forward (rule_sets := [DccReduce])]
theorem reduce_all_complete (h : A →ᵦ B) : reduce_all A = B := by
  have h := RedNorm.complete_fst h
  grind

@[dcc_force_reduce, aesop safe apply (rule_sets := [DccReduce])]
theorem reduce_all_complete_eq (h : A →ᵦ B) : reduce_reduces heq = h := by
  simp [reduce_reduces]

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
def Pi.C.type'.complete (h : Pi.C.type' A B v τ) : read_pi_C_type τ = .ok ⟨A, B, v, h⟩ := by
  cases h with
  | mk h₁ h₂ h₃ =>
    have heq₁ := reduce_all_complete h₁
    have heq₂ := reduce_all_complete h₂
    have heq₃ := reduce_all_complete h₃
    simp [read_pi_C_type]
    split
    case h_1 heq' =>
      cases heq'.symm.trans heq₂
      split
      case h_1 heq' =>
        cases heq'.symm.trans heq₃
        cases heq₁
        simp_all
        constructor
        · simp [reduce_reduces]
        · constructor <;> simp [reduce_reduces]
      · grind
    · grind

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
def Pi.C.type'.complete₁ (h : Pi.C.type' A B v τ) : view_pi_C_type τ A B = .ok ⟨v, h⟩ := by
  have heq := h.complete
  cases h with
  | mk h₁ h₂ h₃ => simp [view_pi_C_type, heq]

-- (Π(Id(Sort 0), `(Sort 0, Π(`(𝟙, Sort 0), `(𝟙, `(Sort 0, Sort 1))))) 𝟙)
open Dsl in inductive Pi.C.type :
  Expr → Expr → Level → Expr → Type
  | canon  : (fB x) →ᵦ A
    → (fC x) →ᵦ (Π B (Λ A B (`(Σ' A B) Sort v)))
    → Pi.C.type B A v (DCC ((Π fB fC) x))
  | canon' : (fB x) →ᵦ (! A)
    → (fC x) →ᵦ (Π (!<> B) (!Λ A B (`(! (Σ' A B)) Sort v)))
    → Pi.C.type B (DCC (! A)) v (DCC ((Π fB fC) x))
  | arrow  : (fB x) →ᵦ A
    → (fB₂ x₂) →ᵦ A₂
    → (fC₂ x₂) →ᵦ (`A₂ Sort v)
    → (fC x) →ᵦ (`A ((Π fB₂ fC₂) x₂))
    → Pi.C.type (DCC (`A A₂)) A v (DCC ((Π fB fC) x))
  | semi  : (fB x) →ᵦ A
    → (fC x) →ᵦ (Π B (`δ₂ (`δ₃ Sort v)))
    → Pi.C.type B A v (DCC ((Π fB fC) x))
deriving Repr

open Dsl in
@[dcc_judge]
def view_pi_f_β (τ B A : Expr) : Except (TypeError τ) ((v : Level) × (Pi.C.type B A v τ)) :=
  match τ with
  | DCC ((Π fB fC) x) =>
    match heq₁ : (reduce_all (DCC (fB x))), heq₂ : (reduce_all (DCC (fC x))) with
    | A₁, DCC (`_A ((Π fB₂ fC₂) x₂)) =>
      if heq₁' : A₁ = A then
        match heq₃ : reduce_all (DCC (fC₂ x₂)) with
        | DCC (`A₂ Sort _v) =>
          if heq₄ : _A = A₁ then
            if heq₅ : A₂ = (reduce_all (DCC (fB₂ x₂))) then
              have heq₂ := heq₄ ▸ heq₂
              if heq₆ : B = (DCC (`A A₂)) then
                heq₆ ▸ heq₁' ▸ .ok ⟨_, .arrow (reduce_reduces heq₁) (reduce_reduces heq₅.symm) (reduce_reduces heq₃) (reduce_reduces heq₂)⟩
              else .error (.mismatch (DCC (`A A₂)) B τ)
            else .error (.mismatch (reduce_all (DCC (fB₂ x₂))) A₂ τ)
          else .error (.mismatch A _A τ)
        | τ₀ => .error (.unexpected τ τ₀)
      else .error (.mismatch A₁ A τ)
    | A₁, DCC (Π B₂ (`_δ₂ (`_δ₃ Sort _v))) =>
      if heq₁' : A₁ = A then
        if heq₂' : B₂ = B then
           .ok ⟨_, .semi (reduce_reduces (heq₁' ▸ heq₁)) (reduce_reduces (heq₂' ▸ heq₂))⟩
        else .error (.mismatch B B₂ τ)
      else .error (.mismatch A A₁ τ)
    | A₁, DCC (Π B₂ (Λ _A _B (`(Σ' __A __B) Sort v))) =>
      if heq₁' : A₁ = A then
        if heq₂' : DCC (Π B₂ (Λ _A _B (`(Σ' __A __B) Sort v))) = DCC (Π B (Λ A B (`(Σ' A B) Sort v))) then
          .ok ⟨_, .canon (reduce_reduces (heq₁' ▸ heq₁)) (reduce_reduces (heq₂' ▸ heq₂))⟩
        else .error (.mismatch (DCC (Π B (Λ A B (`(Σ' A B) Sort v)))) (DCC (Π B₂ (Λ _A _B (`(Σ' __A __B) Sort v)))) τ)
      else .error (.mismatch A A₁ τ)
    | DCC (! A₁), DCC (Π (!<> B₂) (!Λ _A __B (`(! (Σ' __A ___B)) Sort v))) =>
      if heq₁' : A = (DCC (! A₁)) then
        if heq₂' : (DCC (Π (!<> B₂) (!Λ _A __B (`(! (Σ' __A ___B)) Sort v)))) = (DCC (Π (!<> B) (!Λ A₁ B (`(! (Σ' A₁ B)) Sort v)))) then
          heq₁' ▸ .ok ⟨_, .canon' (reduce_reduces heq₁) (reduce_reduces (heq₂' ▸ heq₂))⟩
        else .error (.mismatch (DCC (Π (!<> B) (!Λ A₁ B (`(! (Σ' A₁ B)) Sort v)))) (DCC (Π (!<> B₂) (!Λ _A __B (`(! (Σ' __A ___B)) Sort v)))) τ)
      else .error (.mismatch A (DCC (! A₁)) τ)
    | _, _ => .error (.unexpected τ τ)
  | _ => .error (.unexpected τ τ)

open Dsl in
@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Pi.C.type.complete {τ : Expr}
  (h : Pi.C.type B A v τ) : view_pi_f_β τ B A = .ok ⟨v, h⟩ := by
  cases h with
  | arrow h₁ h₂ h₃ h₄ =>
    have heq₁ := RedNorm.complete_fst h₁
    have heq₂ := RedNorm.complete_fst h₂
    have heq₃ := RedNorm.complete_fst h₃
    have heq₄ := RedNorm.complete_fst h₄
    simp [view_pi_f_β]
    split
    any_goals (grind)
    case h_1 heq' =>
      cases heq'.symm.trans heq₄
      simp [heq₁, heq₂]
      split
      case h_1 heq' =>
        cases heq'.symm.trans heq₃
        simp
        subst heq₁
        subst heq₂
        simp
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [reduce_reduces]
      · grind
  | semi h₁ h₂ =>
    have heq₁ := RedNorm.complete_fst h₁
    have heq₂ := RedNorm.complete_fst h₂
    simp [view_pi_f_β]
    split
    any_goals (grind)
    case h_2 heq' =>
      cases heq'.symm.trans heq₂
      simp [heq₁]
      constructor <;> simp [reduce_reduces]
  | canon h₁ h₂ =>
    have heq₁ := RedNorm.complete_fst h₁
    have heq₂ := RedNorm.complete_fst h₂
    simp [view_pi_f_β]
    split
    any_goals (grind)
    case h_3 heq' =>
      cases heq'.symm.trans heq₂
      simp [heq₁]
      constructor <;> simp [reduce_reduces]
  | canon' h₁ h₂ =>
    have heq₁ := RedNorm.complete_fst h₁
    have heq₂ := RedNorm.complete_fst h₂
    simp [view_pi_f_β]
    split
    any_goals (grind)
    case h_4 heq₁' heq₂' =>
      cases heq₁'.symm.trans heq₁
      cases heq₂'.symm.trans heq₂
      simp
      constructor <;> simp [reduce_reduces]

open Dsl in
@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.view_complete {A B τ : Expr} (h : Arrow A B τ) : view_arrow τ A B = .ok h := by
  cases h with
  | simple h₁ h₂ =>
    have heq₁ := RedNorm.complete_fst h₁
    have heq₂ := RedNorm.complete_fst h₂
    simp [view_arrow, read_arrow]
    subst heq₁
    subst heq₂
    simp
    constructor <;> simp [reduce_reduces]

open Dsl in
@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce]), aesop safe forward (rule_sets := [DccReduce])]
theorem Arrow.read_complete {A B τ : Expr}
  (h : Arrow A B τ) : τ.read_arrow = .ok ⟨A, B, h⟩ := by
  cases h with
  | simple h₁ h₂ =>
    have heq₁ := RedNorm.complete_fst h₁
    have heq₂ := RedNorm.complete_fst h₂
    simp [read_arrow]
    subst heq₁
    subst heq₂
    simp
    constructor <;> simp [reduce_reduces]

open Dsl in
@[dcc_judge, inline]
abbrev comp.g.type := Arrow

open Dsl in
inductive Curr.x.type : Expr → Expr → Expr → Expr → Type where
  | mk : (B xA) →ᵦ (Σ A' B') → (C xA) →ᵦ C' → Curr.x.type A' B' C' (DCC ((Π B C) xA))
deriving Repr

open Dsl in
inductive Curr'.x.type : Expr → Expr → Expr → Expr → Type where
  | mk : (B xA) →ᵦ (! (Σ A' B')) → (C xA) →ᵦ C' → Curr'.x.type A' B' C' (DCC ((Π B C) xA))
deriving Repr

def read_curr_x_type (τ : Expr) : Except (TypeError τ) (Σ (A B C : Expr), Curr.x.type A B C τ) :=
  open Dsl in match τ with
  | (DCC ((Π B _C) xA)) =>
    match heq₁ : (DCC (B xA)).reduce_all with
    | (DCC (Σ _A' _B')) =>
      .ok ⟨_, _, _, .mk (reduce_reduces heq₁) (reduce_reduces rfl)⟩
    | τ₀ => .error (.unexpected τ₀ τ)
  | τ => .error (.unexpected τ τ)

def read_curr'_x_type (τ : Expr) : Except (TypeError τ) (Σ (A B C : Expr), Curr'.x.type A B C τ) :=
  open Dsl in match τ with
  | (DCC ((Π B _C) xA)) =>
    match heq₁ : (DCC (B xA)).reduce_all with
    | (DCC (! (Σ _A' _B'))) =>
      .ok ⟨_, _, _, .mk (reduce_reduces heq₁) (reduce_reduces rfl)⟩
    | τ₀ => .error (.unexpected τ₀ τ)
  | τ => .error (.unexpected τ τ)

def view_curr_x_type (τ A B C : Expr) : Except (TypeError τ) (Curr.x.type A B C τ) :=
  match read_curr_x_type τ with
  | .ok ⟨A', B', C', h⟩ =>
    if heq₁ : A' = A then
      if heq₂ : B' = B then
        if heq₃ : C' = C then
          .ok (heq₁ ▸ heq₂ ▸ heq₃ ▸ h)
        else .error (.mismatch C C' τ)
      else .error (.mismatch B B' τ)
    else .error (.mismatch A A' τ)
  | .error e => .error e

def view_curr'_x_type (τ A B C : Expr) : Except (TypeError τ) (Curr.x.type A B C τ) :=
  match read_curr_x_type τ with
  | .ok ⟨A', B', C', h⟩ =>
    if heq₁ : A' = A then
      if heq₂ : B' = B then
        if heq₃ : C' = C then
          .ok (heq₁ ▸ heq₂ ▸ heq₃ ▸ h)
        else .error (.mismatch C C' τ)
      else .error (.mismatch B B' τ)
    else .error (.mismatch A A' τ)
  | .error e => .error e

def view_curr_x_type₂ (τ A B : Expr) : Except (TypeError τ) (Σ (C : Expr), Curr.x.type A B C τ) :=
  match read_curr_x_type τ with
  | .ok ⟨A', B', _C', h⟩ =>
    if heq₁ : A' = A then
      if heq₂ : B' = B then
        .ok ⟨_, heq₁ ▸ heq₂ ▸ h⟩
      else .error (.mismatch B B' τ)
    else .error (.mismatch A A' τ)
  | .error e => .error e

def view_curr'_x_type₂ (τ A B : Expr) : Except (TypeError τ) (Σ (C : Expr), Curr'.x.type A B C τ) :=
  match read_curr'_x_type τ with
  | .ok ⟨A', B', _C', h⟩ =>
    if heq₁ : A' = A then
      if heq₂ : B' = B then
        .ok ⟨_, heq₁ ▸ heq₂ ▸ h⟩
      else .error (.mismatch B B' τ)
    else .error (.mismatch A A' τ)
  | .error e => .error e

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce]), aesop safe forward (rule_sets := [DccReduce])]
def Curr.x.type.complete (h : Curr.x.type A B C τ) : read_curr_x_type τ = .ok ⟨A, B, C, h⟩ := by
  cases h with
  | mk h₁ h₂ =>
    have heq₁ := reduce_all_complete h₁
    have heq₂ := reduce_all_complete h₂
    simp [read_curr_x_type]
    split
    case h_1 heq' =>
      cases heq'.symm.trans heq₁
      simp [heq₂]
      congr!
      apply HEq.symm
      apply h₂.heq
    · grind

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce]), aesop safe forward (rule_sets := [DccReduce])]
def Curr.x.type.complete₃ (h : Curr.x.type A B C τ) : view_curr_x_type τ A B C = .ok h := by
  have heq := h.complete
  simp [view_curr_x_type, heq]

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce]), aesop safe forward (rule_sets := [DccReduce])]
def Curr.x.type.complete₂ (h : Curr.x.type A B C τ) : view_curr_x_type₂ τ A B = .ok ⟨C, h⟩ := by
  have heq := h.complete
  simp [view_curr_x_type₂, heq]

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce]), aesop safe forward (rule_sets := [DccReduce])]
def Curr'.x.type.complete (h : Curr'.x.type A B C τ) : read_curr'_x_type τ = .ok ⟨A, B, C, h⟩ := by
  cases h with
  | mk h₁ h₂ =>
    have heq₁ := reduce_all_complete h₁
    have heq₂ := reduce_all_complete h₂
    simp [read_curr'_x_type]
    split
    case h_1 heq' =>
      cases heq'.symm.trans heq₁
      simp [heq₂]
      congr!
      apply HEq.symm
      apply h₂.heq
    · grind

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce]), aesop safe forward (rule_sets := [DccReduce])]
def Curr'.x.type.complete₃ (h : Curr.x.type A B C τ) : view_curr'_x_type τ A B C = .ok h := by
  have heq := h.complete
  simp [view_curr'_x_type, heq]

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce]), aesop safe forward (rule_sets := [DccReduce])]
def Curr'.x.type.complete₂ (h : Curr'.x.type A B C τ) : view_curr'_x_type₂ τ A B = .ok ⟨C, h⟩ := by
  have heq := h.complete
  simp [view_curr'_x_type₂, heq]

def Curr.x.type.is_norm (h : Curr.x.type A B C τ) (h₁ : IsNorm Red τ) : IsNorm Red A ×' IsNorm Red B ×' IsNorm Red C :=
  match h with
  | ⟨h₁, h₂⟩ => ⟨fun ⟨_, h⟩ => h₁.is_norm ⟨_, .point 0 (by grind) h⟩, fun ⟨_, h⟩ => h₁.is_norm ⟨_, .point 1 (by grind) h⟩, h₂.is_norm⟩

def Curr'.x.type.is_norm (h : Curr'.x.type A B C τ) (h₁ : IsNorm Red τ) : IsNorm Red A ×' IsNorm Red B ×' IsNorm Red C :=
  match h with
  | ⟨h₁, h₂⟩ => ⟨fun ⟨_, h⟩ => h₁.is_norm ⟨_, .point 0 (by grind) (.point 0 (by point_arity) h)⟩, fun ⟨_, h⟩ => h₁.is_norm ⟨_, .point 0 (by point_arity) (.point 1 (by point_arity) h)⟩, h₂.is_norm⟩

open Dsl in
inductive Judge : Expr → Expr → Type where
  | eq     : Judge A (DCC (Sort u))
    → Judge x τ₁
    → Judge y τ₂
    → τ₁ ≡ τ₂
    → τ₂ ≡ A
    → Judge (DCC (= A x y)) (DCC Sort 0)
  | refl    : Judge f_α τ_f_α
    → ArrowSort δ m τ_f_α
    → f_α →ᵦ f_α'
    → Judge (DCC (refl f_α)) (Expr.refl.type f_α' δ)
  | eql    : Judge f_α τ_f_α
    → Arrow δ (DCC (Sort m)) τ_f_α
    → f_α →ᵦ f_α'
    → Judge (DCC (Eql f_α)) (eql.type f_α' δ)
  | eq_mk  : Judge f_α τ_f_α
    → Arrow δ (DCC (Sort m)) τ_f_α
    → f_α →ᵦ f_α'
    → Judge (DCC (=' f_α)) (eq_mk.type f_α' δ)
  | id     : Judge α (DCC Sort m)
    → α →ᵦ α'
    → Judge (DCC (Id α)) (id.type α')
  | comp   : Judge g τ_g
    → comp.g.type A B τ_g
    → Judge f (comp.f.type B C)
    → (g →ᵦ g')
    → Judge (DCC (∘ f g)) (comp.type A C g')
  | sigma' : Judge B τ_B
    → Arrow A (DCC (Sort v)) τ_B
    → B →ᵦ B'
    → Judge C τ_C
    → Sigma'.C.type A B' s τ_C
    → Judge (DCC (Σ' B C)) (DCC (→ (! A) (Sort (max v s))))
  | sigma  : Judge A (DCC (Sort u))
    → Judge B (DCC ((Π fB fC) xA))
    → A ≡ (fB xA)
    → (fC xA (#(.hole (DCC ((Π fB fC) xA)).max_hole.succ))) →ᵦ (Sort v)
    → Judge (DCC (Σ A B)) (DCC (Sort (max u v)))
  | fstc   : Judge B τ_B
    → ArrowSort A n τ_B
    → B →ᵦ B'
    → Judge (DCC (Fst B)) (fstc.type A B')
  | sndc    : Judge B τ_B
    → ArrowSort A n τ_B
    → B →ᵦ B'
    → Judge (DCC (Snd B)) (sndc.type A B')
  | mk     : Judge x A
    → Judge B τ_B
    → ArrowSort A n τ_B
    → B →ᵦ B'
    → #(DCC (B' x)) →ᵦ τ₂
    → Judge y τ₂
    → Judge (DCC (,B x y)) (DCC (Σ A B'))
  /-
    Λ(β, x)
    β receives (α, x)
    β : Coup(Sort m, Id(Sort m)) → Sort n
  -/
  | curr   : Judge A (DCC Sort u)
    → Judge B τ_β
    → A →ᵦ A'
    → ArrowSort A' v τ_β
    → Judge x τ_x
    → Curr.x.type A' B' C τ_x
    → B →ᵦ B'
    → Judge (DCC (Λ A B x)) (curr.type A' B' C)
  | curr'  : Judge A (DCC Sort u)
    → Judge B τ_B
    → A →ᵦ A'
    → ArrowSort A' v τ_B
    → Judge x τ_x
    → Curr'.x.type A' B' C τ_x
    → B →ᵦ B'
    → Judge (DCC (!Λ A B x)) (curr'.type A' B' C)
  -- !<f> &(x) = !(x)
  /-| map    : Judge x (DCC (Π(Id(Sort m), f_β) α))
    → Reduces (DCC (f_β α)) (DCC `(α, Sort n))
    → Reduces (DCC ((!(α) : Sort m) → Sort n)) τ
    → Judge (DCC !<x>) τ-/
  | map    : Judge x τ_x
    → Arrow A (DCC Sort n) τ_x
    → Judge (DCC (!<> x)) (DCC (→ (! A) Sort n))
  | fmap   : Judge x (open Dsl in (DCC ((Π f_A f_B) x_A)))
    → (f_A x_A) →ᵦ A
    → (f_B x_A) →ᵦ f_B'
    → Judge (DCC ($<> x)) (open Dsl in (DCC ((Π (`𝟙 (! A)) (`𝟙 (!<> f_B'))) ∗)))
  | unbox  : Judge A (DCC Sort m)
    → A →ᵦ A'
    → Judge (DCC (* A)) (open Dsl in (DCC (→ (! A') A')))
  | eval   : Judge A (DCC Sort u)
    → Judge B τ_β
    → ArrowSort A' v τ_β
    → Judge x (Expr.Eval.x.type A' B' C)
    → A →ᵦ A'
    → B →ᵦ B'
    → Judge (DCC (Eval A B x)) (Expr.Eval.type A' B' C)
  /-| eval   : Judge x (open Dsl in (DCC ((Π f_α f_B) env)))
    → Reduces α α'
    → Reduces B B'
    → Reduces (DCC (f_α env)) α'
    → Reduces (DCC (f_B env)) (open Dsl in (DCC ((Π B' γ))))
    → Judge α (DCC Sort m)
    → Judge B (open Dsl in (DCC ((Π f_α₂ f_B₂) env₂)))
    → Reduces (DCC (f_α₂ env₂)) α'
    → Reduces (DCC (f_B₂ env₂)) (open Dsl in (DCC (`α' Sort n)))
    → Reduces (Expr.Eval.type α B γ m n) τ
    → Judge (DCC (Eval α B x)) τ-/
  | quot   : Judge x α
    → Judge B (DCC Sort n)
    → B →ᵦ B'
    → Judge (open Dsl in (DCC (`B x))) (quot.type α B')
  | pair     : Judge M (Pair.f.type A B)
    → Judge C τ_C
    → C →ᵦ C'
    → Judge N (Pair.g.type A B C')
    → Sigma'.C.type A B _v τ_C
    → Judge (DCC (⟨,⟩C M N)) (Pair.type A B C')
  | swap   : Judge A (DCC Sort u)
    → Judge B (DCC Sort v)
    → A →ᵦ A'
    → B →ᵦ B'
    → Judge (DCC (Swap A B)) (Expr.Swap.type A' B')
  /-
    ef_α : α → Sort m
    f_β : ∀ (x : α) (y : f_α x), Sort n
    Π(f_α, f_β)
  -/
  | pi     : Judge B τ_B
    → ArrowSort A v τ_B
    → Judge C τ_C
    → B →ᵦ B'
    → Pi.C.type' A B' s τ_C
    → Judge (open Dsl in (DCC (Π B C))) (Pi.type A v s)
  | sort    : Judge (DCC Sort m) (DCC Sort m.succ)
  | top     : Judge (DCC 𝟙) Top.type
  | bot     : Judge (DCC 𝟘) Bot.type
  | tintro  : Judge (DCC ∗) Tintro.type
  | bang    : Judge τ (DCC Sort m) → Judge (open Dsl in (DCC (! τ))) (DCC Sort m)
  | box     : Judge x τ
    → Judge (open Dsl in (DCC (& x))) (open Dsl in (DCC (! τ)))
  | false   : Judge (DCC 𝟘₂) (DCC 𝟚)
  | true    : Judge (DCC 𝟙₂) (DCC 𝟚)
  | bool    : Judge (DCC 𝟚) (DCC Sort 1)
  | app     : Judge f (open Dsl in (DCC ((Π f_α f_β) x_α)))
    → (f_α x_α) ≡ α
    → Judge x α
    → (f_β x_α x) →ᵦ τ
    → Judge (DCC (f x)) τ
  | ind_bot  : Judge motive τ_motive
    → Arrow A τ_motive₂ τ_motive
    → Arrow (DCC 𝟘) (DCC Sort v) τ_motive₂
    → motive →ᵦ motive'
    → Judge (DCC (𝟘.Rec motive)) (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟘) motive'))) ∗))
  | ind_bool : Judge motive τ_motive
    → Sigma'.C.type A (DCC (`A 𝟚)) _v τ_motive
    → Judge x (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) motive'))) ∗))
    → Judge y (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) motive'))) ∗))
    → motive →ᵦ motive'
    → Judge (DCC (𝟚.Rec motive x y)) (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) motive'))) ∗))
deriving Repr

-- Replaces everything from `def infer₂` to end-of-file.
-- Everything above (TypeError, Reduces, def_eq?, Judge, …) is unchanged.

def Pi.C.type.is_norm (h : Pi.C.type B A v τ) : IsNorm Red B ×' IsNorm Red A := by
  cases h with
  | semi h₁ h₂ | canon h₁ h₂ => exact ⟨fun ⟨_, h⟩ => h₂.is_norm ⟨_, Red.point 0 (by grind) h⟩, RedNorm.is_norm (by assumption)⟩
  | canon' h₁ h₂ => exact ⟨fun ⟨_, h⟩ => h₂.is_norm ⟨_, Red.point 0 (by grind) (Red.point 0 (by point_arity) h)⟩, RedNorm.is_norm (by assumption)⟩
  | arrow h₁ h₂ h₃ => exact ⟨fun ⟨_, h⟩ => match h with | .point 0 hn h => h₁.is_norm ⟨_, h⟩ | .point 1 hn h => h₂.is_norm ⟨_, h⟩, h₁.is_norm⟩

def infer (e : Expr) : Except (TypeError e) (Σ' (t : Expr), Judge e t) :=
  open Dsl in match e with
  | DCC (𝟚.Rec motive x y) =>
    match infer motive with
    | .ok ⟨τ_motive, h₁⟩ =>
      match τ_motive.read_sigma'_C_type with
      | .ok ⟨A, (DCC (`A₂ 𝟚)), _s, h₂⟩ =>
        if heq₁ : A₂ = A then
          match x.infer with
          | .ok ⟨τ_x, h₃⟩ =>
            match y.infer with
            | .ok ⟨τ_y, h₄⟩ =>
              if heq₂ : τ_x = (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) #(reduce_all motive)))) ∗)) then
                if heq₃ : τ_y = (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) #(reduce_all motive)))) ∗)) then
                  .ok ⟨_, .ind_bool h₁ (heq₁ ▸ h₂) (heq₂ ▸ h₃) (heq₃ ▸ h₄) (reduce_reduces rfl)⟩
                else .error (.sub y (.unexpected y τ_y))
              else .error (.sub x (.unexpected x τ_x))
              /-match def_eq? τ_x (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) #(reduce_all motive)))) ∗)) with
              | .ok h_defeq₁ =>
                match def_eq? τ_y (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) motive))) ∗)) with
                | .ok h_defeq₂ =>
                  .ok ⟨_, .ind_bool h₁ h_arr₁ h_arr₂ h₂ h_defeq₁ h₃ h_defeq₂ (reduce_reduces rfl)⟩
                | .error e => .error (.sub y (.def_eq e))
              | .error e => .error (.sub x (.def_eq e))-/
            | .error e => .error (.sub y e)
          | .error e => .error (.sub x e)
        else .error (.sub motive (.mismatch A₂ A τ_motive))
      | .ok ⟨_A, B, _s, _h₂⟩ =>
        .error (.sub motive (.unexpected B τ_motive))
      | .error e => .error (.sub motive (.sub τ_motive e))
    | .error e => .error (.sub motive e)
    /-match infer motive with
    | .ok ⟨τ_motive, h₁⟩ =>
      match read_arrow τ_motive with
      | .ok ⟨A, τ_motive₂, h_arr₁⟩ =>
        match read_arrow₁ τ_motive₂ (DCC 𝟚) with
        | .ok ⟨DCC Sort _v, h_arr₂⟩ =>
          match x.infer with
          | .ok ⟨τ_x, h₂⟩ =>
            match y.infer with
            | .ok ⟨τ_y, h₃⟩ =>
              if heq₁ : τ_x = (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) #(reduce_all motive)))) ∗)) then
                if heq₂ : τ_y = (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) #(reduce_all motive)))) ∗)) then
                  .ok ⟨_, .ind_bool h₁ h_arr₁ h_arr₂ (heq₁ ▸ h₂) (heq₂ ▸ h₃) (reduce_reduces rfl)⟩
                else .error (.sub y (.unexpected y τ_y))
              else .error (.sub x (.unexpected x τ_x))
              /-match def_eq? τ_x (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) #(reduce_all motive)))) ∗)) with
              | .ok h_defeq₁ =>
                match def_eq? τ_y (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) motive))) ∗)) with
                | .ok h_defeq₂ =>
                  .ok ⟨_, .ind_bool h₁ h_arr₁ h_arr₂ h₂ h_defeq₁ h₃ h_defeq₂ (reduce_reduces rfl)⟩
                | .error e => .error (.sub y (.def_eq e))
              | .error e => .error (.sub x (.def_eq e))-/
            | .error e => .error (.sub y e)
          | .error e => .error (.sub x e)
        | .ok ⟨τ_elim, _⟩ => .error (.sub τ_motive (.unexpected τ_elim τ_motive₂))
        | .error e => .error (.sub motive (.sub τ_motive (.sub τ_motive₂ e)))
      | .error e => .error (.sub motive (.sub τ_motive e))
    | .error e => .error (.sub motive e)-/
  | DCC (𝟘.Rec motive) =>
    match infer motive with
    | .ok ⟨τ_motive, h₁⟩ =>
      match read_arrow τ_motive with
      | .ok ⟨_A, τ_motive₂, h_arr₁⟩ =>
        match read_arrow₁ τ_motive₂ (DCC 𝟘) with
        | .ok ⟨DCC Sort _v, h_arr₂⟩ =>
          .ok ⟨_, .ind_bot h₁ h_arr₁ h_arr₂ (reduce_reduces rfl)⟩
        | .ok ⟨τ_elim, _⟩ => .error (.sub τ_motive (.unexpected τ_elim τ_motive₂))
        | .error e => .error (.sub motive (.sub τ_motive (.sub τ_motive₂ e)))
      | .error e => .error (.sub motive (.sub τ_motive e))
    | .error e => .error (.sub motive e)
  | DCC 𝟙₂ => .ok ⟨_, .true⟩
  | DCC 𝟘₂ => .ok ⟨_, .false⟩
  | DCC 𝟚 => .ok ⟨_, .bool⟩
  | .hole _u => .error (.unexpected e e)
  | DCC (Swap A B) =>
    match infer A with
    | .ok ⟨DCC Sort _u, h₁⟩ =>
      match infer B with
      | .ok ⟨DCC Sort _v, h₂⟩ =>
        .ok ⟨_, .swap h₁ h₂ (reduce_reduces rfl) (reduce_reduces rfl)⟩
      | .error e => .error (.sub B e)
      | .ok ⟨τ', _⟩ => .error (.sub B (.unexpected τ' B))
    | .error e => .error (.sub A e)
    | .ok ⟨τ', _⟩ => .error (.sub A (.unexpected τ' A))
  | DCC (!<> f) =>
    match infer f with
    | .ok ⟨τ_f, ht₁⟩ =>
      match τ_f.read_arrow with
      | .ok ⟨_A, DCC Sort _n, harr⟩ =>
        .ok ⟨_, .map ht₁ harr⟩
      | _ => .error (.mark 3 (.unexpected τ_f f))
    | .error e => .error (.sub f e)
  /-| DCC !<f> =>
    match infer f with
    | .ok ⟨(DCC (Π(Id(Sort m), f_β) α)), ⟨ht₁⟩⟩ =>
      match (DCC (f_β α)).reduce_all with
      | (DCC `(α₂, Sort n)) =>
        if heq : (DCC (f_β α)).reduce_all = (DCC `(α, Sort n)) then
          .ok ⟨_, ⟨.map ht₁ (reduce_reduces heq) (reduce_reduces rfl)⟩⟩
        else .error (.mismatch (DCC `(α, Sort n)) (DCC (f_β α)).reduce_all f)
      | x => .error (.mark 2 (.unexpected x f))
    | .ok ⟨t, _⟩ => .error (.mark 1 (.unexpected t f))
    | .error ε => .error (.sub f ε)-/
  /-| DCC !<f> =>
    match infer f with
    | .ok ⟨(DCC (Π(Id(Sort m), f_β) α)), ⟨ht₁⟩⟩ =>
      .ok ⟨_, ⟨.map ht₁ (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
    | .ok ⟨t, _⟩ => .error (.mark 1 (.unexpected t f))
    | .error ε => .error (.sub f ε)-/
  | DCC ($<> f) =>
    match f.infer with
    | .ok ⟨(DCC ((Π _f_A _f_B) _x_A)), ht⟩ =>
      .ok ⟨_, .fmap ht (reduce_reduces rfl) (reduce_reduces rfl)⟩
    | .ok ⟨t, _⟩ => .error (.unexpected t f)
    | .error ε => .error (.sub f ε)
  | DCC (* A) =>
    match A.infer with
    | .ok ⟨DCC Sort _m, ht⟩ =>
      .ok ⟨_, .unbox ht (reduce_reduces rfl)⟩
    | .error ε => .error (.sub A ε)
    | .ok ⟨τ, _⟩ => .error (.unexpected τ A)
  | DCC (! τ) =>
    match τ.infer with
    | .ok ⟨DCC Sort _m, ht⟩ => .ok ⟨_, .bang ht⟩
    | .ok ⟨t, _⟩ => .error (.unexpected t τ)
    | .error ε => .error (.sub τ ε)
  | DCC (& x) =>
    match x.infer with
    | .ok ⟨_τ, ht⟩ => .ok ⟨_, .box ht⟩
    | .error ε => .error (.sub x ε)
  | DCC 𝟙 => .ok ⟨_, .top⟩
  | DCC 𝟘 => .ok ⟨_, .bot⟩
  | DCC ∗ => .ok ⟨_, .tintro⟩
  | DCC Sort _m => .ok ⟨_, .sort⟩
  | DCC (Id α) =>
    match infer α with
    | .ok ⟨DCC Sort _m, ht⟩ =>
      .ok ⟨_, .id ht (reduce_reduces rfl)⟩
    | .ok ⟨t, _⟩ => .error (.unexpected t α)
    | .error ε => .error (.sub α ε)
  | DCC (∘ f g) =>
    match infer g with
    | .ok ⟨τ_g, ht₁⟩ =>
      match τ_g.read_arrow with
      | .ok ⟨_A, B, harr_g⟩ =>
        match infer f with
        | .ok ⟨DCC ((Π (`𝟙 B₂) (`𝟙 _C)) ∗), ht₂⟩ =>
          if heq₂ : B₂ = B then
            .ok ⟨_, .comp ht₁ harr_g (heq₂ ▸ ht₂) (reduce_reduces rfl)⟩
          else .error (.unexpected τ_g f)
        | .ok ⟨τ, _⟩ => .error (.unexpected τ g)
        | .error ε => .error (.sub f ε)
      | .error e => .error (.sub τ_g e)
      /-if heq : (DCC (Π(Id(Sort m), `(_m, *<Σ(__a, Λ(_a, _b, `(___a, β)))>)) !(α))) = comp.g.type α β m then
        match infer f with
        | .ok ⟨(DCC (Π(Id(Sort n), f_γ) Coup(f_β))), ⟨ht₂⟩⟩ =>
          if _heq₂ : (DCC (Π(Id(Sort n), f_γ) Coup(f_β))) = comp.f.type f_β f_γ n then
            if heq₃ : f_β.reduce_all = (DCC `(α, β)) then
              .ok ⟨_, ⟨.comp (heq ▸ ht₁) ht₂ (reduce_reduces heq₃) (reduce_reduces rfl) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
            else .error (.mismatch (DCC `(α, β)) f_β.reduce_all f)
          else .error (.mismatch (comp.f.type f_β f_γ n) (DCC (Π(Id(Sort n), f_γ) Coup(f_β))) f)
        | .ok ⟨t, _⟩ => .error (.unexpected t f)
        | .error ε => .error (.sub f ε)
      else .error (.mismatch (comp.g.type α β m) (DCC (Π(Id(Sort m), `(_m, *<Σ(__a, Λ(_a, _b, `(___a, β)))>)) !(α))) g)-/
    | .error ε => .error (.sub g ε)
  | DCC (= A x y) =>
    match infer A with
    | .ok ⟨DCC Sort _u, ht₀⟩ =>
      match infer x with
      | .ok ⟨t_x, ht₁⟩ =>
        match infer y with
        | .ok ⟨t_y, ht₂⟩ =>
          match t_x.def_eq? t_y with
          | .ok h =>
            match def_eq? t_y A with
            | .ok h₃ =>
              .ok ⟨_, .eq ht₀ ht₁ ht₂ h h₃⟩
            | .error e => .error (.def_eq e)
          | .error e => .error (.def_eq e)
        | .error ε => .error (.sub y ε)
      | .error ε => .error (.sub x ε)
    | .ok ⟨τ_A, _⟩ => .error (.sub A (.unexpected A τ_A))
    | .error ε => .error (.sub A ε)
  | DCC (Eql f_α) =>
    match infer f_α with
    | .ok ⟨τ, ht₁⟩ =>
      match τ.read_arrow with
      | .ok ⟨_δ, DCC (Sort _m), h⟩ =>
        .ok ⟨_, .eql ht₁ h (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC (=' f_α) =>
    match infer f_α with
    | .ok ⟨τ, ht₁⟩ =>
      match τ.read_arrow with
      | .ok ⟨_δ, DCC (Sort _m), h⟩ =>
        .ok ⟨_, .eq_mk ht₁ h (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC (refl f_α) =>
    match infer f_α with
    | .ok ⟨τ, ht₁⟩ =>
      match τ.read_arrow_sort with
      | .ok ⟨_δ, _m, h⟩ =>
        .ok ⟨_, .refl ht₁ h (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC (Σ A B) =>
    match A.infer with
    | .ok ⟨DCC Sort _u, h₁⟩ =>
      match B.infer with
      | .ok ⟨DCC ((Π fB fC) xA), h₂⟩ =>
        match def_eq? A (DCC (fB xA)) with
        | .ok h₃ =>
          match heq : reduce_all (DCC (fC xA (#(.hole (DCC ((Π fB fC) xA)).max_hole.succ)))) with
          | DCC Sort _s =>
            .ok ⟨_, .sigma h₁ h₂ h₃ (reduce_reduces heq)⟩
          | τ_u => .error (.sub B (.unexpected B τ_u))
        | .error e => .error (.sub B (.def_eq e))
        /-match τ_B.read_arrow with
        | .ok ⟨A', DCC Sort v, h_arr⟩ =>
          if heq : A' = reduce_all A then
            .ok ⟨_, .sigma h₁ h₂ h_arr (reduce_reduces (by grind))⟩
          else .error (.unexpected A' τ_B)
        | .ok ⟨_, u_τ_B, _⟩ => .error (.unexpected u_τ_B τ_B)
        | .error e => .error (.sub B (.sub τ_B e))-/
      | .ok ⟨τ_B, _⟩ => .error (.sub B (.unexpected B τ_B))
      | .error e => .error (.sub B e)
    | .ok ⟨τ_A, _⟩ => .error (.unexpected τ_A A)
    | .error e => .error (.sub A e)
  | DCC (Σ' B C) =>
    match B.infer with
    | .ok ⟨τ_B, h₁⟩ =>
      match read_arrow τ_B with
      | .ok ⟨A, DCC (Sort _v), harr₁⟩ =>
        match C.infer with
        | .ok ⟨τ_C, h₂⟩ =>
          match τ_C.view_sigma'_C_type A (reduce_all B) with
          | .ok ⟨_, h⟩ =>
            .ok ⟨_, .sigma' h₁ harr₁ (reduce_reduces rfl) h₂ h⟩
          | .error e => .error (.sub C (.sub τ_C e))
        | .error e => .error (.sub C e)
      | .ok ⟨_, τ, _⟩ => .error (.sub B (.unexpected τ τ_B))
      | .error e => .error (.sub B (.sub τ_B e))
    | .error e => .error (.sub B e)
  | DCC (,B x y) =>
    match infer x with
    | .ok ⟨α, ht₁⟩ =>
      match infer y with
      | .ok ⟨Bxm, ht₂⟩ =>
        match B.infer with
        | .ok ⟨τ_B, h₃⟩ =>
          match τ_B.view_arrow_sort₁ α with
          | .ok ⟨_n, harr⟩ =>
            if heq₂ : reduce_all (DCC (#(reduce_all B) x)) = Bxm then
              .ok ⟨_, .mk ht₁ h₃ harr
                (reduce_reduces rfl) (reduce_reduces (B := Bxm) (heq₂ ▸ rfl)) ht₂⟩
            else .error (.mismatch (reduce_all (DCC (B x))) Bxm y)
          | _ => .error (.unexpected τ_B B)
        | .error ε => .error (.sub B ε)
      | .error ε => .error (.sub y ε)
    | .error ε => .error (.sub x ε)
  | DCC (Fst B) =>
    match (infer B) with
    | .ok ⟨τ_β, ht₁⟩ =>
      match τ_β.read_arrow_sort with
      | .ok ⟨_α, _n, harr⟩ =>
        .ok ⟨_, .fstc ht₁ harr (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ_β B)
    | .error ε => .error (.sub B ε)
  | DCC (Snd B) =>
    match (infer B) with
    | .ok ⟨τ_β, ht₁⟩ =>
      match τ_β.read_arrow_sort with
      | .ok ⟨_α, _n, harr⟩ =>
        .ok ⟨_, .sndc ht₁ harr (reduce_reduces rfl)⟩
      | .error e => .error (.sub B (.sub τ_β e))
    | .error ε => .error (.sub B ε)
  | DCC (Λ A B x) =>
    match A.infer with
    | .ok ⟨DCC Sort _m, ht⟩ =>
      match B.infer with
      | .ok ⟨τ_β, ht_β⟩ =>
        match τ_β.view_arrow_sort₁ (reduce_all A) with
        | .ok ⟨_n, h⟩ =>
          match infer x with
          | .ok ⟨τ_x, ht₂⟩ =>
            match τ_x.view_curr_x_type₂ (reduce_all A) (reduce_all B) with
            | .ok ⟨_C, h_x⟩ =>
              .ok ⟨_, .curr ht ht_β (reduce_reduces rfl) h ht₂ h_x (reduce_reduces rfl)⟩
            | .error e => .error (.sub x (.sub τ_x e))
          | .error e => .error (.sub x e)
        | _ => .error (.unexpected τ_β B)
      | .error ε => .error (.sub B ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t A)
    | .error ε => .error (.sub A ε)
  | DCC (!Λ A B x) =>
    match A.infer with
    | .ok ⟨DCC Sort _m, ht⟩ =>
      match B.infer with
      | .ok ⟨τ_β, ht_β⟩ =>
        match τ_β.view_arrow_sort₁ (reduce_all A) with
        | .ok ⟨_n, h⟩ =>
          match infer x with
          | .ok ⟨τ_x, ht₂⟩ =>
            match τ_x.view_curr'_x_type₂ (reduce_all A) (reduce_all B) with
            | .ok ⟨_C, h_x⟩ =>
              .ok ⟨_, .curr' ht ht_β (reduce_reduces rfl) h ht₂ h_x (reduce_reduces rfl)⟩
            | .error e => .error (.sub x (.sub τ_x e))
          | .error e => .error (.sub x e)
        | _ => .error (.unexpected τ_β B)
      | .error ε => .error (.sub B ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t A)
    | .error ε => .error (.sub A ε)
  | DCC (Eval A B x) =>
    match A.infer with
    | .ok ⟨DCC Sort _u, ht⟩ =>
      match B.infer with
      | .ok ⟨τ_β, ht_β⟩ =>
        match τ_β.view_arrow_sort₁ (reduce_all A) with
        | .ok ⟨_v, h⟩ =>
            match infer x with
            | .ok ⟨DCC ((Π _A (`_B (Π _C C))) _D), ht₂⟩ =>
              if heq : (DCC ((Π _A (`_B (Π _C C))) _D)) = (Expr.Eval.x.type (reduce_all A) (reduce_all B) C) then
                .ok ⟨_, .eval ht ht_β h (heq ▸ ht₂) (reduce_reduces rfl) (reduce_reduces rfl)⟩
              else .error (.sub x (.unexpected (DCC ((Π _A (`_B C)) _D)) e))
            | .error e => .error (.sub x e)
            | .ok ⟨τ, _⟩ => .error (.sub x (.unexpected τ e))
        | _ => .error (.unexpected τ_β B)
      | .error e => .error (.sub B e)
    | .ok ⟨t, _⟩ => .error (.unexpected t A)
    | .error ε => .error (.sub A ε)
  | DCC (`B x) =>
    match infer x with
    | .ok ⟨_A, ht₁⟩ =>
      match infer B with
      | .ok ⟨DCC Sort _v, ht₂⟩ =>
        .ok ⟨_, .quot ht₁ ht₂ (reduce_reduces rfl)⟩
      | .ok ⟨t, _⟩ => .error (.unexpected t B)
      | .error ε => .error (.sub B ε)
    | .error ε => .error (.sub x ε)
  | DCC (⟨,⟩C M N) =>
    match infer M with
    | .ok ⟨DCC ((Π (`𝟙 A) (`𝟙 B)) ∗), ht_M⟩ =>
      if heq : DCC ((Π (`𝟙 A) (`𝟙 B)) ∗) = (Pair.f.type A B) then
        match infer C with
        | .ok ⟨τ_C, ht_C⟩ =>
          match infer N with
          | .ok ⟨τ_N, ht_N⟩ =>
            if heq₂ : τ_N = (Pair.g.type A B (reduce_all C)) then
              match τ_C.view_sigma'_C_type A B with
              | .ok ⟨_, h_τ_C⟩ =>
                .ok ⟨_, .pair (heq ▸ ht_M) ht_C (reduce_reduces rfl) (heq₂ ▸ ht_N) h_τ_C⟩
              | .error e => .error (.sub τ_C e)
            else .error (.sub N (.unexpected τ_N N))
          | .error e => .error (.sub N e)
        | .error e => .error (.sub C e)
      else
        .error (.sub M (.unexpected M (DCC ((Π (`𝟙 A) (`𝟙 B)) ∗))))
    | .error e => .error (.sub M e)
    | .ok ⟨τ_M, _⟩ => .error (.sub M (.unexpected M τ_M))
  | DCC (Π B C) =>
    match B.infer with
    | .ok ⟨τ_B, ht₁⟩ =>
      match τ_B.read_arrow_sort with
      | .ok ⟨A, _v, harr⟩ =>
        match infer C with
        | .ok ⟨τ_C, ht₂⟩ =>
          match τ_C.view_pi_C_type A (reduce_all B) with
          | .ok ⟨_s, h₂⟩ =>
            .ok ⟨_, .pi ht₁ harr ht₂ (reduce_reduces rfl) h₂⟩
          | .error e => .error (.mark 4 (.sub τ_C e))
        | .error ε => .error (.mark 3 (.sub C ε))
      | _ => .error (.mark 2 (.unexpected τ_B B))
    | .error ε => .error (.mark 1 (.sub B ε))
  | DCC (f x) =>
    match infer f with
    | .ok ⟨DCC ((Π f_α _f_β) x_α), ht₁⟩ =>
      match infer x with
      | .ok ⟨τ₂', ht₂⟩ =>
        match def_eq? (DCC (f_α x_α)) τ₂' with
        | .ok h =>
           .ok ⟨_, .app ht₁ h ht₂ (reduce_reduces rfl)⟩
        | .error e => .error (.sub (DCC (f_α x_α)) (.def_eq e))
      | .error ε => .error (.sub x ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t f)
    | .error ε => .error (.sub f ε)
  | e => .error (.unexpected e e)

abbrev infer' (e : Expr) : Except (TypeError e) Expr := (·.fst) <$> e.infer

instance : Repr (Σ' (τ : Expr), Judge A τ) := ⟨fun ⟨B, x⟩ =>
  Repr.addAppParen s!"PSigma.mk {repr B} ({repr x})"⟩

end Expr

/-
Unifying two different kinds of arrows:

((Π (Id (Sort 0)) (`Sort 0 (`𝟙 (Sort 1)))) 𝟙)
((Π (Id (Sort 0)) (Λ (Sort 0) (Id (Sort 0)) (`(Σ (Id (Sort 0))) (Sort 1)))) 𝟙)
-/

#eval (DCC ((Id Sort 1) (Sort 0))).infer
open Dsl in #eval (DCC ((Id (→ (Sort 1) Sort 1)) (Id Sort 1))).infer
