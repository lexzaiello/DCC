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

def Arrow.is_norm (h : Arrow A B τ) (hn : IsNorm Red τ) : (IsNorm Red A) ×' (IsNorm Red B) :=
  match h with
  | .simple h₁ h₂ => ⟨h₁.is_norm, h₂.is_norm⟩

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
def read_arrow₁ (τ A : Expr) : Except (TypeError τ) ((B : Expr) × (Arrow A B τ)) :=
  match read_arrow τ with
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

open Dsl in
@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.read₁_complete {A B τ : Expr} (h : Arrow A B τ) : τ.read_arrow₁ A = .ok ⟨B, h⟩ := by
  cases h
  · expose_names
    simp [read_arrow₁, read_arrow, reduce_all, RedNorm.complete_fst a, RedNorm.complete_fst a_1, reduce_reduces]
    congr!
    · simp [RedNorm.complete_fst a]
    · simp [RedNorm.complete_fst a_1]

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

@[dcc_force_reduce, aesop safe forward (rule_sets := [DccReduce])]
theorem reduce_all_complete (h : A →ᵦ B) : reduce_all A = B := by
  have h := RedNorm.complete_fst h
  grind

@[dcc_force_reduce, aesop safe apply (rule_sets := [DccReduce])]
theorem reduce_all_complete_eq (h : A →ᵦ B) : reduce_reduces heq = h := by
  simp [reduce_reduces]

open Dsl in
@[dcc_judge, inline]
abbrev comp.g.type := Arrow

open Dsl in
inductive Judge : Expr → Expr → Type where
  | eq     : Judge x τ₁
    → Judge y τ₂
    → τ₁ ≡ τ₂
    → τ₂ ≡ A
    → Judge (DCC (= A x y)) (DCC Sort 0)
  | refl    : Judge f_α τ_f_α
    → Arrow δ (DCC Sort m) τ_f_α
    → #(Expr.refl.type f_α δ) →ᵦ τ
    → Judge (DCC (refl f_α)) τ
  | eql    : Judge f_α τ_f_α
    → Arrow δ (DCC Sort m) τ_f_α
    → #(eql.type f_α δ) →ᵦ τ'
    → Judge (DCC (Eql f_α)) τ'
  | id     : Judge α (DCC Sort m)
    → α →ᵦ α'
    → Judge (DCC (Id α)) (id.type α')
  | comp   : Judge g τ_g
    → comp.g.type A B τ_g
    → Judge f (comp.f.type B C)
    → (g →ᵦ g')
    → Judge (DCC (∘ f g)) (comp.type A C g')
  | sigma  : Judge B τ_B
    → Arrow A (DCC (Sort v)) τ_B
    → Judge C τ_C
    → B →ᵦ B'
    → Pi.C.type B' A s τ_C
    → Judge (DCC (Σ B C)) (DCC (→ A (Sort (max v s))))
  | fstc   : Judge B τ_B
    → Arrow A (DCC Sort n) τ_B
    → B →ᵦ B'
    → Judge (DCC (Fst B)) (fstc.type A B')
  | sndc    : Judge B τ_B
    → Arrow A (DCC Sort n) τ_B
    → B →ᵦ B'
    → Judge (DCC (Snd B)) (sndc.type A B')
  | mk     : Judge x A
    → Judge B τ_B
    → Arrow A (DCC Sort n) τ_B
    → B →ᵦ B'
    → #(DCC (B' x)) →ᵦ τ₂
    → Judge y τ₂
    → (Σ' A B') →ᵦ τ
    → Judge (DCC (,B x y)) τ
  /-
    Λ(β, x)
    β receives (α, x)
    β : Coup(Sort m, Id(Sort m)) → Sort n
  -/
  | curr   : Judge A (DCC Sort u)
    → Judge B τ_β
    → A →ᵦ A'
    → Arrow A' (DCC Sort v) τ_β
    → Judge x (curr.x.type A' B' C)
    → B →ᵦ B'
    → Judge (DCC (Λ A B x)) (curr.type A' B' C)
  | curr'  : Judge A (DCC Sort u)
    → Judge B τ_B
    → A →ᵦ A'
    → Arrow A' (DCC Sort v) τ_B
    → Judge x (curr'.x.type A' B' C)
    → B →ᵦ B'
    →  #(curr'.type A B C) →ᵦ τ
    → Judge (DCC (!Λ A B x)) τ
  -- !<f> &(x) = !(x)
  /-| map    : Judge x (DCC (Π(Id(Sort m), f_β) α))
    → Reduces (DCC (f_β α)) (DCC `(α, Sort n))
    → Reduces (DCC ((!(α) : Sort m) → Sort n)) τ
    → Judge (DCC !<x>) τ-/
  | map    : Judge x τ_x
    → Arrow A (DCC Sort n) τ_x
    → (→ (! A) Sort n) →ᵦ τ
    → Judge (DCC (!<> x)) τ
  | fmap   : Judge x (open Dsl in (DCC ((Π f_A f_B) x_A)))
    → ((Π (`𝟙 (! (f_A x_A))) (`𝟙 (!<> (f_B x_A)))) ∗) →ᵦ τ
    → Judge (DCC ($<> x)) τ
  | unbox  : Judge A (DCC Sort m)
    → A →ᵦ A'
    → Judge (DCC (* A)) (open Dsl in (DCC (→ (! A') A')))
  | eval   : Judge A (DCC Sort u)
    → Judge B τ_β
    → Arrow A' (DCC Sort v) τ_β
    → Judge x (Expr.Eval.x.type A' B' C)
    → A →ᵦ A'
    → B →ᵦ B'
    → #(Expr.Eval.type A B C) →ᵦ τ
    → Judge (DCC (Eval A B x)) τ
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
    → #(quot.type α B) →ᵦ τ
    → Judge (open Dsl in (DCC (`B x))) τ
  | pair     : Judge M (Pair.f.type A B)
    → Judge C τ_C
    → Judge N τ_N
    → τ_N ≡ #(Pair.g.type A B C)
    → #(Pair.type A B C) →ᵦ τ'
    → Judge (DCC (⟨,⟩C M N)) τ'
  | swap   : Judge A (DCC Sort u)
    → Judge B (DCC Sort v)
    → #(Expr.Swap.type A B) →ᵦ τ'
    → Judge (DCC (Swap A B)) τ'
  /-
    ef_α : α → Sort m
    f_β : ∀ (x : α) (y : f_α x), Sort n
    Π(f_α, f_β)
  -/
  | pi     : Judge B τ_B
    → Arrow A (DCC Sort v) τ_B
    → Judge C τ_C
    → B →ᵦ B'
    → Pi.C.type B' A s τ_C
    → #(Pi.type A v s) →ᵦ τ
    → Judge (open Dsl in (DCC (Π B C))) τ
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
  | bimap   : Judge f τ_f
    → Judge g τ_g
    → Arrow A A' τ_f
    → Arrow B B' τ_g
    → (→ (Σ' A (`A B)) (Σ' B' (`A' B'))) →ᵦ τ'
    → Judge (DCC (Map A' B' f g)) τ'
  | assoc    : Judge A (DCC Sort u)
    → Judge B (DCC Sort v)
    → Judge C (DCC Sort s)
    → (→ (Σ' (Σ' A (`A B)) (`(Σ' A (`A B)) C)) (Σ' A (`A (Σ' B (`B C))))) →ᵦ τ'
    → Judge (DCC (Assoc A B C)) τ'
  | ind_bot  : Judge motive τ_motive
    → Arrow A τ_motive₂ τ_motive
    → Arrow (DCC 𝟘) (DCC Sort v) τ_motive₂
    → ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟘) motive))) ∗) →ᵦ τ'
    → Judge (DCC (𝟘.Rec motive)) τ'
  | ind_bool : Judge motive τ_motive
    → Arrow A τ_motive₂ τ_motive
    → Arrow (DCC 𝟚) (DCC Sort v) τ_motive₂
    → Judge x τ_x
    → τ_x ≡ ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) motive))) ∗)
    → Judge y τ_y
    → τ_y ≡ ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) motive))) ∗)
    → ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) motive))) ∗) →ᵦ τ'
    → Judge (DCC (𝟚.Rec motive x y)) τ'
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
      match read_arrow τ_motive with
      | .ok ⟨A, τ_motive₂, h_arr₁⟩ =>
        match read_arrow₁ τ_motive₂ (DCC 𝟚) with
        | .ok ⟨DCC Sort _v, h_arr₂⟩ =>
          match x.infer with
          | .ok ⟨τ_x, h₂⟩ =>
            match y.infer with
            | .ok ⟨τ_y, h₃⟩ =>
              match def_eq? τ_x (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) motive))) ∗)) with
              | .ok h_defeq₁ =>
                match def_eq? τ_y (DCC ((Π (`𝟙 A) (`𝟙 (Π (`A 𝟚) motive))) ∗)) with
                | .ok h_defeq₂ =>
                  .ok ⟨_, .ind_bool h₁ h_arr₁ h_arr₂ h₂ h_defeq₁ h₃ h_defeq₂ (reduce_reduces rfl)⟩
                | .error e => .error (.sub y (.def_eq e))
              | .error e => .error (.sub x (.def_eq e))
            | .error e => .error (.sub y e)
          | .error e => .error (.sub x e)
        | .ok ⟨τ_elim, _⟩ => .error (.sub τ_motive (.unexpected τ_elim τ_motive₂))
        | .error e => .error (.sub motive (.sub τ_motive (.sub τ_motive₂ e)))
      | .error e => .error (.sub motive (.sub τ_motive e))
    | .error e => .error (.sub motive e)
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
  | DCC (Assoc A B C) =>
    match A.infer with
    | .ok ⟨DCC Sort _u, h₁⟩ =>
      match B.infer with
      | .ok ⟨DCC Sort _v, h₂⟩ =>
        match C.infer with
        | .ok ⟨DCC Sort _s, h₃⟩ =>
          .ok ⟨_, .assoc h₁ h₂ h₃ (reduce_reduces rfl)⟩
        | .error e => .error (.sub C e)
        | .ok ⟨τ_C, _⟩ => .error (.unexpected τ_C C)
      | .error e => .error (.sub B e)
      | .ok ⟨τ_B, _⟩ => .error (.unexpected τ_B B)
    | .error e => .error (.sub A e)
    | .ok ⟨τ_A, _⟩ => .error (.unexpected τ_A A)
  | DCC (Map A' B' f g) =>
    match f.infer with
    | .ok ⟨τ_f, h₁⟩ =>
      match g.infer with
      | .ok ⟨τ_g, h₂⟩ =>
        match read_arrow τ_f with
        | .ok ⟨_A, A'', h_arr₁⟩ =>
          match read_arrow τ_g with
          | .ok ⟨_B, B'', h_arr₂⟩ =>
            if heq₁ : A'' = A' then
              if heq₂ : B'' = B' then
                .ok ⟨_, .bimap h₁ h₂ (heq₁ ▸ h_arr₁) (heq₂ ▸ h_arr₂) (reduce_reduces rfl)⟩
              else .error (.sub g (.mismatch A'' A' g))
            else .error (.sub f (.mismatch A'' A' f))
          | .error e => .error (.sub g (.sub τ_g e))
        | .error e => .error (.sub f (.sub τ_f e))
      | .error e => .error (.sub g e)
    | .error e => .error (.sub f e)
  | DCC 𝟙₂ => .ok ⟨_, .true⟩
  | DCC 𝟘₂ => .ok ⟨_, .false⟩
  | DCC 𝟚 => .ok ⟨_, .bool⟩
  | .hole _u => .error (.unexpected e e)
  | DCC (Swap A B) =>
    match infer A with
    | .ok ⟨DCC Sort _u, h₁⟩ =>
      match infer B with
      | .ok ⟨DCC Sort _v, h₂⟩ =>
        .ok ⟨_, .swap h₁ h₂ (reduce_reduces rfl)⟩
      | .error e => .error (.sub B e)
      | .ok ⟨τ', _⟩ => .error (.sub B (.unexpected τ' B))
    | .error e => .error (.sub A e)
    | .ok ⟨τ', _⟩ => .error (.sub A (.unexpected τ' A))
  | DCC (!<> f) =>
    match infer f with
    | .ok ⟨τ_f, ht₁⟩ =>
      match τ_f.read_arrow with
      | .ok ⟨_A, DCC Sort _n, harr⟩ =>
        .ok ⟨_, .map ht₁ harr (reduce_reduces rfl)⟩
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
      .ok ⟨_, .fmap ht (reduce_reduces rfl)⟩
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
    match infer x with
    | .ok ⟨t_x, ht₁⟩ =>
      match infer y with
      | .ok ⟨t_y, ht₂⟩ =>
        match t_x.def_eq? t_y with
        | .ok h =>
          match def_eq? t_y A with
          | .ok h₃ =>
            .ok ⟨_, .eq ht₁ ht₂ h h₃⟩
          | .error e => .error (.def_eq e)
        | .error e => .error (.def_eq e)
      | .error ε => .error (.sub y ε)
    | .error ε => .error (.sub x ε)
  | DCC (Eql f_α) =>
    match infer f_α with
    | .ok ⟨τ, ht₁⟩ =>
      match τ.read_arrow with
      | .ok ⟨_δ, DCC Sort _m, h⟩ =>
        .ok ⟨_, .eql ht₁ h (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC (refl f_α) =>
    match infer f_α with
    | .ok ⟨τ, ht₁⟩ =>
      match τ.read_arrow with
      | .ok ⟨_δ, DCC Sort _m, h⟩ =>
        .ok ⟨_, .refl ht₁ h (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC (Σ B C) =>
    match B.infer with
    | .ok ⟨τ_B, h₁⟩ =>
      match read_arrow τ_B with
      | .ok ⟨A, DCC Sort _v, harr₁⟩ =>
        match C.infer with
        | .ok ⟨τ_C, h₂⟩ =>
          match τ_C.view_pi_f_β (reduce_all B) A with
          | .ok ⟨_, h⟩ =>
            .ok ⟨_, .sigma h₁ harr₁ h₂ (reduce_reduces rfl) h⟩
          | .error e => .error (.sub C (.sub τ_C e))
        | .error e => .error (.sub C e)
      | .ok ⟨_A, τ₂, _h⟩ =>
        .error (.sub B (.unexpected τ₂ τ_B))
      | .error e => .error (.sub B (.sub τ_B e))
    | .error e => .error (.sub B e)
  | DCC (,B x y) =>
    match infer x with
    | .ok ⟨α, ht₁⟩ =>
      match infer y with
      | .ok ⟨Bxm, ht₂⟩ =>
        match B.infer with
        | .ok ⟨τ_B, h₃⟩ =>
          match τ_B.read_arrow₁ α with
          | .ok ⟨DCC Sort _n, harr⟩ =>
            if heq₂ : reduce_all (DCC (#(reduce_all B) x)) = Bxm then
              .ok ⟨_, .mk ht₁ h₃ harr
                (reduce_reduces rfl) (reduce_reduces (B := Bxm) (heq₂ ▸ rfl)) ht₂ (reduce_reduces rfl)⟩
            else .error (.mismatch (reduce_all (DCC (B x))) Bxm y)
          | _ => .error (.unexpected τ_B B)
        | .error ε => .error (.sub B ε)
      | .error ε => .error (.sub y ε)
    | .error ε => .error (.sub x ε)
  | DCC (Fst B) =>
    match (infer B) with
    | .ok ⟨τ_β, ht₁⟩ =>
      match τ_β.read_arrow with
      | .ok ⟨_α, DCC Sort _n, harr⟩ =>
        .ok ⟨_, .fstc ht₁ harr (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ_β B)
    | .error ε => .error (.sub B ε)
  | DCC (Snd B) =>
    match (infer B) with
    | .ok ⟨τ_β, ht₁⟩ =>
      match τ_β.read_arrow with
      | .ok ⟨_α, DCC Sort _n, harr⟩ =>
        .ok ⟨_, .sndc ht₁ harr (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ_β B)
    | .error ε => .error (.sub B ε)
  | DCC (Λ A B x) =>
    match A.infer with
    | .ok ⟨DCC Sort _m, ht⟩ =>
      match B.infer with
      | .ok ⟨τ_β, ht_β⟩ =>
        match τ_β.read_arrow₁ (reduce_all A) with
        | .ok ⟨DCC Sort _n, h⟩ =>
          match infer x with
          | .ok ⟨DCC ((Π _A (`_B C)) _D), ht₂⟩ =>
            if heq : (DCC ((Π _A (`_B C)) _D)) = (curr.x.type (reduce_all A) (reduce_all B) C) then
              .ok ⟨_, .curr ht ht_β (reduce_reduces rfl) h (heq ▸ ht₂) (reduce_reduces rfl)⟩
            else .error (.sub x (.unexpected (DCC ((Π _A (`_B C)) _D)) e))
          | .error e => .error (.sub x e)
          | .ok ⟨τ, _⟩ => .error (.sub x (.unexpected τ e))
        | _ => .error (.unexpected τ_β B)
      | .error ε => .error (.sub B ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t A)
    | .error ε => .error (.sub A ε)
  | DCC (!Λ A B x) =>
    match A.infer with
    | .ok ⟨DCC Sort _m, ht⟩ =>
      match B.infer with
      | .ok ⟨τ_β, ht_β⟩ =>
        match τ_β.read_arrow₁ (reduce_all A) with
        | .ok ⟨DCC Sort _n, h⟩ =>
          match infer x with
          | .ok ⟨DCC ((Π _A (`_B C)) _D), ht₂⟩ =>
            if heq : (DCC ((Π _A (`_B C)) _D)) = (curr'.x.type (reduce_all A) (reduce_all B) C) then
              .ok ⟨_, .curr' ht ht_β (reduce_reduces rfl) h (heq ▸ ht₂) (reduce_reduces rfl) (reduce_reduces rfl)⟩
            else .error (.sub x (.unexpected (DCC ((Π _A (`_B C)) _D)) e))
          | .error e => .error (.sub x e)
          | .ok ⟨τ, _⟩ => .error (.sub x (.unexpected τ e))
        | _ => .error (.unexpected τ_β B)
      | .error ε => .error (.sub B ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t A)
    | .error ε => .error (.sub A ε)
  | DCC (Eval A B x) =>
    match A.infer with
    | .ok ⟨DCC Sort _u, ht⟩ =>
      match B.infer with
      | .ok ⟨τ_β, ht_β⟩ =>
        match τ_β.read_arrow₁ (reduce_all A) with
        | .ok ⟨DCC Sort _v, h⟩ =>
            match infer x with
            | .ok ⟨DCC ((Π _A (`_B (Π _C C))) _D), ht₂⟩ =>
              if heq : (DCC ((Π _A (`_B (Π _C C))) _D)) = (Expr.Eval.x.type (reduce_all A) (reduce_all B) C) then
                .ok ⟨_, .eval ht ht_β h (heq ▸ ht₂) (reduce_reduces rfl) (reduce_reduces rfl) (reduce_reduces rfl)⟩
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
        | .ok ⟨_τ_C, ht_C⟩ =>
          match infer N with
          | .ok ⟨τ_N, ht_N⟩ =>
            match def_eq? τ_N (Pair.g.type A B C) with
            | .ok h =>
              .ok ⟨_, .pair (heq ▸ ht_M) ht_C ht_N h (reduce_reduces rfl)⟩
            | .error e => .error (.sub N (.def_eq e))
          | .error e => .error (.sub N e)
        | .error e => .error (.sub C e)
      else
        .error (.sub M (.unexpected M (DCC ((Π (`𝟙 A) (`𝟙 B)) ∗))))
    | .error e => .error (.sub M e)
    | .ok ⟨τ_M, _⟩ => .error (.sub M (.unexpected M τ_M))
  | DCC (Π B C) =>
    match B.infer with
    | .ok ⟨τ_B, ht₁⟩ =>
      match τ_B.read_arrow with
      | .ok ⟨A, DCC Sort _v, harr⟩ =>
        match infer C with
        | .ok ⟨τ_C, ht₂⟩ =>
          match τ_C.view_pi_f_β (reduce_all B) A with
          | .ok ⟨_s, h₂⟩ =>
            .ok ⟨_, .pi ht₁ harr ht₂ (reduce_reduces rfl) h₂ (reduce_reduces rfl)⟩
          | _ => .error (.mark 4 (.unexpected τ_C C))
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
