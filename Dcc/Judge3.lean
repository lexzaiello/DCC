import Dcc.Ast
import Dcc.Aff.Red
import Dcc.Types
import Dcc.Aff.Unify

inductive DefEqError.{u} {τ_c : Type u} where
  /-| pi_left  (expected actual : GenericExpr τ_c)  : DefEqError A B
  | pi_right (expected actual : GenericExpr τ_c)  : DefEqError A B
  | bang     (inner_errr      : DefEqError τ₁ τ₂) : DefEqError (DCC? !(τ₁)) (DCC? !(τ₂))
  | coup     (inner_errr      : DefEqError τ₁ τ₂) : DefEqError (DCC? Coup(τ₁)) (DCC? Coup(τ₂))-/
  | tm       (expected actual : GenericExpr τ_c)  : DefEqError
deriving DecidableEq, Repr

def DefEqError.toFormat (err : DefEqError (τ_c := τ_c)) : Std.Format :=
  match err with
  | .tm A B => A.toFormat ++ " ≠ " ++ (.nest 2 <| B.toFormat)
  /-"- " ++ (.nest 2 <| (Std.format A) ++ " ≠ " ++ (.indentD (Std.format B)) ++ .line ++
  (match err with
  /-| .pi_left expected actual => "because Π domains are not def-eq. Expected: " ++ (.indentD (Std.format expected)) ++ "but found: " ++ (.indentD (Std.format actual))
  | .pi_right expected actual => "because Π codomains are not def-eq. Expected: " ++ (.indentD (Std.format expected)) ++ "but found: " ++ (.indentD (Std.format actual))
  | .bang inner_err => "because bang types are not def-eq because: " ++ inner_err.toFormat
  | .coup inner_err => "because coup types are not def-eq because: " ++ inner_err.toFormat-/
  | .tm expected actual => "because terms are not def-eq. Expected: " ++ (.indentD (Std.format expected)) ++ .line ++ "but found: " ++ (.indentD (Std.format actual))))-/

instance : Std.ToFormat (DefEqError (τ_c := τ_c)) := ⟨DefEqError.toFormat⟩
instance : ToString (DefEqError (τ_c := τ_c)) := ⟨toString ∘ Std.format⟩

inductive TypeError.{u} {τ_c : Type u} : (e : GenericExpr τ_c) → Type u where
  | mismatch (expected actual at_e : GenericExpr τ_c) : TypeError e
  | unexpected (found at_e : GenericExpr τ_c) : TypeError e
  | sub (at_e : GenericExpr τ_c) (err : TypeError at_e) : TypeError e
  | def_eq (err : DefEqError (τ_c := τ_c)) : TypeError e
  | mark (n : ℕ) (ε : TypeError e) : TypeError e
deriving Repr

def TypeError.toFormat (err : TypeError (τ_c := τ_c) e) : Std.Format :=
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

instance {e : GenericExpr τ_c} : Std.ToFormat (TypeError e) := ⟨TypeError.toFormat⟩
instance {e : GenericExpr τ_c} : ToString (TypeError e) := ⟨toString ∘ Std.format⟩
instance {e : GenericExpr τ_c} : Repr (TypeError e) := ⟨fun e _n => TypeError.toFormat e⟩

namespace GenericExpr

inductive Reduces.{u} {τ_c : Type u} : GenericExpr τ_c → GenericExpr τ_c → Type u
  | mk : RedAffNorm A ⟨B, hn_B⟩ → Unify B B' → Reduces A B'
deriving Repr

def Reduces.aff (h : Reduces A B) : RedAffNorm A (red_aff A) :=
  match h with
  | ⟨hr₁, _⟩ =>
    hr₁.out_eq ▸ hr₁

def Reduces.unique.{u} {τ_c : Type u} [DecidableEq τ_c] {A B C : GenericExpr τ_c}
  (h₁ : Reduces A B) (h₂ : Reduces A C) : B = C :=
  match h₁, h₂ with
  | ⟨hr₁, hr₂⟩, ⟨hr₃, hr₄⟩ => by
    cases hr₁.unique hr₃
    have heq₁ := hr₂.complete
    have heq₂ := hr₄.complete
    grind

/-def Reduces₂.trans.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {A B C : GenericExpr τ_c} (h₁ : Reduces₂ A B) (h₂ : Reduces₂ B C) : Reduces₂ A C :=
  match h₁, h₂ with
  | ⟨hr₁, hn₁, hr₂⟩, ⟨hr₃, hn₃, hr₄⟩ => by
    have ha := hr₂.is_norm hn₁
    have hb := hr₃
    have heq := hb.elim_head_norm ha
    cases heq

    exact ⟨hr₁, hn₁, by sorry⟩-/

/-def Reduces.is_norm.{u} {τ_c : Type u} {A B : GenericExpr τ_c} : Reduces A B → IsNorm RedAff B :=
  fun ⟨_hr₁, hr₂⟩ => hr₂.is_norm-/

@[dcc_force_reduce]
def reduce_all.{u} {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr τ_c) : (GenericExpr τ_c) :=
  match (reduce RedAff e) with
  | ⟨B, _⟩ =>
    match reduce_unify B with
    | ⟨C, _⟩ => C

def reduce_reduces.{u} {τ_c : Type u} [DecidableEq τ_c] {A B : GenericExpr τ_c} (h : reduce_all A = B) : Reduces A B := by
  simp [reduce_all] at h
  exact ⟨⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩, h ▸ (reduce RedAff A).fst.reduce_unify.snd⟩

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def Reduces.complete.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {τ τ' : GenericExpr τ_c}
  (h : Reduces (τ_c := τ_c) τ τ') : reduce_all τ = τ' := by
  match h with
  | ⟨h₁, h₂⟩ =>
    have ha := h₁.complete_fst
    have hb := h₂.complete
    simp [reduce_all]
    grind

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def Reduces.out_eq [DecidableEq τ_c] (h : Reduces (τ_c := τ_c) A B) : B = reduce_all A :=
  match h with
  | ⟨h₁, h₂⟩ => by
    cases h₁.out_eq
    have heq₁ := h₁.complete
    have heq₂ := h₂.complete
    simp [reduce_all]
    grind

def Reduces.push_head [DecidableEq τ_c] (h : Reduces (τ_c := τ_c) A C) (hr : RedAff A B) : Reduces B C :=
  match h with
  | ⟨hrt, h₂⟩ => ⟨hrt.push_head hr, h₂⟩

def Reduces.elim_norm [DecidableEq τ_c] (h : Reduces (τ_c := τ_c) A B) (hn : IsNorm RedAff A) : Unify A B :=
  match h with
  | ⟨hrt, _⟩ => by
    cases hrt.elim_norm hn
    assumption

def Reduces.eq [DecidableEq τ_c] (h : Reduces (τ_c := τ_c) A B) : h = reduce_reduces (A := A) (B := B) (h.out_eq ▸ rfl) :=
  match h with
  | ⟨hr, hr₂⟩ => by
    rw [hr.out_eq] at *
    expose_names
    cases hr_1.unique hr
    cases hr_1.eq
    simp only [reduce_reduces]
    have heq₂ := hr₂.complete
    grind

def Reduces.eq' [DecidableEq τ_c] (h₁ : Reduces (τ_c := τ_c) A B) (h₂ : Reduces (τ_c := τ_c) A B) : h₁ = h₂ :=
  match h₁, h₂ with
  | ⟨hr₁, hr₂⟩, ⟨hr₃, hr₄⟩ => by
    cases hr₁.unique hr₃
    cases hr₁.out_eq
    cases hr₁.eq
    cases hr₃.eq
    have heq₂ := hr₂.complete
    have heq₃ := hr₄.complete
    grind

#eval Std.format <| pair.β.type (DCC (Sort 30)) 10 20

-- For checking arguments under apps
open Dsl in inductive DefEq.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] : GenericExpr τ_c → GenericExpr τ_c → Type u
  | tm : Reduces (DCC? (Unify (? τ₁) (? τ₂) τ₁ τ₂)) (DCC? (,B True proof_eq)) → DefEq τ₁ τ₂
deriving Repr

-- Reduces A B → DefEq A B

def def_eq?.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] (τ₁ τ₂ : GenericExpr τ_c) : Except (DefEqError (τ_c := τ_c)) (DefEq τ₁ τ₂) :=
  open Dsl in match heq : reduce_all (DCC? (Unify (? τ₁) (? τ₂) τ₁ τ₂)) with
  | (DCC? (,_B True _proof_eq)) =>
    .ok (.tm (reduce_reduces heq))
  | _ => .error (.tm τ₁ τ₂)

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def DefEq.complete.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {τ₁ τ₂ : GenericExpr τ_c} (h : DefEq (τ_c := τ_c) τ₁ τ₂) : def_eq? τ₁ τ₂ = .ok h := by
  induction h
  case tm hr₁ hr₂ =>
    expose_names
    have heq := hr₂.complete
    simp [def_eq?]
    split
    case h_1 heq' =>
      cases heq'.symm.trans heq
      congr!
      apply Reduces.eq'
    · grind

/-
Arrow needs to be able to detect the universe level as well.
We can fix (Id Sort u)
-/
open Dsl in
inductive Arrow.{u} {τ : Type u} [DecidableEq τ] : GenericExpr (τ := τ) → GenericExpr (τ := τ) → Level → GenericExpr (τ := τ) → Type u
  | simple : DefEq (DCC? ((Π (Id Sort u) B) α)) (DCC? ((Π (Id Sort u) (`Sort u (`α (B α #(.hole 0))))) α))
    → Reduces (DCC? (B α #(.hole 0))) B'
    → Arrow α B' u (DCC? ((Π (Id Sort u) B) α))
deriving Repr

open Dsl in
@[dcc_judge, inline]
def read_arrow.{u} {τ_c : Type u} [DecidableEq τ_c]
  (τ : GenericExpr (τ := τ_c)) : Except (TypeError τ) ((α β : GenericExpr (τ := τ_c)) × (m : Level) × (Arrow (τ := τ_c) α β m τ)) :=
  open Dsl in match τ with
  | (DCC? ((Π (Id Sort u) B) α)) =>
    match def_eq? (DCC? ((Π (Id Sort u) B) α)) (DCC? ((Π (Id Sort u) (`Sort u (`α (B α #(.hole 0))))) α)) with
    | .ok h => .ok ⟨_, _, _, .simple h (reduce_reduces rfl)⟩
    | .error e => .error (.def_eq e)
  | τ₀ => .error (.unexpected τ₀ τ₀)

open Dsl in
@[dcc_judge, inline]
def read_arrow₁.{u} {τ_c : Type u} [DecidableEq τ_c] (τ α : GenericExpr τ_c) : Except (TypeError τ) ((β : GenericExpr τ_c) × (m : Level) × (Arrow α β m τ)) :=
  match read_arrow τ with
  | .ok ⟨α', _β, _m, h⟩ =>
    if heq : α' = α then
      .ok ⟨_, _, heq ▸ h⟩
    else
      .error (.mismatch α α' τ)
  | .error e => .error e

open Dsl in
@[dcc_judge, inline]
def read_arrow₂.{u} {τ_c : Type u} [DecidableEq τ_c] (τ α : GenericExpr τ_c) (m : Level) : Except (TypeError τ) ((β : GenericExpr τ_c) × (Arrow α β m τ)) :=
  match read_arrow τ with
  | .ok ⟨α', _β, m', h⟩ =>
    if heq₁ : α' = α then
      if heq₂ : m' = m then
        .ok ⟨_, heq₁ ▸ heq₂ ▸ h⟩
      else .error (.unexpected (DCC? (Sort m')) τ)
    else
      .error (.mismatch α α' τ)
  | .error e => .error e

open Dsl in
@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.read₁_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {α β τ : GenericExpr τ_c} (h : Arrow α β m τ) : τ.read_arrow₁ α = .ok ⟨β, m, h⟩ := by
  cases h
  · expose_names
    simp [read_arrow₁, read_arrow, a_1.complete, a.complete, a.eq]
    congr! <;> exact a.out_eq.symm

open Dsl in
@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.read₂_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {α β τ : GenericExpr τ_c} {m : Level} (h : Arrow α β m τ) : τ.read_arrow₂ α m = .ok ⟨β, h⟩ := by
  cases h
  · expose_names
    simp [read_arrow₂, read_arrow, a_1.complete, a.complete, a.eq]
    congr!; exact a.out_eq.symm

open Dsl in
@[dcc_judge, inline]
def view_arrow.{u} {τ_c : Type u} [DecidableEq τ_c] (τ α β : GenericExpr (τ := τ_c)) (m : Level) : Except (TypeError τ) (Arrow α β m τ) :=
  match read_arrow τ with
  | .ok ⟨α', β', m', h⟩ =>
    if heq₁ : α' = α then
      if heq₂ : β' = β then
        if heq₃ : m' = m then
          .ok (heq₁ ▸ heq₂ ▸ heq₃ ▸ h)
        else
          .error (.unexpected (DCC? Sort m') τ)
      else
        .error (.mismatch α α' τ)
    else
      .error (.mismatch β β' τ)
  | .error e => .error e

-- (Π(Id(Sort 0), `(Sort 0, Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 1))))) ⊤)
open Dsl in inductive Pi.C.type.{u} {τ_c : Type u} :
  (GenericExpr τ_c) → (GenericExpr τ_c) → Level → Level → (GenericExpr τ_c) → Type u
  | canon  : Pi.C.type B δ o n
    (DCC? ((Π (Id Sort o) (`Sort o (Π B (Λ δ B (` (Σ B) Sort n))))) δ))
  | canon' : Pi.C.type (DCC? (!<> B)) (DCC? (!δ)) o n
    (DCC? ((Π(Id Sort o) (`Sort o (Π (!<> B) (!Λ δ B (` (! (Σ B)) Sort n))))) (! δ)))
  | arrow  : Pi.C.type B δ o n
    (DCC? ((Π (Id Sort o) (`Sort o (`δ ((Π B (`x₂ (`α Sort n))) α)))) δ))
  | semi   : Pi.C.type B δ o n (DCC? ((Π (Id Sort o) (`Sort o (Π B (`δ₂ (`δ₃ Sort n))))) δ))
deriving Repr

open Dsl in
def read_pi_f_β_cod.{u} {τ_c : Type u} (τ : GenericExpr τ_c) : Option (GenericExpr τ_c) :=
  match _heq₁ : τ with
  | (DCC? ((Π (Id Sort _o) (`_a (Π __a (Λ _b _c (`_d Sort n))))) _e)) =>
      .some (DCC? (Sort n))
  | (DCC? ((Π (Id Sort _o) (`_a (Π __a (!Λ _b _c (`_d Sort n))))) _e)) =>
      .some (DCC? (Sort n))
  | (DCC? ((Π _a (`_b (`_c ((Π (Id Sort _m) (`_d (`_e Sort n))) _α)))) _f)) =>
    .some (DCC? (Sort n))
  | _ => .none

open Dsl in
@[dcc_judge]
def view_pi_f_β.{u} {τ_c : Type u} [DecidableEq τ_c] (τ f_α δ : GenericExpr τ_c) (o : Level) : Option ((n : Level) × (Pi.C.type f_α δ o n τ)) :=
  open Dsl in match heq₁ : τ with
  | (DCC? ((Π __b (`_a (Π __a (Λ _b _c (`_d Sort n))))) _e)) =>
    if heq₂ : τ = (DCC? ((Π (Id Sort o) (`Sort o (Π f_α (Λ δ f_α (` (Σ f_α) Sort n))))) δ)) then
      .some ⟨n, by rw [← heq₁, heq₂]; exact .canon (B := f_α) (δ := δ) (o := o) (n := n)⟩
    else .none
  | (DCC? ((Π __b (` _a (Π __a (!Λ _b _c (`_d Sort n))))) _e)) =>
    match f_α, δ with
    | DCC? (!<> f_α), DCC? (! δ) =>
      if heq₂ : τ = (DCC? ((Π (Id Sort o) (`Sort o (Π (!<> f_α) (!Λ δ f_α (`(! (Σ f_α)) Sort n))))) (! δ))) then
        .some ⟨n, by rw [← heq₁, heq₂]; exact .canon' (B := f_α) (δ := δ) (o := o) (n := n)⟩
      else .none
    | _, _ => .none
  | (DCC? ((Π _a (`_b (`_c ((Π B (`_d (`_e Sort n))) α)))) _f)) =>
    if heq₂ : τ = (DCC? ((Π (Id Sort o) (`Sort o (`δ ((Π B (`_d (`α Sort n))) α)))) δ)) then
      if heq₃ : f_α = B then
        .some ⟨n, by rw [← heq₁, heq₂, heq₃]; exact .arrow (δ := δ) (o := o) (n := n)⟩
      else .none
    else .none
  | (DCC? ((Π __a (`_a (Π _B (`δ₂ (`δ₃ Sort n))))) _δ)) =>
    if heq : (DCC? ((Π __a (`_a (Π _B (`δ₂ (`δ₃ Sort n))))) _δ)) = (DCC? ((Π (Id Sort o) (`Sort o (Π f_α (`δ₂ (`δ₃ Sort n))))) δ)) then
      .some ⟨n, heq ▸ .semi (B := f_α) (δ := δ) (δ₂ := δ₂) (δ₃ := δ₃)⟩
    else .none
  | _ => .none

open Dsl in
@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Pi.C.type.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {f_α δ τ : GenericExpr τ_c}
  (h : Pi.C.type f_α δ o n τ) : view_pi_f_β τ f_α δ o = .some ⟨n, h⟩ := by
  cases h <;> simp [view_pi_f_β]

open Dsl in
@[dcc_judge] abbrev Pi.C.type'.{u} {τ_c : Type u} (f_α α : GenericExpr τ_c) (m o : Level) :=
  (DCC? ((Π (Id Sort m) (`Sort m (Π f_α (Λ α f_α (`(Σ f_α) Sort o))))) α))

open Dsl in
@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.view_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {α β τ : GenericExpr τ_c} (h : Arrow α β m τ) : view_arrow τ α β m = .ok h := by
  cases h with
  | simple h₁ h₂ =>
    simp [view_arrow, read_arrow, h₁.complete, h₂.out_eq, h₂.eq]
    grind

open Dsl in
@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.read_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {α β τ : GenericExpr τ_c}
  (h : Arrow α β m τ) : τ.read_arrow = .ok ⟨α, β, m, h⟩ := by
  cases h with
  | simple h₁ h₂ =>
    simp [read_arrow, h₁.complete, h₂.out_eq, h₂.eq]
    congr! <;> exact h₂.out_eq.symm

open Dsl in
@[dcc_judge, inline]
abbrev arrow.matcher.{u} {τ_c : Type u} [DecidableEq τ_c] (t : GenericExpr τ_c) : Option ((α β : GenericExpr τ_c) × (m : Level) × PULift.{1, 0} (t = (DCC? (α : Sort m) → β))) :=
  match heq₀ : t with
  | DCC? ((Π (Id Sort m) (Λ _a _b (` _c β))) α) =>
    if heq₁ : t = (DCC? (α : Sort m) → β) then
      .some ⟨α, β, m, ⟨by rw [← heq₀, heq₁]⟩⟩
    else
      .none
  | _ => .none

def is_arrow.{u} {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr τ_c) : Bool :=
  (arrow.matcher e).isSome

open Dsl in
@[dcc_judge, inline]
abbrev comp.g.type.{u} {τ : Type u} [DecidableEq τ] := Arrow (τ := τ)

open Dsl in
inductive Judge.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] : GenericExpr τ_c → GenericExpr τ_c → Type u where
  | eq     : Judge x α
    → Judge y α
    → Judge (DCC? (= x y)) (DCC? Sort 0)
  | refl    : Judge f_α τ_f_α
    → Arrow δ (DCC? Sort m) o τ_f_α
    → Reduces (GenericExpr.refl.type f_α δ o) τ
    → Judge (DCC? (refl f_α)) τ
  | eql    : Judge f_α τ_f_α
    → Arrow δ (DCC? Sort m) o τ_f_α
    → Reduces (eql.type f_α δ o) τ
    → Judge (DCC? (Eql f_α)) τ
  | id     : Judge α (DCC? Sort m)
    → Reduces (id.type α m) τ
    → Judge (DCC? (Id α)) τ
  | comp   : Judge g τ_g
    → comp.g.type A B m τ_g
    → Judge f (comp.f.type B C n)
    → Reduces (comp.type A C g m) τ
    → Judge (DCC? (∘ f g)) τ
  | coup   : Judge B τ_B
    → Arrow A (DCC? Sort n) m τ_B
    → Reduces (Coup.type m n) τ
    → Judge (open Dsl in (DCC? (Σ B))) τ
  | fstc   : Judge B τ_β
    → Arrow A (DCC? Sort n) m τ_B
    → Reduces (fstc.type A B m n) τ
    → Judge (DCC? (Fst B)) τ
  | sndc    : Judge B τ_B
    → Arrow A (DCC? Sort n) m τ_B
    → Reduces (sndc.type B m n) τ
    → Judge (DCC? (Snd B)) τ
  | sigma   : Judge B τ_B
    → Arrow δ (DCC? Sort m) o τ_B
    → Judge C τ_C
    -- f_α is not necessarily a normal form here. we need to reduce
    -- since it is not captured by Reduces Sigma.type
    → Reduces B B'
    → Pi.C.type B' δ o n τ_C
    → Reduces (Sigma.type δ m n o) τ
    → Judge (open Dsl in (DCC? (Σ B C))) τ
  | mk     : Judge x α
    → Judge B τ_B
    → Arrow A (DCC? Sort n) m τ_B
    → Reduces (DCC? (B x)) τ₂
    → Judge y τ₂
    → Reduces (open Dsl in (DCC? (Σ B))) τ
    → Judge (DCC? (,B x y)) τ
  /-
    Λ(β, x)
    β receives (α, x)
    β : Coup(Sort m, Id(Sort m)) → Sort n
  -/
  | curr   : Judge A (DCC? Sort u)
    → Judge B τ_β
    → Arrow A' (DCC? Sort v) u τ_β
    → Judge x (curr.x.type B' C u v)
    → Reduces B B'
    → Reduces (curr.type A B C u) τ
    → Judge (DCC? (Λ A B x)) τ
  | curr'  : Judge A (DCC? Sort u)
    → Judge B τ_B
    → Arrow A' (DCC? Sort v) u τ_B
    → Judge x (curr'.x.type B' C u v)
    → Reduces B B'
    → Reduces (curr'.type A B C u) τ
    → Judge (DCC? (!Λ A B x)) τ
  -- !<f> &(x) = !(x)
  /-| map    : Judge x (DCC? (Π(Id(Sort m), f_β) α))
    → Reduces (DCC? (f_β α)) (DCC? `(α, Sort n))
    → Reduces (DCC? ((!(α) : Sort m) → Sort n)) τ
    → Judge (DCC? !<x>) τ-/
  | map    : Judge x τ_x
    → Arrow A (DCC? Sort n) m τ_x
    → Reduces (open Dsl in (DCC? (((! A) : Sort m) → Sort n))) τ
    → Judge (DCC? (!<> x)) τ
  | fmap   : Judge x (open Dsl in (DCC? ((Π (Id Sort m) f_B) α)))
    → Reduces (open Dsl in (DCC? ((Π (Id Sort m) (`Sort m (!<> (f_B α)))) (! α)))) τ
    → Judge (DCC? ($<> x)) τ
  | unbox  : Judge A (DCC? Sort m) → Judge (DCC? (* A)) (open Dsl in (DCC? (((! A) : Sort m) → A)))
  | eval   : Judge A (DCC? Sort u)
    → Judge B τ_β
    → Arrow A' (DCC? Sort v) u τ_β
    → Judge x (GenericExpr.Eval.x.type A' B' c u)
    → Reduces A A'
    → Reduces B B'
    → Reduces (GenericExpr.Eval.type A B C u v) τ
    → Judge (DCC? (Eval A B x)) τ
  /-| eval   : Judge x (open Dsl in (DCC? ((Π f_α f_B) env)))
    → Reduces α α'
    → Reduces B B'
    → Reduces (DCC? (f_α env)) α'
    → Reduces (DCC? (f_B env)) (open Dsl in (DCC? ((Π B' γ))))
    → Judge α (DCC? Sort m)
    → Judge B (open Dsl in (DCC? ((Π f_α₂ f_B₂) env₂)))
    → Reduces (DCC? (f_α₂ env₂)) α'
    → Reduces (DCC? (f_B₂ env₂)) (open Dsl in (DCC? (`α' Sort n)))
    → Reduces (GenericExpr.Eval.type α B γ m n) τ
    → Judge (DCC? (Eval α B x)) τ-/
  | quot   : Judge x α
    → Judge B (DCC? Sort n)
    → Reduces (quot.type α B n) τ
    → Judge (open Dsl in (DCC? (`B x))) τ
  | pair     : Judge M (Pair.f.type A B u)
    → Judge C τ_C
    → Reduces C C'
    → Judge N (Pair.g.type A B C' u)
    → Reduces (Pair.type A B C u) τ'
    → Judge (DCC? (⟨,⟩C M N)) τ'
  | swap   : Judge A (DCC? Sort u)
    → Judge B (DCC? Sort v)
    → Reduces (GenericExpr.Swap.type A B u v) τ'
    → Judge (DCC? (Swap A B)) τ'
  /-
    ef_α : α → Sort m
    f_β : ∀ (x : α) (y : f_α x), Sort n
    Π(f_α, f_β)
  -/
  | pi     : Judge B τ_B
    → Arrow A (DCC? Sort v) u τ_f_α
    → Judge C τ_C
    → Reduces B B'
    → Pi.C.type B' A u s τ_C
    → Reduces (Pi.type A u v s) τ
    → Judge (open Dsl in (DCC? (Π B C))) τ
  | sort   : Judge (DCC? Sort m) (DCC? Sort m.succ)
  | top    : Judge (DCC? ⊤) Top.type
  | bot    : Judge (DCC? ⊥) Bot.type
  | tintro : Judge (DCC? ∗) Tintro.type
  | bang   : Judge τ (DCC? Sort m) → Judge (open Dsl in (DCC? (! τ))) (DCC? Sort m)
  | box    : Judge x τ
    → Judge (open Dsl in (DCC? (& x))) (open Dsl in (DCC? (! τ)))
  | app    : Judge f (open Dsl in (DCC? ((Π f_α f_β) x_α)))
    → DefEq (DCC? (f_α x_α)) α
    → Judge x α
    → Reduces (DCC? (f_β x_α x)) τ
    → Judge (DCC? (f x)) τ
deriving Repr

-- Replaces everything from `def infer₂` to end-of-file.
-- Everything above (TypeError, Reduces, def_eq?, Judge, …) is unchanged.

def infer.{u} {τ_c : Type u} [hDecEq : DecidableEq τ_c] [BEq τ_c] (e : GenericExpr τ_c) : Except (TypeError e) (Σ' (t : GenericExpr τ_c), Judge e t) :=
  open Dsl in match e with
  | .dom₂ _x | .uncoup _x | .dom _x | .unbang _x | .hole _u => .error (.unexpected e e)
  | DCC? (Swap A B) =>
    match infer A with
    | .ok ⟨DCC? Sort u, h₁⟩ =>
      match infer B with
      | .ok ⟨DCC? Sort v, h₂⟩ =>
        .ok ⟨_, .swap h₁ h₂ (reduce_reduces rfl)⟩
      | .error e => .error (.sub B e)
      | .ok ⟨τ', _⟩ => .error (.sub B (.unexpected τ' B))
    | .error e => .error (.sub A e)
    | .ok ⟨τ', _⟩ => .error (.sub A (.unexpected τ' A))
  | DCC? (!<> f) =>
    match infer f with
    | .ok ⟨τ_f, ht₁⟩ =>
      match τ_f.read_arrow with
      | .ok ⟨A, DCC? Sort n, m, harr⟩ =>
        .ok ⟨_, .map ht₁ harr (reduce_reduces rfl)⟩
      | _ => .error (.mark 3 (.unexpected τ_f f))
    | .error e => .error (.sub f e)
  /-| DCC? !<f> =>
    match infer f with
    | .ok ⟨(DCC? (Π(Id(Sort m), f_β) α)), ⟨ht₁⟩⟩ =>
      match (DCC? (f_β α)).reduce_all with
      | (DCC? `(α₂, Sort n)) =>
        if heq : (DCC? (f_β α)).reduce_all = (DCC? `(α, Sort n)) then
          .ok ⟨_, ⟨.map ht₁ (reduce_reduces heq) (reduce_reduces rfl)⟩⟩
        else .error (.mismatch (DCC? `(α, Sort n)) (DCC? (f_β α)).reduce_all f)
      | x => .error (.mark 2 (.unexpected x f))
    | .ok ⟨t, _⟩ => .error (.mark 1 (.unexpected t f))
    | .error ε => .error (.sub f ε)-/
  /-| DCC? !<f> =>
    match infer f with
    | .ok ⟨(DCC? (Π(Id(Sort m), f_β) α)), ⟨ht₁⟩⟩ =>
      .ok ⟨_, ⟨.map ht₁ (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
    | .ok ⟨t, _⟩ => .error (.mark 1 (.unexpected t f))
    | .error ε => .error (.sub f ε)-/
  | DCC? ($<> f) =>
    match f.infer with
    | .ok ⟨(DCC? ((Π (Id Sort m) B) α)), ht⟩ =>
      .ok ⟨_, .fmap ht (reduce_reduces rfl)⟩
    | .ok ⟨t, _⟩ => .error (.unexpected t f)
    | .error ε => .error (.sub f ε)
  | DCC? (* A) =>
    match A.infer with
    | .ok ⟨DCC? Sort _m, ht⟩ =>
      .ok ⟨_, .unbox ht⟩
    | .error ε => .error (.sub A ε)
    | .ok ⟨τ, _⟩ => .error (.unexpected τ A)
  | DCC? (! τ) =>
    match τ.infer with
    | .ok ⟨DCC? Sort _m, ht⟩ => .ok ⟨_, .bang ht⟩
    | .ok ⟨t, _⟩ => .error (.unexpected t τ)
    | .error ε => .error (.sub τ ε)
  | DCC? (& x) =>
    match x.infer with
    | .ok ⟨_τ, ht⟩ => .ok ⟨_, .box ht⟩
    | .error ε => .error (.sub x ε)
  | DCC? ⊤ => .ok ⟨_, .top⟩
  | DCC? ⊥ => .ok ⟨_, .bot⟩
  | DCC? ∗ => .ok ⟨_, .tintro⟩
  | DCC? Sort _m => .ok ⟨_, .sort⟩
  | DCC? (Id α) =>
    match infer α with
    | .ok ⟨DCC? Sort m, ht⟩ =>
      .ok ⟨_, .id ht (reduce_reduces rfl)⟩
    | .ok ⟨t, _⟩ => .error (.unexpected t α)
    | .error ε => .error (.sub α ε)
  | DCC? (∘ f g) =>
    match infer g with
    | .ok ⟨τ_g, ht₁⟩ =>
      match τ_g.read_arrow with
      | .ok ⟨A, B, m, harr_g⟩ =>
        match infer f with
        | .ok ⟨DCC? ((Π (Id Sort n) (`(Sort n₂) C)) B₂), ht₂⟩ =>
          if heq₁ : n = n₂ then
            if heq₂ : B₂ = B then
              .ok ⟨_, .comp ht₁ harr_g (heq₁ ▸ heq₂ ▸ ht₂) (reduce_reduces rfl)⟩
            else .error (.unexpected τ_g f)
          else .error (.unexpected τ_g f)
        | .ok ⟨τ, _⟩ => .error (.unexpected τ g)
        | .error ε => .error (.sub f ε)
      | .error e => .error (.sub τ_g e)
      /-if heq : (DCC? (Π(Id(Sort m), `(_m, *<Σ(__a, Λ(_a, _b, `(___a, β)))>)) !(α))) = comp.g.type α β m then
        match infer f with
        | .ok ⟨(DCC? (Π(Id(Sort n), f_γ) Coup(f_β))), ⟨ht₂⟩⟩ =>
          if _heq₂ : (DCC? (Π(Id(Sort n), f_γ) Coup(f_β))) = comp.f.type f_β f_γ n then
            if heq₃ : f_β.reduce_all = (DCC? `(α, β)) then
              .ok ⟨_, ⟨.comp (heq ▸ ht₁) ht₂ (reduce_reduces heq₃) (reduce_reduces rfl) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
            else .error (.mismatch (DCC? `(α, β)) f_β.reduce_all f)
          else .error (.mismatch (comp.f.type f_β f_γ n) (DCC? (Π(Id(Sort n), f_γ) Coup(f_β))) f)
        | .ok ⟨t, _⟩ => .error (.unexpected t f)
        | .error ε => .error (.sub f ε)
      else .error (.mismatch (comp.g.type α β m) (DCC? (Π(Id(Sort m), `(_m, *<Σ(__a, Λ(_a, _b, `(___a, β)))>)) !(α))) g)-/
    | .error ε => .error (.sub g ε)
  | DCC? (= x y) =>
    match infer x with
    | .ok ⟨t_x, ht₁⟩ =>
      match infer y with
      | .ok ⟨t_y, ht₂⟩ =>
        if heq : t_x = t_y then
          .ok ⟨_, .eq ht₁ (heq ▸ ht₂)⟩
        else .error (.mismatch t_x t_y y)
      | .error ε => .error (.sub y ε)
    | .error ε => .error (.sub x ε)
  | DCC? (Eql f_α) =>
    match infer f_α with
    | .ok ⟨τ, ht₁⟩ =>
      match τ.read_arrow with
      | .ok ⟨δ, DCC? Sort _m, o, h⟩ =>
        .ok ⟨_, .eql ht₁ h (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC? (refl f_α) =>
    match infer f_α with
    | .ok ⟨τ, ht₁⟩ =>
      match τ.read_arrow with
      | .ok ⟨δ, DCC? Sort _m, o, h⟩ =>
        .ok ⟨_, .refl ht₁ h (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC? (Σ f_α f_β) =>
    match f_α.infer with
    | .ok ⟨τ_f_α, h₁⟩ =>
      match τ_f_α.read_arrow with
      | .ok ⟨δ, DCC? Sort m, o, harr⟩ =>
        match infer f_β with
        | .ok ⟨τ_f_β, h₂⟩ =>
          match τ_f_β.view_pi_f_β (reduce_all f_α) δ o with
          | .some ⟨n, h₃⟩ =>
            .ok ⟨_, .sigma h₁ harr h₂ (reduce_reduces rfl) h₃ (reduce_reduces rfl)⟩
          | _ => .error (.unexpected τ_f_β f_β)
        | .error ε => .error (.sub f_β ε)
      | _ => .error (.unexpected τ_f_α f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC? (,B x y) =>
    match infer x with
    | .ok ⟨α, ht₁⟩ =>
      match infer y with
      | .ok ⟨Bxm, ht₂⟩ =>
        match B.infer with
        | .ok ⟨τ_B, h₃⟩ =>
          match τ_B.read_arrow₁ α with
          | .ok ⟨DCC? Sort _n, _m, harr⟩ =>
            if heq₂ : reduce_all (DCC? (B x)) = Bxm then
              .ok ⟨_, .mk ht₁ h₃ harr
                (reduce_reduces (B := Bxm) (heq₂ ▸ rfl)) ht₂ (reduce_reduces rfl)⟩
            else .error (.mismatch (reduce_all (DCC? (B x))) Bxm y)
          | _ => .error (.unexpected τ_B B)
        | .error ε => .error (.sub B ε)
      | .error ε => .error (.sub y ε)
    | .error ε => .error (.sub x ε)
  | DCC? (Σ B) =>
    match infer B with
    | .ok ⟨τ_B, ht⟩ =>
      match read_arrow τ_B with
      | .ok ⟨_A, DCC? Sort v, u, harr⟩ =>
        .ok ⟨_, .coup ht harr (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ_B B)
      /-match (DCC? (f_B α)).reduce_all with
      | DCC? `(_α₂, Sort n) =>
        if heq : (DCC? (f_B α)).reduce_all = DCC? `(α, Sort n) then
          .ok ⟨_, ⟨.coup ht (reduce_reduces heq) (reduce_reduces rfl)⟩⟩
        else .error (.mismatch (DCC? `(α, Sort n)) (DCC? (f_B α)).reduce_all B)
      | other => .error (.unexpected other B)-/
    | .error ε => .error (.sub B ε)
  | DCC? (Fst B) =>
    match (infer B) with
    | .ok ⟨τ_β, ht₁⟩ =>
      match τ_β.read_arrow with
      | .ok ⟨_α, DCC? Sort _n, _m, harr⟩ =>
        .ok ⟨_, .fstc ht₁ harr (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ_β B)
    | .error ε => .error (.sub B ε)
  | DCC? (Snd B) =>
    match (infer B) with
    | .ok ⟨τ_β, ht₁⟩ =>
      match τ_β.read_arrow with
      | .ok ⟨_α, DCC? Sort _n, _m, harr⟩ =>
        .ok ⟨_, .sndc ht₁ harr (reduce_reduces rfl)⟩
      | _ => .error (.unexpected τ_β B)
    | .error ε => .error (.sub B ε)
  | DCC? (Λ A B x) =>
    match A.infer with
    | .ok ⟨DCC? Sort m, ht⟩ =>
      match B.infer with
      | .ok ⟨τ_β, ht_β⟩ =>
        match τ_β.read_arrow₂ (reduce_all A) m with
        | .ok ⟨DCC? Sort n, h⟩ =>
          match infer x with
          | .ok ⟨DCC? ((Π _A (`_B C)) _D), ht₂⟩ =>
            if heq : (DCC? ((Π _A (`_B C)) _D)) = (curr.x.type (reduce_all B) C m n) then
              .ok ⟨_, .curr ht ht_β h (heq ▸ ht₂) (reduce_reduces rfl) (reduce_reduces rfl)⟩
            else .error (.sub x (.unexpected (DCC? ((Π _A (`_B C)) _D)) e))
          | .error e => .error (.sub x e)
          | .ok ⟨τ, _⟩ => .error (.sub x (.unexpected τ e))
        | _ => .error (.unexpected τ_β B)
      | .error ε => .error (.sub B ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t A)
    | .error ε => .error (.sub A ε)
  | DCC? (!Λ A B x) =>
    match A.infer with
    | .ok ⟨DCC? Sort m, ht⟩ =>
      match B.infer with
      | .ok ⟨τ_β, ht_β⟩ =>
        match τ_β.read_arrow₂ (reduce_all A) m with
        | .ok ⟨DCC? Sort n, h⟩ =>
          match infer x with
          | .ok ⟨DCC? ((Π _A (`_B C)) _D), ht₂⟩ =>
            if heq : (DCC? ((Π _A (`_B C)) _D)) = (curr'.x.type (reduce_all B) C m n) then
              .ok ⟨_, .curr' ht ht_β h (heq ▸ ht₂) (reduce_reduces rfl) (reduce_reduces rfl)⟩
            else .error (.sub x (.unexpected (DCC? ((Π _A (`_B C)) _D)) e))
          | .error e => .error (.sub x e)
          | .ok ⟨τ, _⟩ => .error (.sub x (.unexpected τ e))
        | _ => .error (.unexpected τ_β B)
      | .error ε => .error (.sub B ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t A)
    | .error ε => .error (.sub A ε)
  | DCC? (Eval A B x) =>
    match A.infer with
    | .ok ⟨DCC? Sort u, ht⟩ =>
      match B.infer with
      | .ok ⟨τ_β, ht_β⟩ =>
        match τ_β.read_arrow₂ (reduce_all A) u with
        | .ok ⟨DCC? Sort v, h⟩ =>
            match infer x with
            | .ok ⟨DCC? ((Π _A (`_B (Π _C C))) _D), ht₂⟩ =>
              if heq : (DCC? ((Π _A (`_B (Π _C C))) _D)) = (GenericExpr.Eval.x.type (reduce_all A) (reduce_all B) C u) then
                .ok ⟨_, .eval ht ht_β h (heq ▸ ht₂) (reduce_reduces rfl) (reduce_reduces rfl) (reduce_reduces rfl)⟩
              else .error (.sub x (.unexpected (DCC? ((Π _A (`_B C)) _D)) e))
            | .error e => .error (.sub x e)
            | .ok ⟨τ, _⟩ => .error (.sub x (.unexpected τ e))
        | _ => .error (.unexpected τ_β B)
      | .error e => .error (.sub B e)
    | .ok ⟨t, _⟩ => .error (.unexpected t A)
    | .error ε => .error (.sub A ε)
  | DCC? (`B x) =>
    match infer x with
    | .ok ⟨A, ht₁⟩ =>
      match infer B with
      | .ok ⟨DCC? Sort v, ht₂⟩ =>
        .ok ⟨_, .quot ht₁ ht₂ (reduce_reduces rfl)⟩
      | .ok ⟨t, _⟩ => .error (.unexpected t B)
      | .error ε => .error (.sub B ε)
    | .error ε => .error (.sub x ε)
  | DCC? (⟨,⟩C M N) =>
    match infer M with
    | .ok ⟨DCC? ((Π (Id Sort u) (`(Sort u₂) B)) A), ht_M⟩ =>
      dbg_trace "1"
      if heq : (DCC? ((Π (Id Sort u) (`(Sort u₂) B)) A)) = (Pair.f.type A B u) then
        dbg_trace "2"
        match infer C with
        | .ok ⟨τ_C, ht_C⟩ =>
          dbg_trace "3"
          dbg_trace repr B
          dbg_trace repr A
          dbg_trace "4"
          dbg_trace "5"
          match infer N with
          | .ok ⟨τ_N, ht_N⟩ =>
            dbg_trace "6"
            if heq₂ : τ_N = (Pair.g.type A B (reduce_all C) u) then
              dbg_trace "7"
              dbg_trace repr (Pair.type A B C u)
              .ok ⟨_, .pair (heq ▸ ht_M) ht_C (reduce_reduces rfl) (heq₂ ▸ ht_N) (reduce_reduces rfl)⟩
            else .error (.sub N (.unexpected N τ_N))
          | .error e => .error (.sub N e)
        | .error e => .error (.sub C e)
      else
        .error (.sub M (.unexpected M (DCC? ((Π (Id Sort u) (`(Sort u₂) B)) A))))
    | .error e => .error (.sub M e)
    | .ok ⟨τ_M, _⟩ => .error (.sub M (.unexpected M τ_M))
  | DCC? (Π B C) =>
    match B.infer with
    | .ok ⟨τ_B, ht₁⟩ =>
      match τ_B.read_arrow with
      | .ok ⟨A, DCC? Sort v, u, harr⟩ =>
        match infer C with
        | .ok ⟨τ_C, ht₂⟩ =>
          match τ_C.view_pi_f_β (reduce_all B) A u with
          | .some ⟨s, h₂⟩ =>
            .ok ⟨_, .pi ht₁ harr ht₂ (reduce_reduces rfl) h₂ (reduce_reduces rfl)⟩
          | _ => .error (.mark 4 (.unexpected τ_C C))
        | .error ε => .error (.mark 3 (.sub C ε))
      | _ => .error (.mark 2 (.unexpected τ_B B))
    | .error ε => .error (.mark 1 (.sub B ε))
  | DCC? (f x) =>
    match infer f with
    | .ok ⟨DCC? ((Π f_α f_β) x_α), ht₁⟩ =>
      match infer x with
      | .ok ⟨τ₂', ht₂⟩ =>
        match def_eq? (DCC? (f_α x_α)) τ₂' with
        | .ok h =>
           .ok ⟨_, .app ht₁ h ht₂ (reduce_reduces rfl)⟩
        | .error e => .error (.sub (DCC? (f_α x_α)) (.def_eq e))
      | .error ε => .error (.sub x ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t f)
    | .error ε => .error (.sub f ε)
  | .const c => .error (.unexpected (.const c) (.const c))

abbrev infer' {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr τ_c) : Except (TypeError e) (GenericExpr τ_c) := (·.fst) <$> e.infer

instance [DecidableEq τ_c] [Repr τ_c] : Repr (Σ' (τ : GenericExpr τ_c), Judge A τ) := ⟨fun ⟨B, x⟩ =>
  Repr.addAppParen s!"PSigma.mk {repr B} ({repr x})"⟩

end GenericExpr

abbrev Expr.infer' (e : Expr) : Except (TypeError e) Expr := (·.fst) <$> e.infer
abbrev Expr.infer (e : Expr) : Except (TypeError e) (Σ' (t : GenericExpr Unit), (GenericExpr.Judge e t)) := GenericExpr.infer e

#eval (DCC ((Id Sort 1) (Sort 0))).infer
#eval (DCC ((Id ((Sort 1 : Sort 2) → Sort 1)) (Id Sort 1))).infer
