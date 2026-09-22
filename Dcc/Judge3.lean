import Dcc.Ast
import Dcc.Aff.Red
import Dcc.Types
import Dcc.Eta.Nbe2.Canonicalize

inductive DefEqError.{u} {τ_c : Type u} : (A B : GenericExpr τ_c) → Type u where
  /-| pi_left  (expected actual : GenericExpr τ_c)  : DefEqError A B
  | pi_right (expected actual : GenericExpr τ_c)  : DefEqError A B
  | bang     (inner_errr      : DefEqError τ₁ τ₂) : DefEqError (DCC? !(τ₁)) (DCC? !(τ₂))
  | coup     (inner_errr      : DefEqError τ₁ τ₂) : DefEqError (DCC? Coup(τ₁)) (DCC? Coup(τ₂))-/
  | tm       (expected actual : GenericExpr τ_c)  : DefEqError A B
  | not_eta_reducible (at_e : GenericExpr τ_c)    : DefEqError A B
deriving DecidableEq

def DefEqError.flip (e : DefEqError A B) : DefEqError B A :=
  match e with
  | .tm expected actual => .tm expected actual
  | .not_eta_reducible x => .not_eta_reducible x

def DefEqError.toFormat (err : DefEqError (τ_c := τ_c) A B) : Std.Format :=
  "- " ++ (.nest 2 <| (Std.format A) ++ " ≠ " ++ (.indentD (Std.format B)) ++ .line ++
  (match err with
  /-| .pi_left expected actual => "because Π domains are not def-eq. Expected: " ++ (.indentD (Std.format expected)) ++ "but found: " ++ (.indentD (Std.format actual))
  | .pi_right expected actual => "because Π codomains are not def-eq. Expected: " ++ (.indentD (Std.format expected)) ++ "but found: " ++ (.indentD (Std.format actual))
  | .bang inner_err => "because bang types are not def-eq because: " ++ inner_err.toFormat
  | .coup inner_err => "because coup types are not def-eq because: " ++ inner_err.toFormat-/
  | .not_eta_reducible x => "because this term is not η-reducible: " ++ (.indentD (Std.format x))
  | .tm expected actual => "because terms are not def-eq. Expected: " ++ (.indentD (Std.format expected)) ++ .line ++ "but found: " ++ (.indentD (Std.format actual))))

instance {A B : GenericExpr τ_c} : Std.ToFormat (DefEqError A B) := ⟨DefEqError.toFormat⟩
instance {A B : GenericExpr τ_c} : ToString (DefEqError A B) := ⟨toString ∘ Std.format⟩

inductive TypeError.{u} {τ_c : Type u} : (e : GenericExpr τ_c) → Type u where
  | mismatch (expected actual at_e : GenericExpr τ_c) : TypeError e
  | unexpected (found at_e : GenericExpr τ_c) : TypeError e
  | sub (at_e : GenericExpr τ_c) (err : TypeError at_e) : TypeError e
  | def_eq {τ₁ τ₂ : GenericExpr τ_c} (err : DefEqError τ₁ τ₂) : TypeError e
  | mark (n : ℕ) (ε : TypeError e) : TypeError e

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
  | mk : RedAffNorm A ⟨B, hn_B⟩
    → RedEta B C
    → Reduces A C
deriving Repr

def Reduces.aff (h : Reduces A B) : RedAffNorm A (red_aff A) :=
  match h with
  | ⟨hr₁, _hn₂⟩ =>
    hr₁.out_eq ▸ hr₁

def Reduces.unique.{u} {τ_c : Type u} [DecidableEq τ_c] {A B C : GenericExpr τ_c}
  (h₁ : Reduces A B) (h₂ : Reduces A C) : B = C :=
  match h₁, h₂ with
  | ⟨hr₁, hr₂⟩, ⟨hr₃, hr₄⟩ => by
    cases hr₁.unique hr₃
    exact Unique.unique hr₂ hr₄

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
def reduce_all.{u} {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr τ_c) (e₂ : GenericExpr τ_c := e) : Except (DefEqError e e₂) (GenericExpr τ_c) :=
  match (red_eta (τ_c := τ_c)) (reduce' RedAff e) with
  | .some ⟨e', _⟩ => .ok e'
  | .none => .error (.not_eta_reducible e)

def reduce_reduces.{u} {τ_c : Type u} [DecidableEq τ_c] {A B : GenericExpr τ_c} {e₂ : GenericExpr τ_c} (h : reduce_all A (e₂ := e₂) = .ok B) : Reduces A B := ⟨aff_sound rfl, by
  simp [reduce_all, reduce'] at h
  split at h
  · cases h
    assumption
  · grind⟩

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def Reduces.complete.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {τ τ' : GenericExpr τ_c}
  (h : Reduces (τ_c := τ_c) τ τ') {e₂ : GenericExpr τ_c} : reduce_all τ (e₂ := e₂) = .ok τ' := by
  match h with
  | ⟨hr, hr₂⟩ =>
    have ha := hr.complete
    have hb := hr₂.complete
    have hc := Complete'.complete hr₂
    simp [reduce_all, reduce']
    have hc := run_sound hc
    grind

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def Reduces.out_eq [DecidableEq τ_c] (h : Reduces (τ_c := τ_c) A B) : .ok B = reduce_all A (e₂ := B) :=
  match h with
  | ⟨hr, hr'⟩ => by
    cases hr.out_eq
    simp [reduce_all]
    have ha := hr.complete
    have hb := hr'.complete
    grind

def Reduces.push_head [DecidableEq τ_c] (h : Reduces (τ_c := τ_c) A C) (hr : RedAff A B) : Reduces B C :=
  match h with
  | ⟨hrt, hn⟩ => ⟨hrt.push_head hr, hn⟩

def Reduces.elim_norm [DecidableEq τ_c] (h : Reduces (τ_c := τ_c) A B) (hn : IsNorm RedAff A) : RedEta A B :=
  match h with
  | ⟨hrt, hn'⟩ => by
    cases hrt.elim_norm hn
    assumption

def Reduces.eq [DecidableEq τ_c] (h : Reduces (τ_c := τ_c) A B) : h = reduce_reduces (A := A) (B := B) (e₂ := B) (h.out_eq ▸ rfl) :=
  match h with
  | ⟨hr, hr'⟩ => by
    rw [hr.out_eq] at *
    expose_names
    cases hr_1.unique hr
    cases hr_1.eq
    simp only [reduce_reduces]
    congr!
    apply proof_eq

def Reduces.eq' [DecidableEq τ_c] (h₁ : Reduces (τ_c := τ_c) A B) (h₂ : Reduces (τ_c := τ_c) A B) : h₁ = h₂ :=
  match h₁, h₂ with
  | ⟨hr₁, hr₂⟩, ⟨hr₃, hr₄⟩ => by
    cases hr₁.unique hr₃
    cases hr₁.out_eq
    cases hr₁.eq
    cases hr₃.eq
    congr!
    apply proof_eq

#eval Std.format <| pair.β.type (DCC (Sort 30)) 10 20

-- For checking arguments under apps
inductive DefEq.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] : GenericExpr τ_c → GenericExpr τ_c → Type u
  | tm : Reduces τ₁ τ' → Reduces τ₂ τ' → DefEq τ₁ τ₂

-- Reduces A B → DefEq A B

def def_eq?.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] (τ₁ τ₂ : GenericExpr τ_c) : Except (DefEqError τ₁ τ₂) (PLift (DefEq τ₁ τ₂)) :=
  match heq₀ : τ₁.reduce_all (e₂ := τ₂), heq₂ : τ₂.reduce_all (e₂ := τ₁) with
  | .ok hτ₁, .ok hτ₂ =>
    if heq : hτ₁ = hτ₂ then
      .ok ⟨.tm (reduce_reduces heq₀) (reduce_reduces (heq ▸ heq₂))⟩
    else .error (.tm hτ₁ hτ₂)
  | .error e, _ => .error e
  | _, .error e => .error e.flip

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def DefEq.complete.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {τ₁ τ₂ : GenericExpr τ_c} (h : DefEq (τ_c := τ_c) τ₁ τ₂) : def_eq? τ₁ τ₂ = .ok ⟨h⟩ := by
  induction h
  case tm hr₁ hr₂ =>
    expose_names
    have ha := hr₁.complete (e₂ := τ₂_1)
    have hb := hr₂.complete (e₂ := τ₁)
    simp [def_eq?]
    split
    case h_1 =>
      expose_names
      cases heq.symm.trans ha
      cases heq_1.symm.trans hb
      simp
      constructor
      · apply Eq.symm
        apply Reduces.eq'
      · apply Eq.symm
        apply Reduces.eq'
    · grind
    · grind

inductive Judge.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] : GenericExpr τ_c → GenericExpr τ_c → Type u where
  | eq     : Judge x α
    → Judge y α
    → Judge (DCC? x = y) (DCC? Sort 0)
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
    → Pi.C.type B A u s τ_C
    → Reduces C C'
    → Judge N (Pair.g.type A B C' u)
    → Reduces (Pair.type A B C u) τ'
    → Judge (DCC? (⟨,⟩C M N)) τ'
  | swap   : Judge B τ_B
    → Arrow A (DCC? Sort v) u τ_B
    → Judge C τ_C
    → Reduces B B'
    → Pi.C.type B' A u s τ_C
    → Judge (DCC? (Swap B C)) (GenericExpr.Swap.type B C u v)
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
    → Reduces (DCC? (f_α x_α)) α
    → Judge x α
    → Reduces (DCC? (f_β x_α x)) τ
    → Judge (DCC? (f x)) τ
deriving Repr

-- Replaces everything from `def infer₂` to end-of-file.
-- Everything above (TypeError, Reduces, def_eq?, Judge, …) is unchanged.

def infer.{u} {τ_c : Type u} [hDecEq : DecidableEq τ_c] [BEq τ_c] (e : GenericExpr τ_c) : Except (TypeError e) (Σ' (t : GenericExpr τ_c), Judge e t) :=
  open Dsl in match e with
  | .dom₂ _x | .uncoup _x | .dom _x | .unbang _x | .hole _u => .error (.unexpected e e)
  | DCC? (Swap B C) =>
    match infer B with
    | .ok ⟨τ_B, ht_B⟩ =>
      match read_arrow τ_B with
      | .some ⟨A, DCC? Sort _v, u, harr_B⟩ =>
        match heq : (reduce_all B) with
        | .ok B' =>
          match infer C with
          | .ok ⟨τ_C, ht_C⟩ =>
            match view_pi_f_β τ_C B' A u with
            | .some ⟨_, h_view_C⟩ =>
              .ok ⟨_ , .swap ht_B harr_B ht_C (reduce_reduces heq) h_view_C⟩
            | .none => .error (.unexpected τ_C C)
          | .error e => .error (.sub C e)
        | .error e => .error (.sub B (.def_eq e))
      | _ => .error (.sub B (.unexpected τ_B B))
    | .error e => .error (.sub B e)
  | DCC? (!<> f) =>
    match infer f with
    | .ok ⟨τ_f, ht₁⟩ =>
      match τ_f.read_arrow with
      | .some ⟨A, DCC? Sort n, m, harr⟩ =>
        match heq_τ' : reduce_all (DCC? (((! A) : Sort m) → Sort n)) with
        | .ok _τ' =>
          .ok ⟨_, .map ht₁ harr (reduce_reduces heq_τ')⟩
        | .error e => .error (.def_eq e)
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
      match heq_τ' : reduce_all (DCC? ((Π (Id Sort m) (`Sort m (!<> (B α)))) (! α))) with
      | .ok _τ' =>
        .ok ⟨_, .fmap ht (reduce_reduces heq_τ')⟩
      | .error e => .error (.def_eq e)
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
      match hred_τ' : reduce_all (id.type α m) with
      | .ok _τ =>
        .ok ⟨_, .id ht (reduce_reduces hred_τ')⟩
      | .error e => .error (.def_eq e)
    | .ok ⟨t, _⟩ => .error (.unexpected t α)
    | .error ε => .error (.sub α ε)
  | DCC? (∘ f g) =>
    match infer g with
    | .ok ⟨τ_g, ht₁⟩ =>
      match τ_g.read_arrow with
      | .some ⟨A, B, m, harr_g⟩ =>
        match infer f with
        | .ok ⟨DCC? ((Π (Id Sort n) (`(Sort n₂) C)) B₂), ht₂⟩ =>
          if heq₁ : n = n₂ then
            if heq₂ : B₂ = B then
              match heq_τ' : reduce_all (comp.type A C g m) with
              | .ok _τ' =>
                .ok ⟨_, .comp ht₁ harr_g (heq₁ ▸ heq₂ ▸ ht₂) (reduce_reduces heq_τ')⟩
              | .error e => .error (.def_eq e)
            else .error (.unexpected τ_g f)
          else .error (.unexpected τ_g f)
        | .ok ⟨τ, _⟩ => .error (.unexpected τ g)
        | .error ε => .error (.sub f ε)
      | .none => .error (.unexpected τ_g g)
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
  | DCC? x = y =>
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
      | .some ⟨δ, DCC? Sort _m, o, h⟩ =>
        match heq_τ' : reduce_all (eql.type f_α δ o) with
        | .ok _τ' =>
          .ok ⟨_, .eql ht₁ h (reduce_reduces heq_τ')⟩
        | .error e => .error (.def_eq e)
      | _ => .error (.unexpected τ f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC? (refl f_α) =>
    match infer f_α with
    | .ok ⟨τ, ht₁⟩ =>
      match τ.read_arrow with
      | .some ⟨δ, DCC? Sort _m, o, h⟩ =>
        match heq_τ' : reduce_all (GenericExpr.refl.type f_α δ o) with
        | .ok _τ' =>
          .ok ⟨_, .refl ht₁ h (reduce_reduces heq_τ')⟩
        | .error e => .error (.def_eq e)
      | _ => .error (.unexpected τ f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC? (Σ f_α f_β) =>
    match f_α.infer with
    | .ok ⟨τ_f_α, h₁⟩ =>
      match τ_f_α.read_arrow with
      | .some ⟨δ, DCC? Sort m, o, harr⟩ =>
        match infer f_β with
        | .ok ⟨τ_f_β, h₂⟩ =>
          match heq : (reduce_all f_α) with
          | .ok f_α' =>
            match τ_f_β.view_pi_f_β f_α' δ o with
            | .some ⟨n, h₃⟩ =>
              match heq_τ' : (reduce_all (Sigma.type δ m n o)) with
              | .ok _τ' =>
                .ok ⟨_, .sigma h₁ harr h₂ (reduce_reduces heq) h₃ (reduce_reduces heq_τ')⟩
              | .error e => .error (.def_eq e)
            | _ => .error (.unexpected τ_f_β f_β)
          | .error ε => .error (.sub f_α (.def_eq ε))
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
          | .some ⟨DCC? Sort _n, _m, harr⟩ =>
            match heq : reduce_all (DCC? (B x)) with
            | .ok Bxm' =>
              if heq₂ : Bxm' = Bxm then
                match heq_τ' : reduce_all (DCC? (Σ B)) with
                | .ok _τ' =>
                  .ok ⟨_, .mk ht₁ h₃ harr
                    (reduce_reduces (B := Bxm) (heq₂ ▸ heq)) ht₂ (reduce_reduces heq_τ')⟩
                | .error e => .error (.def_eq e)
              else .error (.mismatch Bxm' Bxm y)
            | .error e => .error (.sub B (.def_eq e))
          | _ => .error (.unexpected τ_B B)
        | .error ε => .error (.sub B ε)
      | .error ε => .error (.sub y ε)
    | .error ε => .error (.sub x ε)
  | DCC? (Σ B) =>
    match infer B with
    | .ok ⟨τ_B, ht⟩ =>
      match read_arrow τ_B with
      | .some ⟨_A, DCC? Sort v, u, harr⟩ =>
        match heq : reduce_all (Coup.type u v) with
        | .ok _τ =>
          .ok ⟨_, .coup ht harr (reduce_reduces heq)⟩
        | .error e => .error (.sub B (.def_eq e))
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
      | .some ⟨_α, DCC? Sort _n, _m, harr⟩ =>
        match heq : reduce_all (GenericExpr.fstc.type _α B _m _n) with
        | .ok _τ' => .ok ⟨_, .fstc ht₁ harr (reduce_reduces heq)⟩
        | .error ε => .error (.def_eq ε)
      | _ => .error (.unexpected τ_β B)
    | .error ε => .error (.sub B ε)
  | DCC? (Snd B) =>
    match (infer B) with
    | .ok ⟨τ_β, ht₁⟩ =>
      match τ_β.read_arrow with
      | .some ⟨_α, DCC? Sort _n, _m, harr⟩ =>
        match heq : reduce_all (GenericExpr.sndc.type B _m _n) with
        | .ok _τ' => .ok ⟨_, .sndc ht₁ harr (reduce_reduces heq)⟩
        | .error ε => .error (.def_eq ε)
      | _ => .error (.unexpected τ_β B)
    | .error ε => .error (.sub B ε)
  | DCC? (Λ A B x) =>
    match A.infer with
    | .ok ⟨DCC? Sort m, ht⟩ =>
      match B.infer with
      | .ok ⟨τ_β, ht_β⟩ =>
        match A.reduce_all with
        | .ok A' =>
          match τ_β.read_arrow₂ A' m with
          | .some ⟨DCC? Sort n, h⟩ =>
            match heq_red_B : B.reduce_all with
            | .ok B' =>
              match infer x with
              | .ok ⟨DCC? ((Π _A (`_B C)) _D), ht₂⟩ =>
                if heq : (DCC? ((Π _A (`_B C)) _D)) = (curr.x.type B' C m n) then
                  match heq_red : (curr.type A B C m).reduce_all with
                  | .ok _τ' =>
                    .ok ⟨_, .curr ht ht_β h (heq ▸ ht₂) (reduce_reduces heq_red_B) (reduce_reduces heq_red)⟩
                  | .error e => .error (.def_eq e)
                else .error (.sub x (.unexpected (DCC? ((Π _A (`_B C)) _D)) e))
              | .error e => .error (.sub x e)
              | .ok ⟨τ, _⟩ => .error (.sub x (.unexpected τ e))
            | .error e => .error (.sub B (.def_eq e))
          | _ => .error (.unexpected τ_β B)
        | .error ε => .error (.sub A (.def_eq ε))
      | .error ε => .error (.sub B ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t A)
    | .error ε => .error (.sub A ε)
  | DCC? (!Λ A B x) =>
    match A.infer with
    | .ok ⟨DCC? Sort m, ht⟩ =>
      match B.infer with
      | .ok ⟨τ_β, ht_β⟩ =>
        match A.reduce_all with
        | .ok A' =>
          match τ_β.read_arrow₂ A' m with
          | .some ⟨DCC? Sort n, h⟩ =>
            match heq_red_B : B.reduce_all with
            | .ok B' =>
              match infer x with
              | .ok ⟨DCC? ((Π _A (`_B C)) _D), ht₂⟩ =>
                if heq : (DCC? ((Π _A (`_B C)) _D)) = (curr'.x.type B' C m n) then
                  match heq_red : (curr'.type A B C m).reduce_all with
                  | .ok _τ' =>
                    .ok ⟨_, .curr' ht ht_β h (heq ▸ ht₂) (reduce_reduces heq_red_B) (reduce_reduces heq_red)⟩
                  | .error e => .error (.def_eq e)
                else .error (.sub x (.unexpected (DCC? ((Π _A (`_B C)) _D)) e))
              | .error e => .error (.sub x e)
              | .ok ⟨τ, _⟩ => .error (.sub x (.unexpected τ e))
            | .error e => .error (.sub B (.def_eq e))
          | _ => .error (.unexpected τ_β B)
        | .error ε => .error (.sub A (.def_eq ε))
      | .error ε => .error (.sub B ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t A)
    | .error ε => .error (.sub A ε)
  | DCC? (Eval A B x) =>
    match A.infer with
    | .ok ⟨DCC? Sort u, ht⟩ =>
      match B.infer with
      | .ok ⟨τ_β, ht_β⟩ =>
        match heq_red_A : A.reduce_all with
        | .ok A' =>
          match τ_β.read_arrow₂ A' u with
          | .some ⟨DCC? Sort v, h⟩ =>
              match heq_red_B : B.reduce_all with
              | .ok B' =>
                match infer x with
                | .ok ⟨DCC? ((Π _A (`_B (Π _C C))) _D), ht₂⟩ =>
                  if heq : (DCC? ((Π _A (`_B (Π _C C))) _D)) = (GenericExpr.Eval.x.type A' B' C u) then
                    match heq_red : (GenericExpr.Eval.type A B C u v).reduce_all with
                    | .ok _τ' =>
                      .ok ⟨_, .eval ht ht_β h (heq ▸ ht₂) (reduce_reduces heq_red_A) (reduce_reduces heq_red_B) (reduce_reduces heq_red)⟩
                    | .error e => .error (.def_eq e)
                  else .error (.sub x (.unexpected (DCC? ((Π _A (`_B C)) _D)) e))
                | .error e => .error (.sub x e)
                | .ok ⟨τ, _⟩ => .error (.sub x (.unexpected τ e))
              | .error e => .error (.sub B (.def_eq e))
          | _ => .error (.unexpected τ_β B)
        | .error ε => .error (.sub B (.def_eq ε))
      | .error e => .error (.sub B e)
    | .ok ⟨t, _⟩ => .error (.unexpected t A)
    | .error ε => .error (.sub A ε)
  | DCC? (`B x) =>
    match infer x with
    | .ok ⟨A, ht₁⟩ =>
      match infer B with
      | .ok ⟨DCC? Sort v, ht₂⟩ =>
        match heq_red : (quot.type A B v).reduce_all with
        | .ok _τ' =>
          .ok ⟨_, .quot ht₁ ht₂ (reduce_reduces heq_red)⟩
        | .error e => .error (.def_eq e)
      | .ok ⟨t, _⟩ => .error (.unexpected t B)
      | .error ε => .error (.sub B ε)
    | .error ε => .error (.sub x ε)
  | DCC? (⟨,⟩C M N) =>
    match infer M with
    | .ok ⟨DCC? ((Π (Id Sort u) (`(Sort u₂) B)) A), ht_M⟩ =>
      if heq : (DCC? ((Π (Id Sort u) (`(Sort u₂) B)) A)) = (Pair.f.type A B u) then
        match infer C with
        | .ok ⟨τ_C, ht_C⟩ =>
          match τ_C.view_pi_f_β B A u with
          | .some ⟨_s, h_pi_C⟩ =>
            match heq_red_C : C.reduce_all with
            | .ok C' =>
              match infer N with
              | .ok ⟨τ_N, ht_N⟩ =>
                if heq₂ : τ_N = (Pair.g.type A B C' u) then
                  match heq_τ' : (Pair.type A B C u).reduce_all with
                  | .ok _τ' =>
                    .ok ⟨_, .pair (heq ▸ ht_M) ht_C h_pi_C (reduce_reduces heq_red_C) (heq₂ ▸ ht_N) (reduce_reduces heq_τ')⟩
                  | .error e => .error (.def_eq e)
                else .error (.sub N (.unexpected N τ_N))
              | .error e => .error (.sub N e)
            | .error e => .error (.sub C (.def_eq e))
          | .none => .error (.sub C (.unexpected C τ_C))
        | .error e => .error (.sub C e)
      else
        .error (.sub M (.unexpected M (DCC? ((Π (Id Sort u) (`(Sort u₂) B)) A))))
    | .error e => .error (.sub M e)
    | .ok ⟨τ_M, _⟩ => .error (.sub M (.unexpected M τ_M))
  | DCC? (Π B C) =>
    match B.infer with
    | .ok ⟨τ_B, ht₁⟩ =>
      match τ_B.read_arrow with
      | .some ⟨A, DCC? Sort v, u, harr⟩ =>
        match infer C with
        | .ok ⟨τ_C, ht₂⟩ =>
          match h_red_B : B.reduce_all with
          | .ok B' =>
            match τ_C.view_pi_f_β B' A u with
            | .some ⟨s, h₂⟩ =>
              match heq_τ' : (Pi.type A u v s).reduce_all with
              | .ok _τ' =>
                .ok ⟨_, .pi ht₁ harr ht₂ (reduce_reduces h_red_B) h₂ (reduce_reduces heq_τ')⟩
              | .error e => .error (.def_eq e)
            | _ => .error (.mark 4 (.unexpected τ_C C))
          | .error e => .error (.sub B (.def_eq e))
        | .error ε => .error (.mark 3 (.sub C ε))
      | _ => .error (.mark 2 (.unexpected τ_B B))
    | .error ε => .error (.mark 1 (.sub B ε))
  | DCC? (f x) =>
    match infer f with
    | .ok ⟨DCC? ((Π f_α f_β) x_α), ht₁⟩ =>
      match infer x with
      | .ok ⟨τ₂', ht₂⟩ =>
        match heq_red_A : (DCC? (f_α x_α)).reduce_all with
        | .ok A =>
          if heq : A = τ₂' then
            match heq_τ' : (DCC? (f_β x_α x)).reduce_all with
            | .ok _τ' =>
              .ok ⟨_, .app ht₁ (reduce_reduces heq_red_A) (heq ▸ ht₂) (reduce_reduces heq_τ')⟩
            | .error e => .error (.def_eq e)
          else .error (.mismatch A τ₂' e)
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
