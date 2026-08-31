import Dcc.Ast
import Dcc.Aff.Red
import Dcc.Types
import Dcc.Eta.Nbe.Reduce

inductive DefEqError.{u} {τ_c : Type u} : (A B : GenericExpr τ_c) → Type u where
  | pi_left  (expected actual : GenericExpr τ_c)  : DefEqError A B
  | pi_right (expected actual : GenericExpr τ_c)  : DefEqError A B
  | bang     (inner_errr      : DefEqError τ₁ τ₂) : DefEqError (DCC? !(τ₁)) (DCC? !(τ₂))
  | coup     (inner_errr      : DefEqError τ₁ τ₂) : DefEqError (DCC? Coup(τ₁)) (DCC? Coup(τ₂))
  | tm       (expected actual : GenericExpr τ_c)  : DefEqError A B

def DefEqError.toFormat [Repr τ_c] (err : DefEqError (τ_c := τ_c) A B) : Std.Format :=
  "- " ++ (.nest 2 <| (Std.format A) ++ " ≠ " ++ (.indentD (Std.format B)) ++ .line ++
  (match err with
  | .pi_left expected actual => "because Π domains are not def-eq. Expected: " ++ (.indentD (Std.format expected)) ++ "but found: " ++ (.indentD (Std.format actual))
  | .pi_right expected actual => "because Π codomains are not def-eq. Expected: " ++ (.indentD (Std.format expected)) ++ "but found: " ++ (.indentD (Std.format actual))
  | .bang inner_err => "because bang types are not def-eq because: " ++ inner_err.toFormat
  | .coup inner_err => "because coup types are not def-eq because: " ++ inner_err.toFormat
  | .tm expected actual => "because terms are not def-eq. Expected: " ++ (.indentD (Std.format expected)) ++ .line ++ "but found: " ++ (.indentD (Std.format actual))))

instance {A B : GenericExpr τ_c} [Repr τ_c] : Std.ToFormat (DefEqError A B) := ⟨DefEqError.toFormat⟩
instance {A B : GenericExpr τ_c} [Repr τ_c] : ToString (DefEqError A B) := ⟨toString ∘ Std.format⟩

inductive TypeError.{u} {τ_c : Type u} : (e : GenericExpr τ_c) → Type u where
  | mismatch (expected actual at_e : GenericExpr τ_c) : TypeError e
  | unexpected (found at_e : GenericExpr τ_c) : TypeError e
  | sub (at_e : GenericExpr τ_c) (err : TypeError at_e) : TypeError e
  | def_eq {τ₁ τ₂ : GenericExpr τ_c} (err : DefEqError τ₁ τ₂) : TypeError e
  | mark (n : ℕ) (ε : TypeError e) : TypeError e

def TypeError.toFormat [Repr τ_c] (err : TypeError (τ_c := τ_c) e) : Std.Format :=
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

instance {e : GenericExpr τ_c} [Repr τ_c] : Std.ToFormat (TypeError e) := ⟨TypeError.toFormat⟩
instance {e : GenericExpr τ_c} [Repr τ_c] : ToString (TypeError e) := ⟨toString ∘ Std.format⟩

namespace GenericExpr

inductive Reduces.{u} {τ_c : Type u} : GenericExpr τ_c → GenericExpr τ_c → Type u
  | mk : RedAffNorm A B
    → B.raw.RedEta C
    → Reduces A C

def Reduces.aff (h : Reduces A B) : RedAffNorm A (red_aff A) :=
  match h with
  | ⟨hr₁, _hn₂⟩ =>
    hr₁.out_eq ▸ hr₁

def Reduces.unique.{u} {τ_c : Type u} [DecidableEq τ_c] {A B C : GenericExpr τ_c}
  (h₁ : Reduces A B) (h₂ : Reduces A C) : B = C :=
  match h₁, h₂ with
  | ⟨hr₁, hr₂⟩, ⟨hr₃, hr₄⟩ => by
    cases hr₁.unique hr₃
    exact hr₂.unique hr₄

/-def Reduces₂.trans.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {A B C : GenericExpr τ_c} (h₁ : Reduces₂ A B) (h₂ : Reduces₂ B C) : Reduces₂ A C :=
  match h₁, h₂ with
  | ⟨hr₁, hn₁, hr₂⟩, ⟨hr₃, hn₃, hr₄⟩ => by
    have ha := hr₂.is_norm hn₁
    have hb := hr₃
    have heq := hb.elim_head_norm ha
    cases heq

    exact ⟨hr₁, hn₁, by sorry⟩-/

def Reduces.is_norm.{u} {τ_c : Type u} {A B : GenericExpr τ_c} : Reduces A B → IsNorm RedAff B :=
  fun ⟨_hr₁, hr₂⟩ => hr₂.is_norm

@[dcc_force_reduce]
def reduce_all.{u} {τ_c : Type u} [DecidableEq τ_c] := (red_eta' (τ_c := τ_c)) ∘ reduce' RedAff

def reduce_reduces.{u} {τ_c : Type u} [DecidableEq τ_c] {A B : GenericExpr τ_c} (h : reduce_all A = B) : Reduces A B := ⟨aff_sound rfl, by
  simp [reduce_all, reduce'] at h
  simp [← h]
  exact red_eta_sound⟩

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def Reduces.complete.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {τ τ' : GenericExpr τ_c}
  (h : Reduces (τ_c := τ_c) τ τ') : reduce_all τ = τ' := by
  match h with
  | ⟨hr, hr₂⟩ =>
    have ha := hr.complete
    have hb := hr₂.complete
    have hc := hr₂.complete'
    simp [reduce_all, reduce']
    have hc := red_eta_sound' hc
    grind

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def Reduces.out_eq [DecidableEq τ_c] (h : Reduces (τ_c := τ_c) A B) : B = reduce_all A :=
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

def Reduces.eq [DecidableEq τ_c] (h : Reduces (τ_c := τ_c) A B) : h = reduce_reduces (A := A) (B := B) (h.out_eq ▸ rfl) :=
  match h with
  | ⟨hr, hr'⟩ => by
    rw [hr.out_eq] at *
    expose_names
    cases hr_1.unique hr
    cases hr_1.eq
    cases hr'_1.complete'
    simp only [reduce_reduces]
    have h := hr'_1.complete
    unfold red_eta_sound
    have h := hr'_1.eq'
    rw [h]
    congr

#eval Std.format <| pair.β.type (DCC (Sort 30)) 10 20

-- For checking arguments under apps
inductive DefEq.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] : GenericExpr τ_c → GenericExpr τ_c → Prop
  | pi      : Reduces (DCC? (f_α₁ env₁)) f_α'
    → Reduces (DCC? (f_α₂ env₂)) f_α'
    → Reduces (DCC? (f_β₁ env₁)) f_β'
    → Reduces (DCC? (f_β₂ env₂)) f_β'
    → DefEq (DCC? (Π(f_α₁, f_β₁) env₁)) (DCC? (Π(f_α₂, f_β₂) env₂))
  | bang    : DefEq τ₁ τ₂ → DefEq (DCC? !(τ₁)) (DCC? !(τ₂))
  | coup    : DefEq τ₁ τ₂ → DefEq (DCC? Coup(τ₁)) (DCC? Coup(τ₂))
  | pi_comp : Reduces (DCC? (Π(f_α₁, f_β₁) ∘' g₁)) τ'
    → Reduces (DCC? (Π(f_α₂, f_β₂) ∘' g₂)) τ'
    → DefEq (DCC? (Π(f_α₁, f_β₁) ∘' g₁)) (DCC? (Π(f_α₂, f_β₂) ∘' g₂))
  | tm : (IsEtaTm τ₁ ⊕ IsEtaTm τ₂)
    → Reduces τ₁ τ'
    → Reduces τ₂ τ'
    → DefEq τ₁ τ₂

-- Reduces A B → DefEq A B

def def_eq?.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] (τ₁ τ₂ : GenericExpr τ_c) : Except (DefEqError τ₁ τ₂) (PLift (DefEq τ₁ τ₂)) :=
  match τ₁.is_eta_tm?, τ₂.is_eta_tm? with
  | .some h₁, _ =>
    if heq : τ₁.reduce_all = τ₂.reduce_all then
      .ok ⟨.tm (.inl h₁) (reduce_reduces rfl) (reduce_reduces heq.symm)⟩
    else .error (.tm τ₁.reduce_all τ₂.reduce_all)
  | _, .some h₁ =>
    if heq : τ₁.reduce_all = τ₂.reduce_all then
      .ok ⟨.tm (.inr h₁) (reduce_reduces rfl) (reduce_reduces heq.symm)⟩
    else .error (.tm τ₁.reduce_all τ₂.reduce_all)
  | .none, .none =>
    match τ₁, τ₂ with
    | (DCC? (Π(f_α₁, f_β₁) ∘' g₁)), (DCC? (Π(f_α₂, f_β₂) ∘' g₂)) =>
      if heq : (DCC? (Π(f_α₁, f_β₁) ∘' g₁)).reduce_all = (DCC? (Π(f_α₂, f_β₂) ∘' g₂)).reduce_all then
        .ok ⟨.pi_comp (reduce_reduces heq) (reduce_reduces rfl)⟩
      else .error (.tm τ₁ τ₂)
    | (DCC? (Π(f_α₁, f_β₁) env₁)), (DCC? (Π(f_α₂, f_β₂) env₂)) =>
      if heq₁ : (DCC? (f_α₁ env₁)).reduce_all = (DCC? (f_α₂ env₂)).reduce_all then
        if heq₂ : (DCC? (f_β₁ env₁)).reduce_all = (DCC? (f_β₂ env₂)).reduce_all then
          .ok ⟨.pi (reduce_reduces rfl) (reduce_reduces heq₁.symm)
            (reduce_reduces rfl)  (reduce_reduces heq₂.symm)⟩
        else .error (.pi_right (DCC? (f_β₁ env₁)).reduce_all (DCC? (f_β₂ env₂)).reduce_all)
      else .error (.pi_left (DCC? (f_α₁ env₁)).reduce_all (DCC? (f_α₂ env₂)).reduce_all)
    | (DCC? !(τ₁)), (DCC? !(τ₂)) =>
      match def_eq? τ₁ τ₂ with
      | .ok ⟨h⟩ => .ok ⟨.bang h⟩
      | .error ε => .error (.bang ε)
    | (DCC? Coup(τ₁)), (DCC? Coup(τ₂)) =>
      match def_eq? τ₁ τ₂ with
      | .ok ⟨h⟩ => .ok ⟨.coup h⟩
      | .error ε => .error (.coup ε)
    | _, _ => .error (.tm τ₁ τ₂)

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
def DefEq.complete.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {τ₁ τ₂ : GenericExpr τ_c} (h : DefEq (τ_c := τ_c) τ₁ τ₂) : def_eq? τ₁ τ₂ = .ok ⟨h⟩ := by
  induction h
  case pi hr₁ hr₂ hr₃ hr₄ =>
    simp [def_eq?, is_eta_tm?, hr₁.complete, hr₂.complete, hr₃.complete, hr₄.complete]
  case coup h_deq heq | bang h_deq heq =>
    simp [def_eq?, is_eta_tm?, heq]
  case pi_comp hr₁ hr₂ =>
    simp [def_eq?, is_eta_tm?, hr₁.complete, hr₂.complete]
  case tm hn₁ hr₁ hr₂ =>
    have ha := hr₁.complete
    have hb := hr₂.complete
    unfold def_eq?
    match hn₁ with
    | .inl h =>
      simp [h.complete, ha, hb]
    | .inr h =>
      simp [h.complete, ha, hb]
      aesop

inductive Judge.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] : GenericExpr τ_c → GenericExpr τ_c → Prop where
  | eq     : Judge x α
    → Judge y α
    → Judge (DCC? x = y) (DCC? Sort 0)
  | refl    : Judge f_α τ_f_α
    → Arrow δ (DCC? Sort m) o τ_f_α
    → Reduces (refl.type f_α δ o) τ
    → Judge (DCC? refl(f_α)) τ
  | eql    : Judge f_α τ_f_α
    → Arrow δ (DCC? Sort m) o τ_f_α
    → Reduces (eql.type f_α δ o) τ
    → Judge (DCC? Eql(f_α)) τ
  | id     : Judge α (DCC? Sort m)
    → Reduces (id.type α m) τ
    → Judge (DCC? Id(α)) τ
  | comp   : Judge g (comp.g.type α β m)
    → Judge f (comp.f.type f_β f_γ n)
    → Reduces f_β (DCC? `(α, β))
    → Reduces (DCC? (f_γ Coup(`(α, β)))) γ
    → Reduces α α'
    → Reduces (comp.type α' γ g m) τ
    → Judge (DCC? (f ∘ g)) τ
  | comp₂  : Judge g τ_g
    → Comp₂.g.type α β m τ_g
    → Judge f (comp₂.f.type β f_γ n)
    → Reduces (DCC? (f_γ Coup(β))) γ
    → Reduces (comp₂.type α γ g m) τ
    → Judge (DCC? (f ∘∘ g)) τ
  | comp'  : Judge g (DCC? (Π(Id(Sort m), f_β₀) α))
    → Reduces (DCC? (f_β₀ α)) (DCC? (`(α, β)))
    → Judge f (DCC? (Π(f_β, f_γ) x_β))
    → Reduces (DCC? (f_β x_β)) β
    → Reduces (DCC? (f_γ x_β)) γ
    → Reduces α α'
    → Reduces (comp'.type α' γ g m) τ
    → Judge (DCC? f ∘' g) τ
  | coup   : Judge β (DCC? (Π(Id(Sort m), f_β) α))
    → Reduces (DCC? (f_β α)) (DCC? `(α, Sort n))
    → Reduces (Coup.type m n) τ
    → Judge (DCC? Coup(β)) τ
  | fstc   : Judge β τ_β
    → Arrow α (DCC? Sort n) m τ_β
    → Reduces (fstc.type α β m n) τ
    → Judge (DCC? Fst(β)) τ
  | sndc    : Judge β τ_β
    → Arrow α (DCC? Sort n) m τ_β
    → Reduces (sndc.type β m n) τ
    → Judge (DCC? Snd(β)) τ
  | sigma   : Judge f_α τ_f_α
    → Arrow δ (DCC? Sort m) o τ_f_α
    → Judge f_β τ_f_β
    -- f_α is not necessarily a normal form here. we need to reduce
    -- since it is not captured by Reduces Sigma.type
    → Reduces f_α f_α'
    → Pi.f_β.type f_α' δ o n τ_f_β
    → Reduces (Sigma.type δ m n o) τ
    → Judge (DCC? Σ(f_α, f_β)) τ
  | mk     : Judge x α
    → Judge β τ_β
    → Arrow α (DCC? Sort n) m τ_β
    → Reduces (DCC? (β x)) τ₂
    → Judge y τ₂
    → Reduces (DCC? Coup(β)) τ
    → Judge (DCC? ⟦β⟧(x, y)) τ
  /-
    Λ(β, x)
    β receives (α, x)
    β : Coup(Sort m, Id(Sort m)) → Sort n
  -/
  | curr   : Judge α (DCC? Sort m)
    → Judge x (DCC? (Π(f_α, γ) x_α))
    → Reduces (DCC? Coup(β)) τα
    → Reduces (DCC? (f_α x_α)) τα
    → Reduces (DCC? (γ x_α)) γ'
    → Reduces α α'
    → Reduces (curr.type α' β γ' m) τ
    → Judge (DCC? Λ(α, β, x)) τ
  | curr'  : Judge α (DCC? Sort m)
    → Judge x (DCC? (Π(f_α, γ) x_α))
    → Reduces (DCC? !(Coup(β))) τα
    → Reduces (DCC? (f_α x_α)) τα
    → Reduces (DCC? (γ x_α)) γ'
    → Reduces α α'
    → Reduces (curr'.type α' β γ' m) τ
    → Judge (DCC? !Λ(α, β, x)) τ
  -- !<f> &(x) = !(x)
  /-| map    : Judge x (DCC? (Π(Id(Sort m), f_β) α))
    → Reduces (DCC? (f_β α)) (DCC? `(α, Sort n))
    → Reduces (DCC? ((!(α) : Sort m) → Sort n)) τ
    → Judge (DCC? !<x>) τ-/
  | map    : Judge x τ_x
    → Arrow α (DCC? Sort n) m τ_x
    → Reduces (DCC? ((!(α) : Sort m) → Sort n)) τ
    → Judge (DCC? !<x>) τ
  | fmap   : Judge x (DCC? (Π(Id(Sort m), f_β) α))
    → Reduces (DCC? (f_β α)) β
    → Reduces (DCC? (Π(Id(Sort m), `(Sort m, !<β>)) !(α))) τ
    → Judge (DCC? $<x>) τ
  | eval   : Judge x (DCC? (Π(f_α, f_β) env))
    → Reduces α α'
    → Reduces β β'
    → Reduces (DCC? (f_α env)) α'
    → Reduces (DCC? (f_β env)) (DCC? (Π(β', γ)))
    → Judge α (DCC? Sort m)
    → Judge β (DCC? (Π(f_α₂, f_β₂) env₂))
    → Reduces (DCC? (f_α₂ env₂)) α'
    → Reduces (DCC? (f_β₂ env₂)) (DCC? `(α', Sort n))
    → Reduces (Eval.type α β γ m n) τ
    → Judge (DCC? Eval(α, β, x)) τ
  | quot   : Judge x α
    → Judge β (DCC? Sort n)
    → Reduces β β'
    → Reduces (quot.type α β' n) τ
    → Judge (DCC? `(β, x)) τ
  | pair   : Judge f (DCC? (Π(Id(Sort m), f_β) x_α))
    → Reduces (DCC? (f_β x_α)) β
    → Judge g (DCC? (Π(f_α₂, f_β₂) α))
    → Reduces γ γ'
    → Reduces (DCC? (f_β₂ α)) (DCC? (Π(β₂, γ₂)))
    → Reduces γ₂ γ'
    → Reduces β₂ β
    → Reduces (DCC? (f_α₂ α)) x_α
    → Reduces (pair.type x_α β γ' m) τ
    → Judge (DCC? ⟦γ⟧⟨f, g⟩) τ
  /-
    ef_α : α → Sort m
    f_β : ∀ (x : α) (y : f_α x), Sort n
    Π(f_α, f_β)
  -/
  | pi     : Judge f_α τ_f_α
    → Arrow δ (DCC? Sort m) o τ_f_α
    → Judge f_β τ_f_β
    → Reduces f_α f_α'
    → Pi.f_β.type f_α' δ o n τ_f_β
    → Reduces (Pi.type δ o m n) τ
    → Judge (DCC? Π(f_α, f_β)) τ
  | sort   : Judge (DCC? Sort m) (DCC? Sort m.succ)
  | top    : Judge (DCC? ⊤) Top.type
  | bot    : Judge (DCC? ⊥) Bot.type
  | tintro : Judge (DCC? ∗) Tintro.type
  | bang   : Judge τ (DCC? Sort m) → Judge (DCC? !(τ)) (DCC? Sort m)
  | box    : Judge x τ
    → Judge (DCC? &(x)) (DCC? !(τ))
  -- This should be dependent I think
  | unmap  : Judge f (DCC? (Π(Id(Sort m), f_β) α))
    → Reduces (DCC? (f_β α)) β
    → Reduces (DCC? ((Π(Id(Sort m), `(Sort m, *<β>)) !(α)))) τ
    → Judge (DCC? *<f>) τ
  | app    : Judge f (DCC? (Π(f_α, f_β) x_α))
    → Reduces (DCC? (f_α x_α)) α₁
    → Judge x α₂
    → DefEq α₁ α₂
    → Reduces x_α x_α'
    → Reduces (DCC? (f_β x_α' x)) τ
    → Judge (DCC? (f x)) τ

-- Replaces everything from `def infer₂` to end-of-file.
-- Everything above (TypeError, Reduces, def_eq?, Judge, …) is unchanged.

def infer.{u} {τ_c : Type u} [hDecEq : DecidableEq τ_c] [BEq τ_c] (e : GenericExpr τ_c) : Except (TypeError e) ((t : GenericExpr τ_c) × (PLift (Judge e t))) :=
  match e with
  | DCC? !<f> =>
    match infer f with
    | .ok ⟨τ_f, ⟨ht₁⟩⟩ =>
      match τ_f.read_arrow with
      | .some ⟨_α, DCC? Sort _n, _m, harr⟩ =>
        .ok ⟨_, ⟨.map ht₁ harr (reduce_reduces rfl)⟩⟩
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
  | DCC? $<f> =>
    match f.infer with
    | .ok ⟨(DCC? (Π(Id(Sort _m), _f_β) _α)), ⟨ht⟩⟩ =>
      .ok ⟨_, ⟨.fmap ht (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
    | .ok ⟨t, _⟩ => .error (.unexpected t f)
    | .error ε => .error (.sub f ε)
  | DCC? *<f> =>
    match f.infer with
    | .ok ⟨DCC? (Π(Id(Sort _m), _f_β) _α), ⟨ht₁⟩⟩ =>
      .ok ⟨_, ⟨.unmap ht₁ (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
    | .ok ⟨t, _⟩ => .error (.unexpected t f)
    | .error ε => .error (.sub f ε)
  | DCC? !(τ) =>
    match τ.infer with
    | .ok ⟨DCC? Sort _m, ⟨ht⟩⟩ => .ok ⟨_, ⟨.bang ht⟩⟩
    | .ok ⟨t, _⟩ => .error (.unexpected t τ)
    | .error ε => .error (.sub τ ε)
  | DCC? &(x) =>
    match x.infer with
    | .ok ⟨_τ, ⟨ht⟩⟩ => .ok ⟨_, ⟨.box ht⟩⟩
    | .error ε => .error (.sub x ε)
  | DCC? ⊤ => .ok ⟨_, ⟨.top⟩⟩
  | DCC? ⊥ => .ok ⟨_, ⟨.bot⟩⟩
  | DCC? ∗ => .ok ⟨_, ⟨.tintro⟩⟩
  | DCC? Sort _m => .ok ⟨_, ⟨.sort⟩⟩
  | DCC? (Id(α)) =>
    match infer α with
    | .ok ⟨DCC? Sort _m, ⟨ht⟩⟩ => .ok ⟨_, ⟨.id ht (reduce_reduces rfl)⟩⟩
    | .ok ⟨t, _⟩ => .error (.unexpected t α)
    | .error ε => .error (.sub α ε)
  | DCC? (f ∘ g) =>
    match infer g with
    | .ok ⟨DCC? (Π(Id(Sort m), `(_m, *<Σ(__a, Λ(_a, _b, `(___a, β)))>)) !(α)), ⟨ht₁⟩⟩ =>
      if heq : (DCC? (Π(Id(Sort m), `(_m, *<Σ(__a, Λ(_a, _b, `(___a, β)))>)) !(α))) = comp.g.type α β m then
        match infer f with
        | .ok ⟨(DCC? (Π(Id(Sort n), f_γ) Coup(f_β))), ⟨ht₂⟩⟩ =>
          if _heq₂ : (DCC? (Π(Id(Sort n), f_γ) Coup(f_β))) = comp.f.type f_β f_γ n then
            if heq₃ : f_β.reduce_all = (DCC? `(α, β)) then
              .ok ⟨_, ⟨.comp (heq ▸ ht₁) ht₂ (reduce_reduces heq₃) (reduce_reduces rfl) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
            else .error (.mismatch (DCC? `(α, β)) f_β.reduce_all f)
          else .error (.mismatch (comp.f.type f_β f_γ n) (DCC? (Π(Id(Sort n), f_γ) Coup(f_β))) f)
        | .ok ⟨t, _⟩ => .error (.unexpected t f)
        | .error ε => .error (.sub f ε)
      else .error (.mismatch (comp.g.type α β m) (DCC? (Π(Id(Sort m), `(_m, *<Σ(__a, Λ(_a, _b, `(___a, β)))>)) !(α))) g)
    | .ok ⟨t, _⟩ => .error (.unexpected t g)
    | .error ε => .error (.sub g ε)
  | DCC? (f ∘∘ g) =>
    match infer g with
    | .ok ⟨τ_g, ⟨ht₁⟩⟩ =>
      match τ_g.read_comp₂_g_type with
      | .some ⟨_α, β, _m, hg⟩ =>
        match infer f with
        | .ok ⟨(DCC? (Π(Id(Sort n), f_γ) _a)), ⟨ht₂⟩⟩ =>
          if heq₂ : (DCC? (Π(Id(Sort n), f_γ) _a)) = comp₂.f.type β f_γ n then
            .ok ⟨_, ⟨.comp₂ ht₁ hg (heq₂ ▸ ht₂) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
          else .error (.mismatch (comp₂.f.type β f_γ n) (DCC? (Π(Id(Sort n), f_γ) _a)) f)
        | .ok ⟨t, _⟩ => .error (.unexpected t f)
        | .error ε => .error (.sub f ε)
      | _ => .error (.unexpected τ_g g)
    | .error ε => .error (.sub g ε)
  | DCC? (f ∘' g) =>
    match infer g with
    | .ok ⟨(DCC? (Π(Id(Sort _m), f_β₀) α)), ⟨ht⟩⟩ =>
      match (DCC? (f_β₀ α)).reduce_all with
      | DCC? `(_α₀', β) =>
        if heq₀ : (DCC? (f_β₀ α)).reduce_all = (DCC? (`(α, β))) then
          match (infer f) with
          | .ok ⟨(DCC? (Π(f_β, _γ) x_β)), ⟨ht₂⟩⟩ =>
            if heq : (DCC? (f_β x_β)).reduce_all = β then
              .ok ⟨_, ⟨.comp' ht (reduce_reduces heq₀) ht₂ (reduce_reduces heq) (reduce_reduces rfl) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
            else .error (.mismatch β (DCC? (f_β x_β)).reduce_all f)
          | .ok ⟨t, _⟩ => .error (.unexpected t f)
          | .error ε => .error (.sub f ε)
        else .error (.mismatch (DCC? (`(α, β))) (DCC? (f_β₀ α)).reduce_all g)
      | other => .error (.unexpected other g)
    | .ok ⟨t, _⟩ => .error (.unexpected t g)
    | .error ε => .error (.sub g ε)
  | DCC? x = y =>
    match infer x with
    | .ok ⟨t_x, ⟨ht₁⟩⟩ =>
      match infer y with
      | .ok ⟨t_y, ⟨ht₂⟩⟩ =>
        if heq : t_x = t_y then
          .ok ⟨_, ⟨.eq ht₁ (heq ▸ ht₂)⟩⟩
        else .error (.mismatch t_x t_y y)
      | .error ε => .error (.sub y ε)
    | .error ε => .error (.sub x ε)
  | DCC? Eql(f_α) =>
    match infer f_α with
    | .ok ⟨τ, ⟨ht₁⟩⟩ =>
      match τ.read_arrow with
      | .some ⟨_δ, DCC? Sort _m, _o, h⟩ =>
        .ok ⟨_, ⟨.eql ht₁ h (reduce_reduces rfl)⟩⟩
      | _ => .error (.unexpected τ f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC? refl(f_α) =>
    match infer f_α with
    | .ok ⟨τ, ⟨ht₁⟩⟩ =>
      match τ.read_arrow with
      | .some ⟨_δ, DCC? Sort _m, _o, h⟩ =>
        .ok ⟨_, ⟨.refl ht₁ h (reduce_reduces rfl)⟩⟩
      | _ => .error (.unexpected τ f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC? Σ(f_α, f_β) =>
    match f_α.infer with
    | .ok ⟨τ_f_α, ⟨h₁⟩⟩ =>
      match τ_f_α.read_arrow with
      | .some ⟨δ, DCC? Sort _m, o, harr⟩ =>
        match infer f_β with
        | .ok ⟨τ_f_β, ⟨h₂⟩⟩ =>
          match τ_f_β.view_pi_f_β (reduce_all f_α) δ o with
          | .some ⟨_n, h₃⟩ =>
            .ok ⟨_, ⟨.sigma h₁ harr h₂ (reduce_reduces rfl) h₃ (reduce_reduces rfl)⟩⟩
          | _ => .error (.unexpected τ_f_β f_β)
        | .error ε => .error (.sub f_β ε)
      | _ => .error (.unexpected τ_f_α f_α)
    | .error ε => .error (.sub f_α ε)
  | DCC? ⟦β⟧(x, y) =>
    match infer x with
    | .ok ⟨α, ⟨ht₁⟩⟩ =>
      match infer y with
      | .ok ⟨βxm, ⟨ht₂⟩⟩ =>
        match β.infer with
        | .ok ⟨τ_β, ⟨h₃⟩⟩ =>
          match τ_β.read_arrow₁ α with
          | .some ⟨DCC? Sort _n, _m, harr⟩ =>
            if heq : reduce_all (DCC? (β x)) = βxm then
              .ok ⟨_, ⟨.mk ht₁ h₃ harr
                (reduce_reduces (B := βxm) heq) (heq ▸ ht₂) (reduce_reduces rfl)⟩⟩
            else .error (.mismatch (reduce_all (DCC? (β x))) βxm y)
          | _ => .error (.unexpected τ_β β)
        | .error ε => .error (.sub β ε)
      | .error ε => .error (.sub y ε)
    | .error ε => .error (.sub x ε)
  | DCC? Coup(β) =>
    match infer β with
    | .ok ⟨(DCC? (Π(Id(Sort _m), f_β) α)), ⟨ht⟩⟩ =>
      match (DCC? (f_β α)).reduce_all with
      | DCC? `(_α₂, Sort n) =>
        if heq : (DCC? (f_β α)).reduce_all = DCC? `(α, Sort n) then
          .ok ⟨_, ⟨.coup ht (reduce_reduces heq) (reduce_reduces rfl)⟩⟩
        else .error (.mismatch (DCC? `(α, Sort n)) (DCC? (f_β α)).reduce_all β)
      | other => .error (.unexpected other β)
    | .ok ⟨t, _⟩ => .error (.unexpected t β)
    | .error ε => .error (.sub β ε)
  | DCC? Fst(β) =>
    match (infer β) with
    | .ok ⟨τ_β, ⟨ht₁⟩⟩ =>
      match τ_β.read_arrow with
      | .some ⟨_α, DCC? Sort _n, _m, harr⟩ =>
        .ok ⟨_, ⟨.fstc ht₁ harr (reduce_reduces rfl)⟩⟩
      | _ => .error (.unexpected τ_β β)
    | .error ε => .error (.sub β ε)
  | DCC? Snd(β) =>
    match (infer β) with
    | .ok ⟨τ_β, ⟨ht₁⟩⟩ =>
      match τ_β.read_arrow with
      | .some ⟨_α, DCC? Sort _n, _m, harr⟩ =>
        .ok ⟨_, ⟨.sndc ht₁ harr (reduce_reduces rfl)⟩⟩
      | _ => .error (.unexpected τ_β β)
    | .error ε => .error (.sub β ε)
  | DCC? Λ(α, β, x) =>
    match α.infer with
    | .ok ⟨DCC? Sort _m, ⟨ht⟩⟩ =>
      match infer x with
      | .ok ⟨DCC? (Π(f_α, _γ) x_α), ⟨ht₂⟩⟩ =>
        if heq : reduce_all (DCC? (f_α x_α)) = reduce_all (DCC? Coup(β)) then
          .ok ⟨_, ⟨.curr
            ht
            ht₂
            (reduce_reduces heq.symm)
            (reduce_reduces rfl)
            (reduce_reduces rfl)
            (reduce_reduces rfl)
            (reduce_reduces rfl)⟩⟩
        else .error (.mismatch (reduce_all (DCC? Coup(β))) (reduce_all (DCC? (f_α x_α))) x)
      | .ok ⟨t, _⟩ => .error (.unexpected t x)
      | .error ε => .error (.sub x ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t α)
    | .error ε => .error (.sub α ε)
  | DCC? !Λ(α, β, x) =>
    match α.infer with
    | .ok ⟨DCC? Sort _m, ⟨ht⟩⟩ =>
      match infer x with
      | .ok ⟨DCC? (Π(f_α, _γ) x_α), ⟨ht₂⟩⟩ =>
        if heq : reduce_all (DCC? (f_α x_α)) = reduce_all (DCC? !(Coup(β))) then
          .ok ⟨_, ⟨.curr'
            ht
            ht₂
            (reduce_reduces heq.symm)
            (reduce_reduces rfl)
            (reduce_reduces rfl)
            (reduce_reduces rfl)
            (reduce_reduces rfl)⟩⟩
        else .error (.mismatch (reduce_all (DCC? !(Coup(β)))) (reduce_all (DCC? (f_α x_α))) x)
      | .ok ⟨t, _⟩ => .error (.mark 2 (.unexpected t x))
      | .error ε => .error (.sub x ε)
    | .ok ⟨t, _⟩ => .error (.mark 1 (.unexpected t α))
    | .error ε => .error (.sub α ε)
  | DCC? Eval(α, β, x) =>
    match infer x with
    | .ok ⟨DCC? (Π(f_α, f_β) env), ⟨ht₁⟩⟩ =>
      if heq : (DCC? (f_α env)).reduce_all = α.reduce_all then
        match heq₂ : (DCC? (f_β env)).reduce_all with
        | DCC? Π(β₂, _γ) =>
          if heq₃ : β₂ = β.reduce_all then
            match infer α with
            | .ok ⟨DCC? Sort _m, ⟨ht₂⟩⟩ =>
              match infer β with
              | .ok ⟨DCC? (Π(f_α₂, f_β₂) env₂), ⟨ht₃⟩⟩ =>
                if heq₄ : (DCC? (f_α₂ env₂)).reduce_all = α.reduce_all then
                  match heq₅ : (DCC? (f_β₂ env₂)).reduce_all with
                  | DCC? `(α₃, Sort _n) =>
                    if heq₆ : α₃ = α.reduce_all then
                      .ok ⟨_, ⟨.eval ht₁ (reduce_reduces rfl) (reduce_reduces rfl) (reduce_reduces heq)
                        (heq₃ ▸ (reduce_reduces heq₂))
                        ht₂ ht₃ (reduce_reduces heq₄) (reduce_reduces (heq₆ ▸ heq₅)) (reduce_reduces rfl)⟩⟩
                    else .error (.mismatch α α₃ β)
                  | other => .error (.unexpected other β)
                else .error (.mismatch α (DCC? (f_α₂ env₂)).reduce_all β)
              | .ok ⟨t, _⟩ => .error (.unexpected t β)
              | .error ε => .error (.sub β ε)
            | .ok ⟨t, _⟩ => .error (.unexpected t α)
            | .error ε => .error (.sub α ε)
          else .error (.mismatch β β₂ x)
        | other => .error (.unexpected other x)
      else .error (.mismatch α (DCC? (f_α env)).reduce_all x)
    | .ok ⟨t, _⟩ => .error (.unexpected t x)
    | .error ε => .error (.sub x ε)
  | DCC? `(β, x) =>
    match infer x with
    | .ok ⟨_α, ⟨ht₁⟩⟩ =>
      match infer β with
      | .ok ⟨DCC? Sort _n, ⟨ht₂⟩⟩ =>
        .ok ⟨_, ⟨.quot ht₁ ht₂ (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
      | .ok ⟨t, _⟩ => .error (.unexpected t β)
      | .error ε => .error (.sub β ε)
    | .error ε => .error (.sub x ε)
  | DCC? ⟦γ⟧⟨f, g⟩ =>
    match infer f with
    | .ok ⟨DCC? (Π(Id(Sort m), f_β) x_α), ⟨ht₁⟩⟩ =>
      match infer g with
      | .ok ⟨DCC? (Π(f_α₂, f_β₂) α), ⟨ht₂⟩⟩ =>
        let β := (DCC? (f_β x_α)).reduce_all
        match heqm : (DCC? (f_β₂ α)).reduce_all with
        | DCC? (Π(β₂, γ₂)) =>
          if heqa : x_α = (DCC? (f_α₂ α)).reduce_all then
            if heqb : β₂.reduce_all = β then
              if heq₂ : γ₂.reduce_all = γ.reduce_all then
                .ok ⟨_, ⟨.pair
                  ht₁
                  (reduce_reduces rfl)
                  ht₂
                  (reduce_reduces rfl)
                  (reduce_reduces heqm)
                  (reduce_reduces heq₂)
                  (reduce_reduces heqb)
                  (reduce_reduces heqa.symm)
                  (reduce_reduces rfl)⟩⟩
              else .error (.mismatch γ.reduce_all γ₂.reduce_all g)
            else .error (.mismatch β β₂.reduce_all g)
          else .error (.mismatch (DCC? (f_α₂ α)).reduce_all (DCC? (Id(Sort m) x_α)).reduce_all f)
        | other => .error (.unexpected other g)
      | .ok ⟨t, _⟩ => .error (.unexpected t g)
      | .error ε => .error (.sub g ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t f)
    | .error ε => .error (.sub f ε)
  | DCC? Π(f_α, f_β) =>
    match f_α.infer with
    | .ok ⟨τ_f_α, ⟨ht₁⟩⟩ =>
      match τ_f_α.read_arrow with
      | .some ⟨δ, DCC? Sort _m, o, harr⟩ =>
        match infer f_β with
        | .ok ⟨τ_f_β, ⟨ht₂⟩⟩ =>
          match τ_f_β.view_pi_f_β f_α.reduce_all δ o with
          | .some ⟨_n, h₂⟩ =>
            .ok ⟨_, ⟨.pi ht₁ harr ht₂ (reduce_reduces rfl) h₂ (reduce_reduces rfl)⟩⟩
          | _ => .error (.mark 4 (.unexpected τ_f_β f_β))
        | .error ε => .error (.mark 3 (.sub f_β ε))
      | _ => .error (.mark 2 (.unexpected τ_f_α f_α))
    | .error ε => .error (.mark 1 (.sub f_α ε))
  | DCC? (f x) =>
    match infer f with
    | .ok ⟨DCC? (Π(f_α, _f_β) x_α), ⟨ht₁⟩⟩ =>
      match infer x with
      | .ok ⟨τ₂', ⟨ht₂⟩⟩ =>
        match def_eq? (reduce_all (DCC? (f_α x_α))) τ₂' with
        | .ok ⟨h⟩ =>
          .ok ⟨_, ⟨.app ht₁ (reduce_reduces rfl) ht₂ h (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
        | .error ε => .error (.def_eq ε)
      | .error ε => .error (.sub x ε)
    | .ok ⟨t, _⟩ => .error (.unexpected t f)
    | .error ε => .error (.sub f ε)
  | .const c => .error (.unexpected (.const c) (.const c))

abbrev infer' {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr τ_c) : Except (TypeError e) (GenericExpr τ_c) := Sigma.fst <$> e.infer

end GenericExpr

abbrev Expr.infer' (e : Expr) : Except (TypeError e) Expr := Sigma.fst <$> e.infer
abbrev Expr.infer (e : Expr) : Except (TypeError e) ((t : GenericExpr Unit) × (PLift (GenericExpr.Judge e t))) := GenericExpr.infer e

@[dcc_force_reduce]
def Expr.reduce_all : Expr → Expr := (GenericExpr.red_eta' (τ_c := Unit)) ∘ GenericExpr.reduce' GenericExpr.RedAff
