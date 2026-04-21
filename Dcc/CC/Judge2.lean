import Dcc.CC.Ast
import Dcc.CC.Step2

/-
Fst(α, β)

β (α, x) : Sort n
-/
/-def fst.β.type (m n : Level) : Expr :=
  arrow (coup.type (DCC Sort m) (DCC Id(Sort m)) m.succ) (DCC (Sort n)) m.succ-/

def fst.f_β.type (α δ : Expr) (m n o : Level) : Expr :=
  (DCC (δ : Sort o) → ((α : Sort m) → Sort n))

def id.type (α : Expr) (m : Level) : Expr :=
  DCC (α : Sort m) → α

/-
Fst(β), what does β indicate?

need some way to fill in environment.
Fst(β) : ∀

Fst / Snd are supposed to work with couples.

I don't think we actually want to change Σ.

We just need some mechanism of CREATING Σ, but Σ itself does not necessarily depend on context.
-/

/-
f_β env : α → Sort n
Fst(f_β, env) : Σ(f_β, δ) → α
-/

def fst.type (α f_β env : Expr) (m n : Level) : Expr :=
  DCC ((Σ(f_β) env) : Sort (max m n)) → α

/-
f_β env : α → Sort n
Snd(f_β, env) : Π(Id(Sort max m n), Λ((f_β env) ∘ Fst(f_β, env)) (Σ(f_β) env)
-/
def snd.type (f_β env : Expr) (m n : Level) : Expr :=
  DCC (Π(Id(Sort (max m n)), `(Sort (max m n), (f_β env) ∘ Fst(f_β, env))) (Σ(f_β) env))

/-
Λ(β, x) y z → x ⟦β⟧(y, z)

β receives (α, x)

x : ∀ (s : coup.type α β m), γ s
-/
def curr.type (α β γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), Λ(Fstc(m.succ, Sort m, Id(Sort m)),
    Π(β, Λ(β, γ)))) α) -- weaken α, keep x

/-
β (α, y)
Λ(β, x) (y, z)

β : Coup(m.succ, Sort m, Id(Sort m))
-/
def curr.β.type (m n : Level) : Expr :=
  DCC (Coup(m.succ, Sort m, Id(Sort m)) : Sort m.succ) → Sort n

#eval Std.format <| curr.β.type 0 4

/-
Nondependent quotation.

x : α
`(β, x) : β → α
-/
def quot.type (α β : Expr) (n : Level) : Expr :=
  DCC (β : Sort n) → α

/-
f : ∀ (x : α), β x
g : ∀ (x : α), γ x

⟦β, γ⟧⟨f, g⟩ x : ⟦`((β x), (γ x))⟧((f x), (g x))

⟦β, γ⟧⟨f, g⟩ : (Π(Id(Sort m), `(Sort m, Σ(
  -- receive (x : α), then (f x)
  Λ(β ∘ Sndc(Sort m, Id(Sort m)), -- receive (α, x), make type of (f x) which is (β x)
     -- receive (x, (f x))
    γ ∘ Fstc(α, β))))) α)
-/
def pair.type (α β γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, Σ(
  -- receive (x : α), then (f x)
  Λ(β ∘ Snd'(Sort m, α), -- receive (α, x), make type of (f x) which is (β x)
     -- receive (x, (f x))
    γ ∘ Fstc(m, α, β))))) α)

def pair.β.type (α : Expr) (m n : Level) : Expr :=
  (DCC (Sort m : Sort m.succ) → ((α : Sort m) → Sort n))

def comp.type (α β γ g : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, (γ β) ∘ g)) α)

/-
f : ∀ (x : α), β x
App(β) : ∀ (s : Σ(`(Π(m, Id(Sort m), β), α))), (β α) ∘ Snd'(Π(m, Id(Sort m), β), β)
-/
def App.type (α β : Expr) (m n : Level) : Expr :=
  DCC (Π(Id(Sort (max m n)),
    `(Sort (max m n), (Λ(Fstc(m.succ, Sort m, Id(Sort m)), β) α)
      ∘ Snd'((Π(Id(Sort m), Λ(Fstc(m.succ, Sort m, Id(Sort m)), β)) α), α)))
    Σ(`((Π(Id(Sort m), Λ(Fstc(m.succ, Sort m, Id(Sort m)), β)) α), α)))

def snd'.type (α β : Expr) (m n : Level) : Expr :=
  DCC (Σ(`(α, β)) : Sort max m n) → β

/-
f_α : α → Sort m
f_β : (x : α) (y : f_α x) → Sort n
Π(m, f_α, f_β) : α → Sort n
-/
def Pi.type (α : Expr) (m o : Level) : Expr :=
  DCC (α : Sort m) → Sort o

/-
Σ(f_β)

f_β : δ → α → Sort n

Σ(f_β) : δ → Sort n
-/
def Sigma.type (δ : Expr) (m n o : Level) : Expr :=
  DCC (δ : Sort o) → Sort max m n

namespace Expr

inductive Reduces : Expr → Expr → Prop
  | mk : RedAffReflTrans A B → IsNormAff B → Reduces A B

@[simp] theorem Reduces.unique : Reduces A B → Reduces A C → B = C := fun ⟨a, b⟩ ⟨c, d⟩ =>
  a.norm_unique b c d

@[simp] theorem Reduces.unique' (h₁ : Reduces A B) (h₂ : Reduces A C) : h₁ ≍ h₂ := by
  have h := h₁.unique h₂
  cases h
  congr

@[simp] theorem Reduces.complete : Reduces A B → reduce A = B :=
  fun ⟨ha, hb⟩ => ha.complete hb

def reduce_reduces (h : reduce A = B) : Reduces A B := ⟨reduce_sound h, reduce_norm h⟩

def reduce_reduces' : Reduces A A.reduce := reduce_reduces rfl

@[inline] abbrev arrow.matcher (t : Expr) : Option ((α β : Expr) × (m : Level) × PLift (t = (DCC (α : Sort m) → β))) :=
  match heq₀ : t with
  | DCC (Π(Id(Sort m), Λ(_π, `(_t_β, β))) α) =>
    if heq₁ : t = (DCC (α : Sort m) → β) then
      .some ⟨α, β, m, ⟨by simp_all⟩⟩
    else
      .none
  | _ => .none

@[inline] abbrev fst.f_β.type.matcher (t : Expr) : Option ((α δ : Expr) × (m n o : Level) × (PLift (t = fst.f_β.type α δ m n o))) :=
  match arrow.matcher t with
  | .some ⟨δ, arr', o, ⟨h_arr⟩⟩ =>
    match arrow.matcher arr' with
    | .some ⟨α, DCC Sort n, m, ⟨h_arr₂⟩⟩ =>
      .some ⟨α, δ, m, n, o, ⟨by rw [h_arr, h_arr₂]; rfl⟩⟩
    | _ => .none
  | _ => .none

@[inline] abbrev pair.β.type.matcher (t : Expr) : Option ((α : Expr) × (m n : Level) × (PLift (t = pair.β.type α m n))) :=
  match arrow.matcher t with
  | .some ⟨DCC Sort m, arr', m₂, ⟨h_arr⟩⟩ =>
    match arrow.matcher arr' with
    | .some ⟨α, DCC Sort n, m₃, ⟨h_arr₂⟩⟩ =>
      if heq : m₂ = m.succ ∧ m₃ = m then
        have ⟨h₁, h₂⟩ := heq
        .some ⟨α, m, n, ⟨by rw [h_arr, h_arr₂, h₁, h₂]; rfl⟩⟩
      else .none
    | _ => .none
  | _ => .none

@[inline] abbrev curr.β.type.matcher (t : Expr) : Option
  ((m n : Level) × (PLift (t = curr.β.type m n))) :=
  match heq₀ : t with
  | DCC (Π(f_α, Λ(_a, `(_b, Sort n))) (_c Sort m)) =>
    if heq : t = curr.β.type m n then
      .some ⟨m, n, ⟨by simp_all⟩⟩
    else .none
  | _ => .none

def Coup.matcher (e : Expr) : Option ((m : Level) × (α β : Expr) × (PLift (e = DCC Coup(m, α, β)))) :=
  match heq₀ : e with
  | DCC (Σ(Λ(Fst(`(Sort m, `(_b, α)), _c), β)) _d) =>
    if heq : e = DCC Coup(m, α, β) then
      .some ⟨m, α, β, ⟨by simp_all⟩⟩
    else .none
  | _ => .none

def coup.β_x (α β x : Expr) (m : Level) :=
  (DCC (β ⟦Sndc(m.succ.succ, Sort m.succ, Id(Sort m.succ))⟧(α, x)))

inductive Judge : Expr → Expr → Prop where
  | id   : Judge α (DCC Sort m)
    → Reduces (id.type α m) τ
    → Judge (DCC Id(α)) τ
  | comp : Judge g (arrow α β m)
    → Judge f (DCC (Π(Id(Sort n), γ) β))
    → Reduces (comp.type α β γ g m) τ
    → Judge (DCC f ∘ g) τ
  /-
    f_β δ : α → Sort n
    Fst(f_β, δ) : Σ(f_β) δ → α
  -/
  | fst  : Judge env δ
    → Judge f_β (fst.f_β.type α δ m n o)
    → Reduces (fst.type α f_β env m n) τ
    → Judge (DCC Fst(f_β, env)) τ
  /-
    f_β δ : α → Sort n
    Snd(f_β, δ) : ∀ (s : Σ(f_β) δ), f_β δ ∘ Fst
  -/
  | snd   : Judge env δ
    → Judge f_β (fst.f_β.type α δ m n o)
    → Reduces (snd.type f_β env m n) τ
    → Judge (DCC Snd(f_β, env)) τ
  | sigma : Judge f_β (fst.f_β.type α δ m n o)
    → Reduces (Sigma.type δ m n o) τ
    → Judge (DCC Σ(f_β)) τ
  | snd' : Judge α (DCC Sort m)
    → Judge β (DCC Sort n)
    → Reduces (snd'.type α β m n) τ
    → Judge (DCC Snd'(α, β)) τ
  | coup : Judge x α
    → Judge y τ₂
    → Judge β (curr.β.type m n)
    → Reduces (coup.β_x α β x m) τ₂
    → Reduces (coup.type α β m) τ
    → Judge (DCC ⟦β⟧(x, y)) τ
  | curr : Judge β (curr.β.type m n)
    → Judge x (DCC (Π(f_α, γ) x_α))
    → Reduces (DCC (f_α x_α)) (DCC Coup(m, α, β))
    → Reduces (curr.type α β (DCC (γ x_α)) m) τ
    → Judge (DCC Λ(β, x)) τ
  | quot : Judge x α
    → Judge β (DCC Sort n)
    → Reduces (quot.type α β n) τ
    → Judge (DCC `(β, x)) τ
  | pair : Judge f (DCC (Π(Id(Sort m), β) α))
    → Judge g (DCC (Π(Id(Sort m), γ) α))
    → Judge β (pair.β.type α m n)
    → Judge γ (pair.β.type α m o)
    → Reduces (pair.type α β γ m) τ
    → Judge (DCC ⟦n, o, α, β, γ⟧⟨f, g⟩) τ
  | appl : Judge α (DCC Sort m)
    → Judge β (arrow (DCC Σ(Id(Sort m))) (DCC Sort n) m.succ)
    → Reduces (App.type α β m n) τ
    → Judge (DCC App(α, β)) τ
  /-
    ef_α : α → Sort m
    f_β : ∀ (x : α) (y : f_α x), Sort n
    Π(f_α, f_β)
  -/
  | pi   : Judge f_α (arrow α (DCC Sort n) m)
    → Judge f_β (DCC (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(f_α, (Λ(Id(Sort m), `(Σ(Id(Sort m)), Sort o)) Σ(f_α)))))) α))
    → Reduces (Pi.type α m o) τ
    → Judge (DCC Π(f_α, f_β)) τ
  | sort : Judge (DCC Sort m) (DCC Sort m.succ)
  | app  : Judge f (DCC (Π(f_α, f_β) x_α))
    → Reduces (DCC (f_α x_α)) α
    → Judge x α
    → Reduces (DCC (f_β x_α x)) τ
    → Judge (DCC (f x)) τ

def with_red (h : Option ((t : Expr) × PLift (Judge e t))) :
  Option ((τ₁ τ₂ : Expr) × PLift (Judge e τ₁) × PLift (Reduces τ₁ τ₂)) :=
  match h with
  | .some ⟨t, h⟩ => .some ⟨t, t.reduce, h, ⟨reduce_reduces rfl⟩⟩
  | _ => .none

def with_arr (h : Option ((t : Expr) × PLift (Judge e t))) :
  Option ((τ α β : Expr) × (m : Level) × PLift (Judge e τ) × PLift (τ = arrow α β m)) :=
    match h with
    | .some ⟨t, h⟩ => match arrow.matcher t with
      | .some ⟨α, β, m, h_arr⟩ => .some ⟨t, α, β, m, h, h_arr⟩
      | _ => .none
    | _ => .none

#eval Std.format <| DCC Coup(0, Sort 10, Sort 20)

def with_fst_fβ_type (h : Option ((t : Expr) × PLift (Judge e t))) :
  Option ((τ α δ : Expr) × (m n o : Level) × PLift (Judge e τ) × (PLift (τ = fst.f_β.type α δ m n o))) :=
  match h with
  | .some ⟨t, h⟩ => match fst.f_β.type.matcher t with
    | .some ⟨α, δ, m, n, o, h₂⟩ => .some ⟨t, α, δ, m, n, o, h, h₂⟩
    | _ => .none
  | _ => none

def with_pair_β_type (h : Option ((t : Expr) × PLift (Judge e t))) :
  Option ((τ α : Expr) × (m n : Level) × PLift (Judge e τ) × (PLift (τ = pair.β.type α m n))) :=
  match h with
  | .some ⟨t, h⟩ => match pair.β.type.matcher t with
    | .some ⟨α, m, n, h₂⟩ => .some ⟨t, α, m, n, h, h₂⟩
    | _ => .none
  | _ => .none

def with_curr_β_type (h : Option ((t : Expr) × PLift (Judge e t))) :
  Option ((τ : Expr) × (m n : Level) × PLift (Judge e τ) × (PLift (τ = curr.β.type m n))) :=
  match h with
  | .some ⟨t, h⟩ => match curr.β.type.matcher t with
    | .some ⟨m, n, h₂⟩ => .some ⟨t, m, n, h, h₂⟩
    | _ => .none
  | _ => none

def infer (e : Expr) : Option ((t : Expr) × PLift (Judge e t)) :=
  match e with
  | DCC Sort _m => .some ⟨_, ⟨.sort⟩⟩
  | DCC (Id(α)) =>
    match infer α with
    | .some ⟨DCC Sort _m, ⟨ht⟩⟩ => .some ⟨_, ⟨.id ht (reduce_reduces rfl)⟩⟩
    | _ => .none
  | DCC (f ∘ g) =>
    match with_arr (infer g) with
    | .some ⟨_, _α, β, _m, ⟨ht₁⟩, ⟨harr₁⟩⟩ =>
      match (infer f) with
      | .some ⟨(DCC (Π(Id(Sort _n₂), _γ) β₂)), ⟨ht₂⟩⟩ =>
        if heq : β₂ = β then
          .some ⟨_, ⟨.comp (harr₁ ▸ ht₁) (heq ▸ ht₂) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Fst(f_β, env) =>
    match infer env with
    | .some ⟨δ, ⟨ht₁⟩⟩ =>
      match with_fst_fβ_type (infer f_β) with
      | .some ⟨_τ₁, _α, δ₂, m, n, o, ⟨ht₂⟩, ⟨harr⟩⟩ =>
        if heq : δ = δ₂ then
          .some ⟨_, ⟨.fst ht₁ (heq ▸ harr ▸ ht₂) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Snd(f_β, env) =>
    match infer env with
    | .some ⟨δ, ⟨ht₁⟩⟩ =>
      match with_fst_fβ_type (infer f_β) with
      | .some ⟨_τ₁, _α, δ₂, m, n, o, ⟨ht₂⟩, ⟨harr⟩⟩ =>
        if heq : δ = δ₂ then
          .some ⟨_, ⟨.snd ht₁ (heq ▸ harr ▸ ht₂) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Σ(β) =>
    match with_fst_fβ_type (infer β) with
    | .some ⟨_τ₁, _α, _δ, _m, _n, _o, ⟨ht⟩, ⟨harr⟩⟩ =>
      .some ⟨_, ⟨.sigma (harr ▸ ht) (reduce_reduces rfl)⟩⟩
    | _ => .none
  | DCC Snd'(α, β) =>
    match infer α with
    | .some ⟨DCC Sort _m, ⟨ht₁⟩⟩ =>
      match (infer β) with
      | .some ⟨DCC Sort _n, ⟨ht₂⟩⟩ =>
        .some ⟨_, ⟨.snd' ht₁ ht₂ (reduce_reduces rfl)⟩⟩
      | _ => .none
    | _ => .none
  | DCC ⟦β⟧(x, y) =>
    match infer x with
    | .some ⟨α, ⟨ht₁⟩⟩ =>
      match infer y with
      | .some ⟨βxm, ⟨ht₂⟩⟩ =>
        match with_curr_β_type (infer β) with
        | .some ⟨_, m, n, ⟨ht₃⟩, ⟨harr⟩⟩ =>
          if heq : (reduce (coup.β_x α β x m)) = βxm then
            .some ⟨_, ⟨.coup ht₁ ht₂ (harr ▸ ht₃) (reduce_reduces heq) (reduce_reduces rfl)⟩⟩
          else .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC Λ(β, x) =>
    match with_curr_β_type (infer β) with
    | .some ⟨_τ₁, m, n, ⟨ht₁⟩, ⟨harr₁⟩⟩ =>
      match infer x with
      | .some ⟨DCC (Π(f_α, _γ) x_α), ⟨ht₂⟩⟩ =>
        match Coup.matcher (reduce (DCC (f_α x_α))) with
        | .some ⟨m₂, α, β₂, ⟨heq⟩⟩ =>
          if heq₂ : β = β₂ ∧ m = m₂ then
            have ⟨h₁, h₂⟩ := heq₂
            .some ⟨_, ⟨.curr (harr₁ ▸ ht₁) ht₂ (reduce_reduces (h₂ ▸ h₁ ▸ heq))
              (reduce_reduces rfl)⟩⟩
          else .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC `(β, x) =>
    match infer x, infer β with
    | .some ⟨_α, ⟨ht₁⟩⟩, .some ⟨DCC Sort _n, ⟨ht₂⟩⟩ =>
      .some ⟨_, ⟨.quot ht₁ ht₂ (reduce_reduces rfl)⟩⟩
    | _, _ => .none
  | DCC ⟦n, o, α, β, γ⟧⟨f, g⟩ =>
    match infer f, infer g with
    | .some ⟨DCC (Π(Id(Sort m), β₂) α₁), ⟨ht₁⟩⟩, .some ⟨DCC (Π(Id(Sort m₂), γ₂) α₂), ⟨ht₂⟩⟩ =>
      match with_pair_β_type (infer β), with_pair_β_type (infer γ) with
      | .some ⟨_, α₃, m₃, n₂, ⟨ht₃⟩, ⟨harr₁⟩⟩, .some ⟨_, α₄, m₄, o₂, ⟨ht₄⟩, ⟨harr₂⟩⟩ =>
        if heq : α = α₁ ∧ β = β₂ ∧ α = α₂ ∧ γ = γ₂ ∧ α = α₃ ∧ α = α₄ ∧ m = m₂ ∧ m = m₃ ∧ m = m₄ ∧ n = n₂ ∧ o = o₂ ∧ α = α₃ ∧ α = α₄ then
          have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h10, h11, h12, h13⟩ := heq
          .some ⟨_, ⟨.pair
            (h₂ ▸ h₁ ▸ ht₁)
            (by rw [← h₃, ← h₇, ← h₄] at ht₂; exact ht₂)
            (by rw [← h10, ← h₈, ← h12] at harr₁; rw [← harr₁]; exact ht₃)
            (by rw [← h13, ← h₉, ← h11] at harr₂; rw [← harr₂]; exact ht₄)
            (reduce_reduces rfl)⟩⟩
        else .none
      | _, _ => .none
    | _, _ => .none
  | DCC App(α, β) =>
      match infer α, with_arr (infer β) with
      | .some ⟨(DCC Sort m), ⟨ht₁⟩⟩,
        .some ⟨_τ₁, DCC Σ(Id(Sort m₂)), DCC Sort _n, m₃, ⟨ht⟩, ⟨harr⟩⟩ =>
          if heq : m₂ = m ∧ m.succ = m₃ then
            have ⟨h₁, h₂⟩ := heq
            .some ⟨_, ⟨.appl ht₁ (h₁ ▸ h₂ ▸ harr ▸ ht)
              (reduce_reduces rfl)⟩⟩
          else .none
      | _, _ => .none
  | DCC Π(f_α, f_β) =>
    match with_arr (infer f_α), infer f_β with
    | .some ⟨_τ₁, α, DCC Sort _n, m, ⟨ht₁⟩, ⟨harr⟩⟩,
      .some ⟨(DCC (Π(Id(Sort m₂), `(Sort m₃, Π(f_α₂, Λ(f_α₃, (Λ(Id(Sort m₄), `(Σ(Id(Sort m₅)), Sort _o)) Σ(f_α₄)))))) α₂)), ⟨ht₂⟩⟩ =>
      if heq : α₂ = α ∧ f_α₂ = f_α ∧ f_α₃ = f_α ∧ f_α₄ = f_α ∧ m₂ = m ∧ m₃ = m ∧ m₄ = m ∧ m₅ = m then
        have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := heq
        .some ⟨_, ⟨.pi (harr ▸ ht₁) (h₈ ▸ h₇ ▸ h₆ ▸ h₅ ▸ h₄ ▸ h₃ ▸ h₂ ▸ h₁ ▸ ht₂) (reduce_reduces rfl)⟩⟩
      else .none
    | _, _ => .none
  | DCC (f x) =>
    match infer f, infer x with
    | .some ⟨DCC (Π(f_α, _f_β) x_α), ⟨ht₁⟩⟩, .some ⟨τ₂', ⟨ht₂⟩⟩ =>
      if heq : (reduce (DCC (f_α x_α))) = τ₂' then
        .some ⟨_, ⟨.app ht₁ (reduce_reduces rfl) (heq ▸ ht₂) (reduce_reduces rfl)⟩⟩
      else .none
    | _, _ => .none

end Expr
