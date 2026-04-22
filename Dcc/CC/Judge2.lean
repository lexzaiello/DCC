import Dcc.CC.Ast
import Dcc.CC.Step2

/-
Need to retain nice properties for pair. (α, x)

but need to reduce amount of (α, x).
we could instead feed β α and then x.

probably makes more sense, but might not even be necessary.

couples just receive x, not (α, x).
-/

def fst.f_β.type (α δ : Expr) (m n o : Level) : Expr :=
  (DCC (δ : Sort o) → ((α : Sort m) → Sort n))

def id.type (α : Expr) (m : Level) : Expr :=
  DCC (α : Sort m) → α

/-
f_β : δ → α → Sort n
Fst(f_β) : ∀ (env : δ) (s : Σ(f_β) env), α
-/

def fst.type (α f_β δ : Expr) (o : Level) : Expr :=
  DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(Σ(f_β), Λ(δ, Σ(f_β), `(Coup(Σ(f_β)), α))) ∘ Snd'(Sort o, δ))) δ) 

/-
Snd(f_β) : ∀ (env : δ) (s : Σ(f_β) env), f_β env (Fst(f_β) env s)
-/

def snd.type (f_β δ : Expr) (o : Level) : Expr :=
  DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(Σ(f_β), Subst(f_β, Fst(f_β))) ∘ Snd'(Sort o, δ))) δ) 


/-
Λ(β, x) y z → x ⟦β⟧(y, z)

β receives x

x : ∀ (s : coup.type α β m), γ s
-/
def curr.type (α β γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, Π(β, Λ(α, β, γ)))) α) -- weaken α, keep x

/-
β : α → Sort n
-/
def curr.β.type (α : Expr) (m n : Level) : Expr :=
  DCC (α : Sort m) → Sort n

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
    Λ(α, (Λ(Sort m, Id(Sort m), β) α), (Λ(Sort m, Id(Sort m), γ) α) ∘ Fstc((Λ(Sort m, Id(Sort m), β) α)))))) α)

def comp.type (α β γ g : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, (γ β) ∘ g)) α)

/-
Alternative App encoding.

f_α and env determine α and

we want to make basically a couple

f_α env indicates α
and f_β env indicates

f element : (Π(Id(Sort m), Λ(Sort m, Id(Sort m), (f_β env))) (f_α env))
g element : (f_α env)
Σ(
-/

def App.type (f_α f_β δ : Expr) (o : Level) : Expr :=
  let f_β_sig := DCC Λ(δ, Π(f_α, f_β), f_α ∘ Fstc(Π(f_α, f_β)))
  DCC (Π(Id(Sort o), `(Sort o, Π(Σ(f_β_sig), Subst(f_β, Snd(f_β_sig))))) δ)

def snd'.type (α β : Expr) (m n : Level) : Expr :=
  DCC (Coup(`(α, β)) : Sort max m n) → β

/-
f_α : α → Sort m
f_β : (x : α) (y : f_α x) → Sort n
Π(m, f_α, f_β) : α → Sort n
-/
def Pi.type (α : Expr) (m o : Level) : Expr :=
  DCC (α : Sort m) → Sort o

def Pi.f_β.type (f_α α : Expr) (m o : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(α, f_α, (Λ(Sort m, Id(Sort m),
    `(Coup(Id(Sort m)), Sort o)) Coup(f_α)))))) α))

/-def Pi.f_β.type (f_α α : Expr) (m o : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(α, f_α, `(Coup(m, α, f_α), Sort o))))) α))-/

def pair.β.type (m n : Level) : Expr :=
  DCC (Coup(Id(Sort m)) : Sort m.succ) → Sort n

/-
β : δ → α → Sort n
x : ∀ (env : δ) (x : α), γ env x
Subst(x, Fst(β)) : ∀ 
-/
def Subst₁.type (β γ δ : Expr) (o : Level) : Expr :=
  (DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(Σ(β), Subst(γ, Fst(β))) ∘ Snd'(Sort o, δ))) δ))

/-
Subst(x, Snd(β₀)) env (y, z) = x env y z
-/
def Subst₂.type (β γ δ : Expr) (o : Level) : Expr :=
  (DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(Σ(β), Subst(γ, Snd(β))) ∘ Snd'(Sort o, δ))) δ))

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

@[simp, aesop safe destruct, aesop safe apply] theorem Reduces.complete : Reduces A B → reduce A = B :=
  fun ⟨ha, hb⟩ => ha.complete hb

def reduce_reduces (h : reduce A = B) : Reduces A B := ⟨reduce_sound h, reduce_norm h⟩

def reduce_reduces' : Reduces A A.reduce := reduce_reduces rfl

@[inline] abbrev arrow.matcher (t : Expr) : Option ((α β : Expr) × (m : Level) × PLift (t = (DCC (α : Sort m) → β))) :=
  match heq₀ : t with
  | DCC (Π(Id(Sort m), Λ(_a, _b, `(_e, β))) α) =>
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

@[inline] abbrev pair.β.type.matcher (t : Expr) : Option ((m n : Level) × (PLift (t = pair.β.type m n))) :=
  match t with
  | DCC (Π(_a, Λ(_b, _c, `(_d, Sort n))) (_e Sort m)) =>
    if heq : DCC (Π(_a, Λ(_b, _c, `(_d, Sort n))) (_e Sort m)) = pair.β.type m n then
      .some ⟨m, n, ⟨by rw [heq]⟩⟩
    else .none
  | _ => .none

@[inline] abbrev curr.β.type.matcher (t : Expr) : Option
  ((α : Expr) × (m n : Level) × (PLift (t = curr.β.type α m n))) :=
  match arrow.matcher t with
  | .some ⟨α, DCC Sort n, m, ⟨h_arr⟩⟩ =>
    .some ⟨α, m, n, ⟨by rw [h_arr]; rfl⟩⟩
  | _ => .none

inductive Judge : Expr → Expr → Prop where
  | id     : Judge α (DCC Sort m)
    → Reduces (id.type α m) τ
    → Judge (DCC Id(α)) τ
  | comp   : Judge g (arrow α β m)
    → Judge f (DCC (Π(Id(Sort n), γ) β))
    → Reduces (comp.type α β γ g m) τ
    → Judge (DCC f ∘ g) τ
  /-
    f_β δ : α → Sort n
    Fst(f_β, δ) : Σ(f_β) δ → α
  -/
  | fst    : Judge f_β (fst.f_β.type α δ m n o)
    → Reduces (fst.type α f_β δ o) τ
    → Judge (DCC Fst(f_β)) τ
  /-
    f_β δ : α → Sort n
    Snd(f_β, δ) : ∀ (s : Σ(f_β) δ), f_β δ ∘ Fst
  -/
  | snd    : Judge f_β (fst.f_β.type α δ m n o)
    → Reduces (snd.type f_β δ o) τ
    → Judge (DCC Snd(f_β)) τ
  | sigma   : Judge f_β (fst.f_β.type α δ m n o)
    → Reduces (Sigma.type δ m n o) τ
    → Judge (DCC Σ(f_β)) τ
  | snd'   : Judge α (DCC Sort m)
    → Judge β (DCC Sort n)
    → Reduces (snd'.type α β m n) τ
    → Judge (DCC Snd'(α, β)) τ
  | coup   : Judge x α
    → Judge y τ₂
    → Judge β (curr.β.type α m n)
    → Reduces (DCC (β x)) τ₂
    → Reduces (coup.type β) τ
    → Judge (DCC ⟦β⟧(x, y)) τ
  /-
    Λ(β, x)
    β receives (α, x)
    β : Coup(Sort m, Id(Sort m)) → Sort n
  -/
  | curr   : Judge β (curr.β.type α m n)
    → Judge x (DCC (Π(f_α, γ) x_α))
    → Reduces (DCC Coup(β)) τα
    → Reduces (DCC (f_α x_α)) τα
    → Reduces (curr.type α β (DCC (γ x_α)) m) τ
    → Judge (DCC Λ(α, β, x)) τ
  | quot   : Judge x α
    → Judge β (DCC Sort n)
    → Reduces (quot.type α β n) τ
    → Judge (DCC `(β, x)) τ
  | pair   : Judge f (DCC (Π(Id(Sort m), Λ(Sort m, Id(Sort m), β)) α))
    → Judge g (DCC (Π(Id(Sort m), Λ(Sort m, Id(Sort m), γ)) α))
    → Judge β (pair.β.type m n)
    → Judge γ (pair.β.type m o)
    → Reduces (pair.type α β γ m) τ
    → Judge (DCC ⟦m, α, β, γ⟧⟨f, g⟩) τ
  | subst₁ : Judge x (DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(`(δ, α), γ)) ∘ Snd'(Sort o, δ)) δ))
    → Reduces (Subst₁.type β γ δ o) τ
    → Judge (DCC Subst(x, Fst(β))) τ
  | appl   : Judge f_α (arrow δ (DCC Sort m) o)
    → Judge f_β (Pi.f_β.type f_α δ o n)
    → Reduces (App.type f_α f_β δ o) τ
    → Judge (DCC App(f_α, f_β)) τ
  /-
    ef_α : α → Sort m
    f_β : ∀ (x : α) (y : f_α x), Sort n
    Π(f_α, f_β)
  -/
  | pi     : Judge f_α (arrow α (DCC Sort n) m)
    → Judge f_β (Pi.f_β.type f_α α m o)
    → Reduces (Pi.type α m o) τ
    → Judge (DCC Π(f_α, f_β)) τ
  | sort   : Judge (DCC Sort m) (DCC Sort m.succ)
  | app    : Judge f (DCC (Π(f_α, f_β) x_α))
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

def with_fst_fβ_type (h : Option ((t : Expr) × PLift (Judge e t))) :
  Option ((τ α δ : Expr) × (m n o : Level) × PLift (Judge e τ) × (PLift (τ = fst.f_β.type α δ m n o))) :=
  match h with
  | .some ⟨t, h⟩ => match fst.f_β.type.matcher t with
    | .some ⟨α, δ, m, n, o, h₂⟩ => .some ⟨t, α, δ, m, n, o, h, h₂⟩
    | _ => .none
  | _ => none

def with_pair_β_type (h : Option ((t : Expr) × PLift (Judge e t))) :
  Option ((τ : Expr) × (m n : Level) × PLift (Judge e τ) × (PLift (τ = pair.β.type m n))) :=
  match h with
  | .some ⟨t, h⟩ => match pair.β.type.matcher t with
    | .some ⟨m, n, h₂⟩ => .some ⟨t, m, n, h, h₂⟩
    | _ => .none
  | _ => .none

def with_curr_β_type (h : Option ((t : Expr) × PLift (Judge e t))) :
  Option ((τ : Expr) × (α : Expr) × (m n : Level) × PLift (Judge e τ) × (PLift (τ = curr.β.type α m n))) :=
  match h with
  | .some ⟨t, h⟩ => match curr.β.type.matcher t with
    | .some ⟨α, m, n, h₂⟩ => .some ⟨t, α, m, n, h, h₂⟩
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
  | DCC Fst(f_β) =>
     match with_fst_fβ_type (infer f_β) with
     | .some ⟨_τ₁, _α, δ₂, m, n, o, ⟨ht₂⟩, ⟨harr⟩⟩ =>
       .some ⟨_, ⟨.fst (harr ▸ ht₂) (reduce_reduces rfl)⟩⟩
     | _ => .none
  | DCC Snd(f_β) =>
     match with_fst_fβ_type (infer f_β) with
     | .some ⟨_τ₁, _α, δ₂, m, n, o, ⟨ht₂⟩, ⟨harr⟩⟩ =>
       .some ⟨_, ⟨.snd (harr ▸ ht₂) (reduce_reduces rfl)⟩⟩
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
        | .some ⟨_, α₂, m, n, ⟨ht₃⟩, ⟨harr⟩⟩ =>
          if heq : (reduce (DCC (β x))) = βxm then
            if heq₂ : α = α₂ then
              .some ⟨_, ⟨.coup ht₁ ht₂ (heq₂ ▸ harr ▸ ht₃) (reduce_reduces heq) (reduce_reduces rfl)⟩⟩
            else .none
          else .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC Λ(α, β, x) =>
    match with_curr_β_type (infer β) with
    | .some ⟨_, α₂, m, n, ⟨htβ⟩, ⟨harrβ⟩⟩ =>
      match infer x with
      | .some ⟨DCC (Π(f_α, _γ) x_α), ⟨ht₂⟩⟩ =>
        if heq : reduce (DCC (f_α x_α)) = reduce (DCC Coup(β)) then
          if heq₂ : α = α₂ then
            .some ⟨_, ⟨.curr (heq₂ ▸ harrβ ▸ htβ) ht₂ (reduce_reduces heq.symm)
              (reduce_reduces rfl)
              (reduce_reduces rfl)⟩⟩
          else .none
        else .none
      | _ => .none
    | _ => .none
  | DCC `(β, x) =>
    match infer x, infer β with
    | .some ⟨_α, ⟨ht₁⟩⟩, .some ⟨DCC Sort _n, ⟨ht₂⟩⟩ =>
      .some ⟨_, ⟨.quot ht₁ ht₂ (reduce_reduces rfl)⟩⟩
    | _, _ => .none
  | DCC ⟦m, α, β, γ⟧⟨f, g⟩ =>
    match infer f, infer g with
    | .some ⟨DCC (Π(Id(Sort m₀), Λ(Sort ma, Id(Sort mb), β₂)) α₁), ⟨ht₁⟩⟩, .some ⟨DCC (Π(Id(Sort m₂), Λ(Sort mc, Id(Sort md), γ₂)) α₂), ⟨ht₂⟩⟩ =>
      match with_pair_β_type (infer β), with_pair_β_type (infer γ) with
      | .some ⟨_, m₃, n, ⟨ht₃⟩, ⟨harr₁⟩⟩, .some ⟨_, m₄, o, ⟨ht₄⟩, ⟨harr₂⟩⟩ =>
        if heq : α = α₂ ∧ β = β₂ ∧ γ = γ₂ ∧ m = m₂ ∧ m = m₃ ∧ m = m₄ ∧ m = ma ∧ m = mb ∧ m = mc ∧ m = md ∧ m = m₀ ∧ α = α₁ then
          have ⟨h₁, h₂, h₄, h₅, h₆, h₇, h₈, h₉, h12, h13, h14, h15⟩ := heq
          .some ⟨_, ⟨.pair
            (by rw [← h14, ← h15, ← h₈, ← h₉, ← h₂] at ht₁; exact ht₁)
            (by rw [← h₁, ← h₄, ← h13, ← h12, ← h₅] at ht₂; exact ht₂)
            (by rw [← h₆] at harr₁; rw [← harr₁]; exact ht₃)
            (by rw [← h₇] at harr₂; rw [← harr₂]; exact ht₄)
            (reduce_reduces rfl)⟩⟩
        else .none
      | _, _ => .none
    | _, _ => .none
  | DCC Subst(x, Fst(β)) =>
    match infer x with
    | .some ⟨(DCC (Π(Id(Sort o), Λ(Sort o₂, Id(Sort o₃), Π(`(δ, α), γ)) ∘ Snd'(Sort o₄, δ₂)) δ₃)), ⟨ht⟩⟩ =>
      if heq : o₂ = o ∧ o₃ = o ∧ o₄ = o ∧ δ₂ = δ ∧ δ₃ = δ then
        have ⟨ha, hb, hc, hd, he⟩ := heq
        .some ⟨_, ⟨.subst₁ (ha ▸ hb ▸ hc ▸ hd ▸ he ▸ ht) (reduce_reduces rfl)⟩⟩
      else .none
    | _ => .none
  | DCC App(f_α, f_β) =>
    match with_arr (infer f_α) with
    | .some ⟨_τ₁, δ, DCC Sort m, o, ⟨ht₁⟩, ⟨harr⟩⟩ =>
      match infer f_β with
      | .some ⟨(DCC (Π(_aa, `(_a, Π(_b, Λ(_c, _d, (Λ(_e, _f, `(_g, Sort n)) _h))))) _i)), ⟨ht₂⟩⟩ =>
        if heq : (DCC (Π(_aa, `(_a, Π(_b, Λ(_c, _d, (Λ(_e, _f, `(_g, Sort n)) _h))))) _i)) = Pi.f_β.type f_α δ o n then
          .some ⟨_, ⟨.appl (harr ▸ ht₁) (heq ▸ ht₂) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Π(f_α, f_β) =>
    match with_arr (infer f_α) with
    | .some ⟨_τ₁, α, DCC Sort _n, m, ⟨ht₁⟩, ⟨harr⟩⟩ =>
      match infer f_β with
      | .some ⟨(DCC (Π(_aa, `(_a, Π(_b, Λ(_c, _d, (Λ(_e, _f, `(_g, Sort o)) _h))))) _i)), ⟨ht₂⟩⟩ =>
        if heq : (DCC (Π(_aa, `(_a, Π(_b, Λ(_c, _d, (Λ(_e, _f, `(_g, Sort o)) _h))))) _i)) = Pi.f_β.type f_α α m o then
          .some ⟨_, ⟨.pi (harr ▸ ht₁) (heq ▸ ht₂) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC (f x) =>
    match infer f, infer x with
    | .some ⟨DCC (Π(f_α, _f_β) x_α), ⟨ht₁⟩⟩, .some ⟨τ₂', ⟨ht₂⟩⟩ =>
      if heq : (reduce (DCC (f_α x_α))) = τ₂' then
        .some ⟨_, ⟨.app ht₁ (reduce_reduces rfl) (heq ▸ ht₂) (reduce_reduces rfl)⟩⟩
      else .none
    | _, _ => .none
  | _ => .none

end Expr
