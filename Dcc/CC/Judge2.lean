import Dcc.CC.Ast
import Dcc.CC.Step2

/-
def arrow (α β : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), Λ(Id(Sort m), `(Σ(Id(Sort m)), β))) α)
-/

def arrow (α β : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), Λ(Id(Sort m), `(Σ(Id(Sort m)), β))) α)

/-def arrow (α β : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, `(α, β))) α)-/

def id.type (α : Expr) (m : Level) : Expr :=
  arrow α α m

def fst.type (α β : Expr) (m n : Level) : Expr :=
  arrow (DCC Σ(β)) α (max m n)

def snd.type (β : Expr) (m n : Level) : Expr :=
  DCC (Π(Id(Sort (max m n)), `(Sort (max m n), β ∘ Fst(β))) Σ(β))

def coup.type (β : Expr) : Expr :=
  DCC Σ(β)

/-
x : ∀ (s : Σ(β)), γ s
Λ(β, x) : ∀ (x : α) (y : β x), γ ⟦β⟧(x, y)
-/
def curr.type (α β γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, Π(β, Λ(β, γ)))) α) -- weaken α, keep x

/-
Nondependent quotation.

x : α
`(β, x) : β → α
-/
def quot.type (α β : Expr) (n : Level) : Expr :=
  arrow β α n

/-
f : ∀ (x : α), β x
g : ∀ (x : α), γ (f x)
⟨f, g⟩ : α → Σ(γ)
-/
def pair.type (α γ : Expr) (m : Level) : Expr :=
  arrow α (DCC Σ(γ)) m

/-
f ∘ g is tail-dependent composition. f is dependent, but g is not.

dependent composition can be derived, however, if g's codomain is Σ α, β

f ∘ g : ∀ (x : α), γ (g x)
-/
def comp.type (α β γ g : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, (γ β) ∘ g)) α)

/-
f : ∀ (x : α), β x
App(β) : ∀ (s : Σ(`(Π(m, Id(Sort m), β), α))), (β α) ∘ Snd'(Π(m, Id(Sort m), β), β)
-/
def App.type (α β : Expr) (m n : Level) : Expr :=
  DCC (Π(Id(Sort (max m n)), (β α) ∘ Snd'(Π(Id(Sort m), β), β)) Σ(`(Π(Id(Sort m), β), α)))

def snd'.type (α β : Expr) (m n : Level) : Expr :=
  arrow (DCC Σ(`(α, β))) β (max m n)

/-
f_α : α → Sort m
f_β : (x : α) (y : f_α x) → Sort n
Π(m, f_α, f_β) : α → Sort n
-/
def Pi.type (α : Expr) (m o : Level) : Expr :=
  arrow α (DCC Sort o) m

def Sigma.type (m n : Level) : Expr :=
  DCC (Sort (max m n))

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

@[inline] abbrev match_arrow (t : Expr) : Option ((α β : Expr) × (m : Level) × PLift (t = arrow α β m)) :=
  match t with
  | DCC (Π(Id(Sort m), Λ(Id(Sort m₂), `(Σ(Id(Sort m₃)), β))) α) =>
    if heq : m = m₂ ∧ m = m₃ then
      have ⟨h₁, h₂⟩ := heq
      .some ⟨α, β, m, ⟨by rw [← h₁, ← h₂]; rfl⟩⟩
    else
      .none
  | _ => .none

inductive Judge : Expr → Expr → Prop where
  | id   : Judge α (DCC Sort m)
    → Reduces (id.type α m) τ
    → Judge (DCC Id(α)) τ
  | comp : Judge g (arrow α β m)
    → Judge f (DCC (Π(Id(Sort n), γ) β))
    → Reduces (comp.type α β γ g m) τ
    → Judge (DCC f ∘ g) τ
  | fst  : Judge β (arrow α (DCC Sort n) m)
    → Reduces (fst.type α β m n) τ
    → Judge (DCC Fst(β)) τ
  | snd   : Judge β (arrow α (DCC Sort n) m)
    → Reduces (snd.type β m n) τ
    → Judge (DCC Snd(β)) τ
  | sigma : Judge β (arrow α (DCC Sort n) m)
    → Judge (DCC Σ(β)) (Sigma.type m n)
  | snd' : Judge α (DCC Sort m)
    → Judge β (DCC Sort n)
    → Reduces (snd'.type α β m n) τ
    → Judge (DCC Snd'(α, β)) τ
  | coup : Judge x α
    → Judge y τ₂
    → Judge β (arrow α (DCC Sort n) m)
    → Reduces (DCC (β x)) τ₂
    → Reduces (coup.type β) τ
    → Judge (DCC ⟦β⟧(x, y)) τ
  | curr : Judge β (arrow α (DCC Sort n) m)
    → Judge x (DCC (Π(f_α, γ) x_α))
    → Reduces (DCC (f_α x_α)) (DCC Σ(β))
    → Reduces (curr.type α β (DCC (γ x_α)) m) τ
    → Judge (DCC Λ(β, x)) τ
  | quot : Judge x α
    → Judge β (DCC Sort n)
    → Reduces (quot.type α β n) τ
    → Judge (DCC `(β, x)) τ
  | pair : Judge f (DCC (Π(f_α, β) x_α))
    → Reduces (DCC (f_α x_α)) α
    → Judge g (DCC (Π(f_α₂, `(Sort m, γ ∘ f)) x_α₂))
    → Reduces (DCC (f_α₂ x_α₂)) α
    → Reduces (pair.type α γ m) τ
    → Judge (DCC ⟦γ⟧⟨f, g⟩) τ
  | appl : Judge β (arrow α (DCC Sort n) m)
    → Reduces (App.type α β m n) τ
    → Judge (DCC App(β)) τ
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
    | .some ⟨t, h⟩ => match match_arrow t with
      | .some ⟨α, β, m, h_arr⟩ => .some ⟨t, α, β, m, h, h_arr⟩
      | _ => .none
    | _ => .none

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
  | DCC Fst(β) =>
    match with_arr (infer β) with
    | .some ⟨_τ₁, _α, DCC Sort _n, _m, ⟨ht⟩, ⟨harr⟩⟩ =>
      .some ⟨_, ⟨.fst (harr ▸ ht) (reduce_reduces rfl)⟩⟩
    | _ => .none
  | DCC Snd(β) =>
    match with_arr (infer β) with
    | .some ⟨_τ₁, _α, DCC Sort _n, _m, ⟨ht⟩, ⟨harr⟩⟩ =>
      .some ⟨_, ⟨.snd (harr ▸ ht) (reduce_reduces rfl)⟩⟩
    | _ => .none
  | DCC Σ(β) =>
    match with_arr (infer β) with
    | .some ⟨_τ₁, _α, DCC Sort _n, _m, ⟨ht⟩, ⟨harr⟩⟩ =>
      .some ⟨_, ⟨.sigma (harr ▸ ht)⟩⟩
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
        match with_arr (infer β) with
        | .some ⟨_, α₂, DCC Sort _n, _m, ⟨ht₃⟩, ⟨harr⟩⟩ =>
          if heq : (reduce (DCC (β x))) = βxm ∧ α = α₂ then
            have ⟨h₁, h₂⟩ := heq
            .some ⟨_, ⟨.coup ht₁ ht₂ (h₂ ▸ harr ▸ ht₃) (reduce_reduces h₁) (reduce_reduces rfl)⟩⟩
          else .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC Λ(β, x) =>
    match with_arr (infer β) with
    | .some ⟨_τ₁, _α, DCC Sort _n, _m, ⟨ht₁⟩, ⟨harr₁⟩⟩ =>
      match infer x with
      | .some ⟨DCC (Π(f_α, _γ) x_α), ⟨ht₂⟩⟩ =>
        if heq : (reduce (DCC (f_α x_α)) = DCC Σ(β)) then
          .some ⟨_, ⟨.curr (harr₁ ▸ ht₁) ht₂ (reduce_reduces heq) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC `(β, x) =>
    match infer x, infer β with
    | .some ⟨_α, ⟨ht₁⟩⟩, .some ⟨DCC Sort _n, ⟨ht₂⟩⟩ =>
      .some ⟨_, ⟨.quot ht₁ ht₂ (reduce_reduces rfl)⟩⟩
    | _, _ => .none
  | DCC ⟦γ⟧⟨f, g⟩ =>
    match infer f, infer g with
    | .some ⟨DCC (Π(f_α, _β) x_α), ⟨ht₁⟩⟩, .some ⟨DCC (Π(f_α₂, `(Sort _m₃, γ₂ ∘ f₂)) x_α₂), ⟨ht₂⟩⟩ =>
      if heq : (reduce (DCC (f_α x_α)) = reduce (DCC (f_α₂ x_α₂))) ∧ f₂ = f ∧ γ₂ = γ then
        have ⟨h₁, h₂, h₃⟩ := heq
        .some ⟨_, ⟨.pair ht₁ (reduce_reduces rfl) (h₂ ▸ h₃ ▸ ht₂) (reduce_reduces h₁.symm) (reduce_reduces rfl)⟩⟩
      else .none
    | _, _ => .none
  | DCC App(β) =>
    match with_arr (infer β) with
    | .some ⟨_τ₁, _α, DCC Sort _n, _m, ⟨ht⟩, ⟨harr⟩⟩ => .some ⟨_, ⟨.appl (harr ▸ ht)
      (reduce_reduces rfl)⟩⟩
    | _ => .none
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
