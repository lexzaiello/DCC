import Dcc.CC.Ast
import Dcc.CC.Step2


def arrow (α β : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, `(α, β))) α)

def id.type (α : Expr) (m : Level) : Expr :=
  arrow α α m

def fst.type (α β : Expr) (m n : Level) : Expr :=
  arrow (DCC Σ(β)) α (max m n)

def snd.type (β : Expr) (m n : Level) : Expr :=
  DCC (Π(Id(Sort (max m n)),
    `(Sort (max m n),
      β ∘ Fst(β))) Σ(β))

def coup.type (β : Expr) : Expr :=
  DCC Σ(β)

/-
x : ∀ (s : Σ(β)), γ s
Λ(β, x) : ∀ (x : α) (y : β x), γ ⟦β⟧(x, y)
-/
def curr.type (α β γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m),
    `(Sort m, Π(β,
      Λ(β, (γ Σ(β)))))) α) -- weaken α, keep x

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
  DCC (Π(Id(Sort (max m n)), (β α) ∘ Snd'(Π(Id(Sort m), β), β))
    Σ(`(Π(Id(Sort m), β), α)))

def snd'.type (α β : Expr) (m n : Level) : Expr :=
  arrow (DCC Σ(`(α, β))) β (max m n)

/-
f_α : α → Sort m
f_β : (x : α) (y : f_α x) → Sort n
Π(m, f_α, f_β) : α → Sort n
-/
def Pi.type (α : Expr) (m n : Level) : Expr :=
  arrow α (DCC Sort n) m

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

inductive IsArrow : Expr → (α β : Expr) → Level → Prop
  | mk    : Reduces A (arrow α β m) → IsArrow A α β m

def IsArrow.unique (h₁ : IsArrow τ α β m) (h₂ : IsArrow τ α₂ β₂ n) : m = n ∧ α = α₂ ∧ β = β₂ := by
  induction h₁ generalizing n
  induction h₂ generalizing m
  rename_i h₁ h₂
  have h := h₂.complete
  rw [h₁.complete] at h
  unfold arrow at h
  simp_all

def IsArrow.unique' (h₁ : IsArrow τ α β m) (h₂ : IsArrow τ α β m) : h₁ = h₂ := by
  induction h₁
  cases h₂
  rename_i h₁ h₂
  cases h₁.unique' h₂
  rfl

@[inline] abbrev is_arrow (t : Expr) : Option ((α β : Expr) × (m : Level) × PLift (IsArrow t α β m)) :=
  match heq₀ : t.reduce with
  | DCC (Π(Id(Sort m), `(Sort m₂, `(α, β))) α₂) =>
    if heq : m = m₂ ∧ α = α₂ then
      have ⟨h₁, h₂⟩ := heq
      .some ⟨α, β, m, ⟨reduce_sound (by
        rw [← h₁, ← h₂] at heq₀
        exact heq₀), reduce_norm (by
        rw [← h₁, ← h₂] at heq₀
        exact heq₀)⟩⟩
    else
      .none
  | _ => .none

@[inline] abbrev match_arrow (t : Expr) : Option ((α β : Expr) × (m : Level) × PLift (t = arrow α β m)) :=
  match t with
  | DCC (Π(Id(Sort m), `(Sort m₂, `(α, β))) α₂) =>
    if heq : m = m₂ ∧ α = α₂ then
      have ⟨h₁, h₂⟩ := heq
      .some ⟨α, β, m, ⟨h₁.symm ▸ h₂.symm ▸ rfl⟩⟩
    else
      .none
  | _ => .none

def IsArrow.complete (h : IsArrow e α β m) : is_arrow e = .some ⟨α, β, m, ⟨h⟩⟩ := by
  match h with
  | ⟨h⟩ =>
    have ha := h.complete
    simp [is_arrow]
    split
    case h_1 heq' =>
      split
      case isTrue h =>
        split
        rw [heq'] at ha
        cases ha
        rfl
      case isFalse h =>
        rw [heq'] at ha
        cases ha
        exact (h ⟨rfl, rfl⟩).elim
    case h_2 h => exact (h _ _ _ _ _ ha).elim

instance : Decidable (∃ α β m, IsArrow e α β m) :=
  if h : (is_arrow e).isSome then
    .isTrue ⟨_, _, _, ((is_arrow e).get h).snd.snd.snd.down⟩
  else
    .isFalse (fun ⟨_, _, _, h⟩ => by
      have h := h.complete
      simp_all)

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
    → Reduces (curr.type α β γ m) τ
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
  | pi   : Judge f_α (arrow α (DCC Sort n) m)
    → Judge f_β (DCC Π(Id(α), Π(f_α, `(α, `(Sort n, Sort o)))))
    → Reduces (Pi.type α m n) τ
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
    | .some ⟨_τ₁, α, DCC Sort n, _m₂, ⟨ht₁⟩, ⟨harr⟩⟩, .some ⟨DCC Π(Id(α₂), Π(f_α₂, `(α₃, `(Sort n₃, Sort _o)))), ⟨ht₂⟩⟩ =>
      if heq : α₂ = α ∧ f_α₂ = f_α ∧ α₃ = α ∧ n₃ = n then
        have ⟨h₁, h₂, h₃, h₄⟩ := heq
        .some ⟨_, ⟨.pi (harr ▸ ht₁) (h₁ ▸ h₂ ▸ h₃ ▸ h₄ ▸ ht₂) (reduce_reduces rfl)⟩⟩
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
