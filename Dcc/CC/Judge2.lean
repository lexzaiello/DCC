import Dcc.CC.Ast
import Dcc.CC.Step2

/-
Experimenting with simpler app:

| app   : Judge f t_f
    → Reduces t_f (DCC (Π(f_α, f_β) x_α))
    → Judge x t_x
    → Reduces (DCC (fα x_α)) α
    → Reduces t_x α
    → Judge (DCC (f x)) (DCC (f_β x_α x))

need types for:

- ~sigma~
- ~pi~
- ~snd'~
- ~comp~
- ~App~
- ~pair~
- ~snd~
- ~quot~
- ~curry~
- ~id~
- ~fst~
- ~couples~

don't need:
- snd'
- flip
- quotation (see if necessary in types)
- can make composition pointed again??

f ∘ g

g : α → β
f : ∀ (x : β), γ x
-/


def arrow (α β : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, `(α, β))) α)

def id.type (α : Expr) (m : Level) : Expr :=
  arrow α (arrow α α m) m

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

inductive Reduces : Expr → Expr → Type
  | mk : RedAffReflTrans A B → IsNormAff B → Reduces A B
deriving Repr

theorem Reduces.complete : Reduces A B → reduce A = B :=
  fun ⟨ha, hb⟩ => ha.complete hb

def reduce_reduces (h : reduce A = B) : Reduces A B := ⟨reduce_sound h, reduce_norm h⟩

def reduce_reduces' : Reduces A A.reduce := reduce_reduces rfl

inductive IsArrow : Expr → (α β : Expr) → Level → Type
  | mk    : Reduces A (arrow α β m) → IsArrow A α β m
deriving Repr

def is_arrow (t : Expr) : Option ((α β : Expr) × (m : Level) × IsArrow t α β m) :=
  match t.reduce with
  | DCC (Π(Id(Sort m), `(α, β)) _a) =>
    if heq : t.reduce = arrow α β m then
      .some ⟨α, β, m, ⟨reduce_sound heq, heq ▸ reduce_norm rfl⟩⟩
    else
      .none
  | _ => .none

inductive Judge : Expr → Expr → Type where
  | id   : Judge α τ
    → Reduces τ (DCC Sort m)
    → Judge (DCC Id(α)) (id.type α m)
  | comp : Judge g τ₁
    → IsArrow τ₁ α β m
    → Judge f τ₂
    → Reduces τ₂ (DCC (Π(Id(Sort n), γ) β))
    → Judge (DCC f ∘ g) (comp.type α β γ g m)
  | fst  : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge (DCC Fst(β)) (fst.type α β m n)
  | snd   : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge (DCC Snd(β)) (snd.type β m n)
  | sigma : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge (DCC Σ(β)) (Sigma.type m n)
  | snd' : Judge α τ₁
    → Reduces τ₁ (DCC Sort m)
    → Judge β τ₂
    → Reduces τ₂ (DCC Sort n)
    → Judge (DCC Snd'(α, β)) (snd'.type α β m n)
  | coup : Judge x τ₁
    → Reduces τ₁ α
    → Judge y τ₂
    → Judge β τ₃
    → IsArrow τ₃ α (DCC Sort n) m
    → Reduces (DCC (β x)) τ₂'
    → Reduces τ₂ τ₂'
    → Judge (DCC ⟦β⟧(x, y)) (coup.type β)
  | curr : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge x τ₂
    → Reduces τ₂ (DCC (Π(f_α, γ) x_α))
    → Reduces (DCC (f_α x_α)) (DCC Σ(β))
    → Judge (DCC Λ(β, x)) (curr.type α β γ m)
  | quot : Judge x τ₁
    → Reduces τ₁ α
    → Judge β τ₂
    → Reduces τ₂ (DCC Sort n)
    → Judge (DCC `(β, x)) (quot.type α β n)
  | pair : Judge f τ₁
    → Reduces τ₁ (DCC (Π(f_α, β) x_α))
    → Reduces (DCC (f_α x_α)) α
    → Judge g τ₂
    → Reduces τ₂ (DCC (Π(f_α₂, `(Sort m, γ ∘ f)) x_α₂))
    → Reduces (DCC (f_α₂ x_α₂)) α
    → Judge (DCC ⟦γ⟧⟨f, g⟩) (pair.type α γ m)
  | appl : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge (DCC App(β)) (App.type α β m n)
  | pi   : Judge f_α τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge f_β τ₂
    → Reduces τ₂ (DCC Π(Id(α), Π(f_α, `(α, `(Sort n, Sort o)))))
    → Judge (DCC Π(f_α, f_β)) (Pi.type α m n)
  | sort : Judge (DCC Sort m) (DCC Sort m.succ)
  | app  : Judge f τ₁
    → Reduces τ₁ (DCC (Π(f_α, f_β) x_α))
    → Reduces (DCC (f_α x_α)) α
    → Judge x τ₂
    → Reduces τ₂ α
    → Judge (DCC (f x)) (DCC (f_β x_α x))

abbrev with_red (h : Option ((t : Expr) × Judge e t)) :
  Option ((τ₁ τ₂ : Expr) × Judge e τ₁ × Reduces τ₁ τ₂) := do
  match ← h with
  | ⟨t, h⟩ => .some ⟨t, t.reduce, h, reduce_reduces rfl⟩

abbrev with_arr (h : Option ((t : Expr) × Judge e t)) :
  Option ((τ α β : Expr) × (m : Level) × Judge e τ × IsArrow τ α β m) := do
    match ← h with
    | ⟨t, h⟩ => match ← is_arrow t with
      | ⟨α, β, m, h_arr⟩ => .some ⟨t, α, β, m, h, h_arr⟩

def infer (e : Expr) : Option ((t : Expr) × Judge e t) := do
  match e with
  | DCC Sort m => .some ⟨_, .sort⟩
  | DCC (Id(α)) => do
    match ← with_red (infer α) with
    | ⟨_, DCC Sort m, ht, h_red⟩ => .some ⟨_, .id ht h_red⟩
    | _ => .none
  | DCC (f ∘ g) => do
    match ← with_arr (infer g), ← with_red (infer f) with
    | ⟨_, α, β, m, ht₁, harr₁⟩, ⟨_, (DCC (Π(Id(Sort n₂), γ) β₂)), ht₂, hred⟩ =>
      if heq : β₂ = β then
        .some ⟨_, .comp ht₁ harr₁ ht₂ (heq ▸ hred)⟩
      else .none
    | _, _ => .none
  | DCC Fst(β) => do
    match ← with_arr (infer β) with
    | ⟨τ₁, α, DCC Sort n, m, ht, harr⟩ =>
      .some ⟨_, .fst ht harr⟩
    | _ => .none
  | DCC Snd(β) => do
    match ← with_arr (infer β) with
    | ⟨τ₁, α, DCC Sort n, m, ht, harr⟩ =>
      .some ⟨_, .snd ht harr⟩
    | _ => .none
  | DCC Σ(β) => do
    match ← with_arr (infer β) with
    | ⟨τ₁, α, DCC Sort n, m, ht, harr⟩ =>
      .some ⟨_, .sigma ht harr⟩
    | _ => .none
  | DCC Snd'(α, β) => do
    match ← with_red (infer α), ← with_red (infer β) with
    | ⟨τ₁, DCC Sort m, ht₁, hr₁⟩, ⟨τ₂, DCC Sort n, ht₂, hr₂⟩ =>
      .some ⟨_, .snd' ht₁ hr₁ ht₂ hr₂⟩
    | _, _ => .none
  | DCC ⟦β⟧(x, y) => do
    match ← with_red (infer x), ← with_red (infer y), ← with_arr (infer β) with
    | ⟨τ₁, α, ht₁, hr₁⟩, ⟨τ₂, βxm, ht₂, hr₂⟩, ⟨_, α₂, DCC Sort n, m, ht₃, harr⟩ =>
      if heq : (reduce (DCC (β x))) = βxm ∧ α = α₂ then
        have ⟨h₁, h₂⟩ := heq
        .some ⟨_, .coup ht₁ hr₁ ht₂ ht₃ (h₂ ▸ harr) (reduce_reduces h₁) hr₂⟩
      else .none
    | _, _, _ => .none
  | DCC Λ(β, x) => do
    match ← with_arr (infer β), ← with_red (infer x) with
    | ⟨τ₁, α, DCC Sort n, m, ht₁, harr₁⟩, ⟨τ₂, DCC (Π(f_α, γ) x_α), ht₂, hr₂⟩ =>
      if heq : (reduce (DCC (f_α x_α)) = DCC Σ(β)) then
        .some ⟨_, .curr ht₁ harr₁ ht₂ hr₂ (reduce_reduces heq)⟩
      else .none
    | _, _ => .none
  | DCC `(β, x) => do
    match ← with_red (infer x), ← with_red (infer β) with
    | ⟨τ₁, α, ht₁, hr₁⟩, ⟨τ₂, DCC Sort n, ht₂, hr₂⟩ =>
      .some ⟨_, .quot ht₁ hr₁ ht₂ hr₂⟩
    | _, _ => .none
  | DCC ⟦γ⟧⟨f, g⟩ => do
    match ← with_red (infer f), ← with_red (infer g) with
    | ⟨τ₁, DCC (Π(f_α, β) x_α), ht₁, hr₁⟩, ⟨τ₂, DCC (Π(f_α₂, `(Sort m₃, γ₂ ∘ f₂)) x_α₂), ht₂, hr₂⟩ =>
      if heq : (reduce (DCC (f_α x_α)) = reduce (DCC (f_α₂ x_α₂))) ∧ f₂ = f ∧ γ₂ = γ then
        have ⟨h₁, h₂, h₃⟩ := heq
        .some ⟨_, .pair ht₁ hr₁ (reduce_reduces rfl) ht₂ (by
          rw [h₂, h₃] at hr₂
          exact hr₂) (reduce_reduces h₁.symm)⟩
      else .none
    | _, _ => .none
  | DCC App(β) =>
    match ← with_arr (infer β) with
    | ⟨τ₁, α, DCC Sort n, m, ht, harr⟩ => .some ⟨_, .appl ht harr⟩
    | _ => .none
  | DCC Π(f_α, f_β) =>
    match ← with_arr (infer f_α), ← with_red (infer f_β) with
    | ⟨τ₁, α, DCC Sort n, m₂, ht₁, harr⟩, ⟨τ₂, DCC Π(Id(α₂), Π(f_α₂, `(α₃, `(Sort n₃, Sort o)))), ht₂, hr₂⟩ =>
      if heq : α₂ = α ∧ f_α₂ = f_α ∧ α₃ = α ∧ n₃ = n then
        have ⟨h₁, h₂, h₃, h₄⟩ := heq
        .some ⟨_, .pi ht₁ harr ht₂ (by
          rw [h₁, h₂, h₃, h₄] at hr₂
          exact hr₂)⟩
      else .none
    | _, _ => .none
  | DCC (f x) =>
    match ← with_red (infer f), ← with_red (infer x) with
    | ⟨τ₁, DCC (Π(f_α, f_β) x_α), ht₁, hr₁⟩, ⟨τ₂, τ₂', ht₂, hr₂⟩ =>
      if heq : (reduce (DCC (f_α x_α))) = τ₂' then
        .some ⟨_, .app ht₁ hr₁ (reduce_reduces rfl) ht₂ (heq ▸ hr₂)⟩
      else .none
    | _, _ => .none

end Expr
