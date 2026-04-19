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
  DCC (Π(m, Id(Sort m), `(Sort m, `(α, β))) α)

def id.type (α : Expr) (m : Level) : Expr :=
  arrow α (arrow α α m) m

def fst.type (α β : Expr) (m n : Level) : Expr :=
  arrow (DCC Σ(β)) α (max m n)

def snd.type (β : Expr) (m n : Level) : Expr :=
  DCC (Π(max m n,
    Id(Sort (max m n)),
    `(Sort (max m n),
      β ∘ Fst(β))) Σ(β))

def coup.type (β : Expr) : Expr :=
  DCC Σ(β)

/-
x : ∀ (s : Σ(β)), γ s
Λ(β, x) : ∀ (x : α) (y : β x), γ ⟦β⟧(x, y)
-/
def curr.type (α β γ : Expr) (m n : Level) : Expr :=
  DCC (Π(m, Id(Sort m),
    `(Sort m, Π(n, β,
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
  DCC (Π(m, Id(Sort m), `(Sort m, (γ β) ∘ g)) α)

/-
f : ∀ (x : α), β x
App(β) : ∀ (s : Σ(`(Π(m, Id(Sort m), β), α))), (β α) ∘ Snd'(Π(m, Id(Sort m), β), β)
-/
def App.type (α β : Expr) (m n : Level) : Expr :=
  DCC (Π(max m n, Id(Sort (max m n)), (β α) ∘ Snd'(Π(m, Id(Sort m), β), β))
    Σ(`(Π(m, Id(Sort m), β), α)))

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
  | DCC (Π(m, Id(_m), `(α, β)) _a) =>
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
    → Reduces τ₂ (DCC (Π(n, Id(Sort n), γ) β))
    → Judge (DCC f ∘ g) (comp.type α β γ g m)
  | fst  : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge (DCC Fst(β)) (fst.type α β m n)
  | snd  : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge (DCC Snd(β)) (snd.type β m n)
  | snd' : Judge α τ₁
    → Reduces τ₁ (DCC Sort m)
    → Judge β τ₂
    → Reduces τ₂ (DCC Sort n)
    → Judge (DCC Snd'(α, β)) (snd'.type α β m n)
  | coup : Judge x τ₁
    → Reduces τ₁ α
    → Judge y τ₂
    → IsArrow β α (DCC Sort n) m
    → Reduces (DCC (β x)) τ₂'
    → Reduces τ₂ τ₂'
    → Judge (DCC ⟦β⟧(x, y)) (coup.type β)
  | curr : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge x τ₂
    → Reduces τ₂ (DCC (Π(max m n, f_α, γ) x_α))
    → Reduces (DCC (f_α x_α)) (DCC Σ(β))
    → Judge (DCC Λ(β, x)) (curr.type α β γ m n)
  | quot : Judge x τ₁
    → Reduces τ₁ α
    → Judge β τ₂
    → Reduces τ₂ (DCC Sort n)
    → Judge (DCC `(β, x)) (quot.type α β n)
  | pair : Judge f τ₁
    → Reduces τ₁ (DCC (Π(m, f_α, β) x_α))
    → Reduces (DCC (f_α x_α)) α
    → Judge g (DCC (Π(m, f_α₂, `(Sort m, γ ∘ f)) x_α₂))
    → Reduces (DCC (f_α₂ x_α₂)) α
    → Judge (DCC ⟦γ⟧⟨f, g⟩) (pair.type α γ m)
  | appl : Judge β τ₁
    → IsArrow β α (DCC Sort n) m
    → Judge (DCC App(β)) (App.type α β m n)
  | pi   : Judge f_α τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge f_β (DCC Π(m, Id(α), Π(n, f_α, `(α, `(Sort n, Sort o)))))
    → Judge (DCC Π(m, f_α, f_β)) (Pi.type α m n)
  | sort : Judge (DCC Sort m) (DCC Sort m.succ)
  | app  : Judge f τ₁
    → Reduces τ₁ (DCC (Π(m, f_α, f_β) x_α))
    → Reduces (DCC (f_α x_α)) α
    → Judge x τ₂
    → Reduces τ₂ α
    → Judge (DCC (f x)) (DCC (f_β x_α x))

end Expr
