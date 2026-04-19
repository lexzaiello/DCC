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

namespace Expr

def arrow (α β : Expr) (m : Level) : Expr :=
  DCC (Π(m, Id(Sort m), `(α, β)) α)

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
      Λ(β, γ)))) α) -- weaken α, keep x

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
def comp.type (α γ g : Expr) (m : Level) : Expr :=
  DCC (Π(m, Id(Sort m), `(Sort m, γ ∘ g)) α)

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

end Expr
